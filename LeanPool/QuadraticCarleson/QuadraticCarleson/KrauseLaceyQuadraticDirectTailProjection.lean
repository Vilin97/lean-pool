/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectProjectionBridge
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectProjectedTail
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectScaleTails
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticTailPerturbation

/-!
# Projection perturbations of direct quadratic tails

The direct scale output is split into its smooth annular projection and the
explicit quadratic projection remainder. This module only performs that
finite pointwise bookkeeping; estimates for the remainder itself remain in
the projection-remainder module.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectTailProjection

open KrauseLaceyQuadraticAnnularTail
open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectProjectedTail
open KrauseLaceyQuadraticDirectProjectionBridge
open KrauseLaceyQuadraticDirectScaleEnergy
open KrauseLaceyQuadraticDirectScaleTails
open KrauseLaceyQuadraticProjectionRemainder
open KrauseLaceyQuadraticTailPerturbation
open KrauseLaceyQuadraticSmoothProjection


noncomputable
section

/-- The explicit projection-remainder output associated with every member of
one direct residue family. -/
def directResidueRemainderOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) : ℕ → ℝ → ℂ :=
  fun n ↦ quadraticProjectionRemainderOutput (residueScale r n)
    (directScaleInput S A scale f (residueScale r n) s)

/-- The finite scalar error majorant for replacing a direct residue family by
its annularly projected version. -/
def directResidueRemainderMajorant
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ‖directResidueRemainderOutput S A scale f r s n x‖ₑ

/-- The extended-nonnegative direct remainder majorant is exactly the
`ofReal` encoding of the generic real-valued projection-error majorant. -/
theorem directResidueRemainderMajorant_eq_ofReal
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) (x : ℝ) :
    directResidueRemainderMajorant S A scale f r s N x =
      ENNReal.ofReal
        (finiteProjectionErrorMajorant N
          (directResidueRemainderOutput S A scale f r s) x) := by
  simpa only [directResidueRemainderMajorant,
    finiteProjectionErrorMajorant, ofReal_norm] using
    (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.range N)
      (f := fun n ↦
        ‖directResidueRemainderOutput S A scale f r s n x‖)
      (fun _ _ ↦ norm_nonneg _)).symm

/-- The square integral of the concrete direct residue remainder majorant is
exactly the square of the corresponding real `L²` majorant norm. -/
theorem lintegral_directResidueRemainderMajorant_sq_eq
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    let input : ℕ → ℝ → ℂ := fun n ↦
      directScaleInput S A scale f (residueScale r n) s
    let u : ℕ → ℝ → ℂ := fun n ↦
      quadraticProjectionRemainderOutput (residueScale r n) (input n)
    let hu : ∀ n, MemLp (u n) 2 volume := fun n ↦
      memLp_two_quadraticProjectionRemainderOutput
        (by unfold residueScale; omega)
        (integrable_directScaleInput S A scale f (residueScale r n) s)
    (∫⁻ x, directResidueRemainderMajorant S A scale f r s N x ^ 2) =
      ENNReal.ofReal
        (‖(memLp_two_finiteProjectionErrorMajorant hu).toLp
          (finiteProjectionErrorMajorant N u)‖ ^ 2) := by
  dsimp only
  calc
    (∫⁻ x, directResidueRemainderMajorant S A scale f r s N x ^ 2) =
        ∫⁻ x, ENNReal.ofReal
          (finiteProjectionErrorMajorant N (fun n ↦
            quadraticProjectionRemainderOutput (residueScale r n)
              (directScaleInput S A scale f (residueScale r n) s)) x) ^ 2 := by
      apply lintegral_congr
      intro x
      rw [directResidueRemainderMajorant_eq_ofReal]
      rfl
    _ = _ := lintegral_ofReal_finiteProjectionErrorMajorant_sq_eq
      (N := N)
      (u := fun n ↦ quadraticProjectionRemainderOutput (residueScale r n)
        (directScaleInput S A scale f (residueScale r n) s))
      (fun n ↦ memLp_two_quadraticProjectionRemainderOutput
        (by unfold residueScale; omega)
        (integrable_directScaleInput S A scale f (residueScale r n) s))

theorem residueScale_nonneg (r : Fin 7) (n : ℕ) :
    0 ≤ residueScale r n := by
  unfold residueScale
  omega

/-- The inverse cubic scale weights are summable uniformly over every finite
initial segment of one of the seven residue classes. -/
theorem sum_inv_cube_residueScale_le_two (r : Fin 7) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        (((2 : ℝ) ^ residueScale r n)⁻¹) ^ 3) ≤ 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [show (((2 : ℝ) ^ residueScale r n)⁻¹) ^ 3 =
          (2 : ℝ) ^ (-3 * residueScale r n) by
            calc
              (((2 : ℝ) ^ residueScale r n)⁻¹) ^ (3 : ℕ) =
                  ((2 : ℝ) ^ (-residueScale r n)) ^ (3 : ℕ) := by
                    rw [zpow_neg]
              _ = ((2 : ℝ) ^ (-residueScale r n)) ^ (3 : ℤ) := rfl
              _ = (2 : ℝ) ^ ((-residueScale r n) * 3) :=
                    (zpow_mul (2 : ℝ) (-residueScale r n) 3).symm
              _ = (2 : ℝ) ^ (-3 * residueScale r n) := by
                    congr 1
                    ring]
      rw [show (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ (-(n : ℤ)) by
        calc
          (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
            rw [one_div_pow, one_div]
          _ = ((2 : ℝ) ^ (n : ℤ))⁻¹ := by rw [zpow_natCast]
          _ = (2 : ℝ) ^ (-(n : ℤ)) :=
            (zpow_neg (2 : ℝ) (n : ℤ)).symm]
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      unfold residueScale
      have hr : 0 ≤ (r : ℕ) := Nat.zero_le _
      omega
    _ ≤ 2 := sum_geometric_two_le N

/-- After inserting the centered unit-mass estimate, the squared remainder
coefficient still has a geometric sum independent of the number of scales. -/
theorem sum_projectionRemainder_residueWeight_le
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        (((2 : ℝ) ^ residueScale r n)⁻¹) ^ 4 *
          (2 : ℝ) ^ (residueScale r n + 2 - s)) ≤
      8 * (2 : ℝ) ^ (-s) := by
  have hweight (k : ℤ) :
      (((2 : ℝ) ^ k)⁻¹) ^ 4 * (2 : ℝ) ^ (k + 2 - s) =
        (2 : ℝ) ^ (2 - s) * (((2 : ℝ) ^ k)⁻¹) ^ 3 := by
    rw [show k + 2 - s = k + (2 - s) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hk : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero k (by norm_num)
    field_simp
  simp_rw [hweight]
  rw [← Finset.mul_sum]
  calc
    (2 : ℝ) ^ (2 - s) *
        (∑ n ∈ Finset.range N,
          (((2 : ℝ) ^ residueScale r n)⁻¹) ^ 3) ≤
      (2 : ℝ) ^ (2 - s) * 2 :=
        mul_le_mul_of_nonneg_left
          (sum_inv_cube_residueScale_le_two r N) (by positivity)
    _ = 8 * (2 : ℝ) ^ (-s) := by
      rw [show 2 - s = 2 + (-s) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring

/-- The abstract centered-mass remainder estimate specialized to the genuine
direct inputs along one residue class. Actual scales use their inherited
unit-window mass bound; absent scales contribute exactly zero. -/
theorem norm_finiteProjectionErrorMajorant_directResidue_le_centeredSum
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (r : Fin 7) (N : ℕ) :
    let input : ℕ → ℝ → ℂ := fun n ↦
      directScaleInput S A scale f (residueScale r n) s
    let bound : ℕ → ℝ := fun n ↦
      if residueScale r n ∈ A.image scale then
        3 * M * (2 : ℝ) ^ (residueScale r n + 2 - s)
      else 0
    let hu : ∀ n, MemLp
        (quadraticProjectionRemainderOutput (residueScale r n) (input n))
        2 volume := fun n ↦
      memLp_two_quadraticProjectionRemainderOutput
        (residueScale_nonneg r n)
        (integrable_directScaleInput S A scale f (residueScale r n) s)
    ‖(memLp_two_finiteProjectionErrorMajorant hu).toLp
        (finiteProjectionErrorMajorant N fun n ↦
          quadraticProjectionRemainderOutput (residueScale r n) (input n))‖ ≤
      ∑ n ∈ Finset.range N,
        2 * (Real.pi * projectionRemainderConstant *
            ((2 : ℝ) ^ residueScale r n)⁻¹ ^ 2) *
          Real.sqrt (bound n) * Real.sqrt (∫ x, ‖input n x‖) := by
  classical
  dsimp only
  let input : ℕ → ℝ → ℂ := fun n ↦
    directScaleInput S A scale f (residueScale r n) s
  let bound : ℕ → ℝ := fun n ↦
    if residueScale r n ∈ A.image scale then
      3 * M * (2 : ℝ) ^ (residueScale r n + 2 - s)
    else 0
  have hbound (n : ℕ) : 0 ≤ bound n := by
    dsimp only [bound]
    split_ifs
    · positivity
    · exact le_rfl
  have hlocal (n : ℕ) (z : ℝ) :
      centeredUnitMass (input n) z ≤ bound n := by
    dsimp only [input, bound]
    by_cases hk : residueScale r n ∈ A.image scale
    · rw [ite_eq_left hk]
      obtain ⟨I, hIA, hIk⟩ := Finset.mem_image.mp hk
      have hgapk : 0 ≤ residueScale r n + 2 - s := by
        simpa only [hIk] using
          hgap (residueScale r n) hk I
            (Finset.mem_filter.mpr ⟨hIA, hIk⟩)
      exact centeredUnitMass_directScaleInput_le
        hA hlam scale hscale f hs hgapk hM hmass z
    · rw [ite_eq_right hk,
        directScaleInput_eq_zero_of_not_mem_image S A scale f
          (residueScale r n) s hk]
      simp [centeredUnitMass]
  simpa only [input, bound] using
    norm_finiteProjectionErrorMajorantL2_le_of_centeredUnitMass
      (N := N) (k := residueScale r) (fun n ↦ residueScale_nonneg r n)
      (f := input)
      (fun n ↦ integrable_directScaleInput S A scale f (residueScale r n) s)
      hbound hlocal

/-- Cardinality-free `L²` bound for the real-valued projection-remainder
majorant along one residue class. This is the finite Cauchy--Schwarz step
combining the centered mass, geometric scale weight, and total input mass. -/
theorem norm_finiteProjectionErrorMajorant_directResidue_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (r : Fin 7) (N : ℕ) :
    let input : ℕ → ℝ → ℂ := fun n ↦
      directScaleInput S A scale f (residueScale r n) s
    let hu : ∀ n, MemLp
        (quadraticProjectionRemainderOutput (residueScale r n) (input n))
        2 volume := fun n ↦
      memLp_two_quadraticProjectionRemainderOutput
        (residueScale_nonneg r n)
        (integrable_directScaleInput S A scale f (residueScale r n) s)
    ‖(memLp_two_finiteProjectionErrorMajorant hu).toLp
        (finiteProjectionErrorMajorant N fun n ↦
          quadraticProjectionRemainderOutput (residueScale r n) (input n))‖ ≤
      2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
        Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖) := by
  classical
  dsimp only
  let input : ℕ → ℝ → ℂ := fun n ↦
    directScaleInput S A scale f (residueScale r n) s
  let bound : ℕ → ℝ := fun n ↦
    if residueScale r n ∈ A.image scale then
      3 * M * (2 : ℝ) ^ (residueScale r n + 2 - s)
    else 0
  let weight : ℕ → ℝ := fun n ↦
    (((2 : ℝ) ^ residueScale r n)⁻¹) ^ 4 *
      (2 : ℝ) ^ (residueScale r n + 2 - s)
  let mass : ℕ → ℝ := fun n ↦ ∫ x, ‖input n x‖
  let C : ℝ :=
    2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M)
  have hspecial :
      ‖(memLp_two_finiteProjectionErrorMajorant fun n ↦
          memLp_two_quadraticProjectionRemainderOutput
            (residueScale_nonneg r n)
            (integrable_directScaleInput S A scale f (residueScale r n) s)).toLp
          (finiteProjectionErrorMajorant N fun n ↦
            quadraticProjectionRemainderOutput (residueScale r n) (input n))‖ ≤
        ∑ n ∈ Finset.range N,
          2 * (Real.pi * projectionRemainderConstant *
              ((2 : ℝ) ^ residueScale r n)⁻¹ ^ 2) *
            Real.sqrt (bound n) * Real.sqrt (mass n) := by
    simpa only [input, bound, mass] using
      norm_finiteProjectionErrorMajorant_directResidue_le_centeredSum
        hA hlam scale hscale f hs hM hmass hgap r N
  have hweight0 (n : ℕ) : 0 ≤ weight n := by
    dsimp only [weight]
    positivity
  have hmass0 (n : ℕ) : 0 ≤ mass n := by
    dsimp only [mass]
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg))
      (Real.sqrt_nonneg _)
  have hterm (n : ℕ) :
      2 * (Real.pi * projectionRemainderConstant *
          ((2 : ℝ) ^ residueScale r n)⁻¹ ^ 2) *
        Real.sqrt (bound n) * Real.sqrt (mass n) =
      C * (Real.sqrt (weight n) * Real.sqrt (mass n)) := by
    by_cases hk : residueScale r n ∈ A.image scale
    · have hsqrtBound :
          Real.sqrt (bound n) = Real.sqrt (3 * M) *
              Real.sqrt ((2 : ℝ) ^ (residueScale r n + 2 - s)) := by
        dsimp only [bound]
        rw [ite_eq_left hk, Real.sqrt_mul (mul_nonneg (by norm_num) hM)]
      have hsqrtWeight :
          Real.sqrt (weight n) =
            ((2 : ℝ) ^ residueScale r n)⁻¹ ^ 2 *
              Real.sqrt ((2 : ℝ) ^ (residueScale r n + 2 - s)) := by
        dsimp only [weight]
        rw [Real.sqrt_mul (by positivity)]
        rw [show (((2 : ℝ) ^ residueScale r n)⁻¹) ^ 4 =
            ((((2 : ℝ) ^ residueScale r n)⁻¹) ^ 2) *
              ((((2 : ℝ) ^ residueScale r n)⁻¹) ^ 2) by ring,
          Real.sqrt_mul_self (sq_nonneg _)]
      rw [hsqrtBound, hsqrtWeight]
      dsimp only [C]
      ring
    · have hinput : input n = 0 := by
        dsimp only [input]
        exact directScaleInput_eq_zero_of_not_mem_image S A scale f
          (residueScale r n) s hk
      have hmassZero : mass n = 0 := by
        dsimp only [mass]
        rw [hinput]
        simp
      rw [hmassZero]
      simp
  have hCS :
      (∑ n ∈ Finset.range N,
          Real.sqrt (weight n) * Real.sqrt (mass n)) ≤
        Real.sqrt (∑ n ∈ Finset.range N, weight n) *
          Real.sqrt (∑ n ∈ Finset.range N, mass n) :=
    Real.sum_sqrt_mul_sqrt_le (Finset.range N) hweight0 hmass0
  have hweightSum :
      (∑ n ∈ Finset.range N, weight n) ≤
        8 * (2 : ℝ) ^ (-s) := by
    simpa only [weight] using sum_projectionRemainder_residueWeight_le r s N
  have hmassSum :
      (∑ n ∈ Finset.range N, mass n) ≤
        ∫ x in I₀.carrier, ‖f x‖ := by
    simpa only [mass, input] using
      sum_range_integral_norm_directScaleInput_residue_le_root
        hA hlam scale hscale f hs I₀ hsub r N
  have hweightSqrt := Real.sqrt_le_sqrt hweightSum
  have hmassSqrt := Real.sqrt_le_sqrt hmassSum
  calc
    ‖(memLp_two_finiteProjectionErrorMajorant fun n ↦
        memLp_two_quadraticProjectionRemainderOutput
          (residueScale_nonneg r n)
          (integrable_directScaleInput S A scale f (residueScale r n) s)).toLp
        (finiteProjectionErrorMajorant N fun n ↦
          quadraticProjectionRemainderOutput (residueScale r n) (input n))‖ ≤
        ∑ n ∈ Finset.range N,
          2 * (Real.pi * projectionRemainderConstant *
              ((2 : ℝ) ^ residueScale r n)⁻¹ ^ 2) *
            Real.sqrt (bound n) * Real.sqrt (mass n) := hspecial
    _ = C * (∑ n ∈ Finset.range N,
        Real.sqrt (weight n) * Real.sqrt (mass n)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm n
    _ ≤ C * (Real.sqrt (∑ n ∈ Finset.range N, weight n) *
          Real.sqrt (∑ n ∈ Finset.range N, mass n)) :=
      mul_le_mul_of_nonneg_left hCS hC
    _ ≤ C * (Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul hweightSqrt hmassSqrt
        (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
        Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖) := by
      dsimp only [C]
      ring

/-- Cardinality-free square-integral estimate for the actual nonnegative
direct residue remainder majorant. -/
theorem lintegral_directResidueRemainderMajorant_sq_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (r : Fin 7) (N : ℕ) :
    (∫⁻ x, directResidueRemainderMajorant S A scale f r s N x ^ 2) ≤
      ENNReal.ofReal
        ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
          Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
            Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2) := by
  rw [lintegral_directResidueRemainderMajorant_sq_eq]
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (norm_nonneg _) (by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg))
          (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))).mpr
  simpa only [directResidueRemainderOutput] using
    norm_finiteProjectionErrorMajorant_directResidue_le_root
      hA hlam scale hscale f hs hM hmass I₀ hsub hgap r N

/-- At every nonnegative residue scale, the literal direct output is almost
everywhere its annular projection plus the explicit remainder convolution. -/
theorem directResidueOutput_ae_eq_projected_add_remainder
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (n : ℕ) :
    directResidueOutput S A scale (f : ℝ → ℂ) r s n =ᵐ[volume]
      fun x ↦ projectedOffsetResidueOutput S A scale f r s n x +
        directResidueRemainderOutput S A scale f r s n x := by
  let k : ℤ := residueScale r n
  have hk : 0 ≤ k := by
    dsimp [k]
    exact residueScale_nonneg r n
  have hLp := offsetOutputScaleLp_sub_annularProjectionL2_eq_remainderOutputL2
    S A scale f hk s
  have hsub :
      (fun x ↦ offsetOutputScaleLp S A scale f k s x -
        annularProjectionL2 k (offsetOutputScaleLp S A scale f k s) x) =ᵐ[volume]
        quadraticProjectionRemainderOutput k (directScaleInput S A scale f k s) := by
    let hrem : MemLp
        (quadraticProjectionRemainderOutput k (directScaleInput S A scale f k s))
        2 volume := memLp_two_quadraticProjectionRemainderOutput hk
          (integrable_directScaleInput S A scale f k s)
    filter_upwards [Lp.coeFn_sub
      (offsetOutputScaleLp S A scale f k s)
      (annularProjectionL2 k (offsetOutputScaleLp S A scale f k s)),
      hrem.coeFn_toLp] with x hx hremx
    rw [← hLp] at hremx
    exact hx.symm.trans hremx
  filter_upwards [
    (offsetOutputScaleLp_ae_eq_directScaleOutput S A scale f k s).symm,
    hsub] with x hdirect hsubx
  have hadd : offsetOutputScaleLp S A scale f k s x =
      annularProjectionL2 k (offsetOutputScaleLp S A scale f k s) x +
        quadraticProjectionRemainderOutput k (directScaleInput S A scale f k s) x :=
    sub_eq_iff_eq_add'.mp hsubx
  simpa only [directResidueOutput, projectedOffsetResidueOutput,
    annularResidueRepresentative, annularResiduePiece, offsetScaleFamily,
    directResidueRemainderOutput, k] using hdirect.trans hadd

/-- Replacing every direct residue output by its projected output costs at
most the finite scalar sum of the corresponding remainder outputs. -/
theorem finitePieceTailMax_directResidueOutput_ae_le_projected_add_remainder
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (r : Fin 7) (s : ℤ) (N : ℕ) :
    ∀ᵐ x : ℝ ∂volume,
      finitePieceTailMax N (directResidueOutput S A scale (f : ℝ → ℂ) r s) x ≤
        finitePieceTailMax N (projectedOffsetResidueOutput S A scale f r s) x +
          directResidueRemainderMajorant S A scale f r s N x := by
  have hall : ∀ᵐ x : ℝ ∂volume,
      ∀ n ∈ Finset.range N,
        directResidueOutput S A scale (f : ℝ → ℂ) r s n x =
          projectedOffsetResidueOutput S A scale f r s n x +
            directResidueRemainderOutput S A scale f r s n x := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact directResidueOutput_ae_eq_projected_add_remainder S A scale f r s n
  filter_upwards [hall] with x hx
  have hmajorant : finitePieceErrorMajorant N
      (directResidueOutput S A scale (f : ℝ → ℂ) r s)
      (projectedOffsetResidueOutput S A scale f r s) x =
      directResidueRemainderMajorant S A scale f r s N x := by
    unfold finitePieceErrorMajorant directResidueRemainderMajorant
    apply Finset.sum_congr rfl
    intro n hn
    rw [hx n hn]
    ring_nf
  rw [← hmajorant]
  exact finitePieceTailMax_le_finitePieceTailMax_add_errorMajorant
    N (directResidueOutput S A scale (f : ℝ → ℂ) r s)
      (projectedOffsetResidueOutput S A scale f r s) x

/-- Complete finite-tail `L²` estimate for one direct residue class, obtained
by combining the projected maximal-tail estimate with the cardinality-free
projection-remainder bound. -/
theorem finitePieceTailMax_directResidueOutput_sq_lintegral_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (r : Fin 7) (N : ℕ) :
    let B : ℝ≥0∞ :=
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖)
    let C : ℝ≥0∞ := ENNReal.ofReal
      ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
        Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)
    (∫⁻ x, finitePieceTailMax N
      (directResidueOutput S A scale (f : ℝ → ℂ) r s) x ^ 2) ≤
      4 * (B + C) := by
  dsimp only
  let E : ℝ → ℝ≥0∞ := directResidueRemainderMajorant S A scale f r s N
  let u : ℕ → ℝ → ℂ := directResidueRemainderOutput S A scale f r s
  have hu : ∀ n, MemLp (u n) 2 volume := by
    intro n
    dsimp only [u, directResidueRemainderOutput]
    exact memLp_two_quadraticProjectionRemainderOutput
      (residueScale_nonneg r n)
      (integrable_directScaleInput S A scale f (residueScale r n) s)
  have hreal : AEMeasurable
      (fun x ↦ ENNReal.ofReal (finiteProjectionErrorMajorant N u x)) volume :=
    (memLp_two_finiteProjectionErrorMajorant hu).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hEmeas : AEMeasurable E volume := by
    apply hreal.congr
    exact ae_of_all _ fun x ↦ by
      dsimp only [E, u]
      exact (directResidueRemainderMajorant_eq_ofReal
        S A scale f r s N x).symm
  exact finitePieceTailMax_sq_lintegral_le_of_ae_bound
    N (directResidueOutput S A scale (f : ℝ → ℂ) r s)
      (projectedOffsetResidueOutput S A scale f r s) E hEmeas
      (finitePieceTailMax_directResidueOutput_ae_le_projected_add_remainder
        S A scale f r s N)
      ((4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖))
      (ENNReal.ofReal
        ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
          Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
            Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2))
      (projectedOffsetResidueTailMax_sq_lintegral_le_root_mass
        hA hlam scale hscale f hs hM hmass I₀ hsub hgap r N)
      (lintegral_directResidueRemainderMajorant_sq_le_root
        hA hlam scale hscale f hs hM hmass I₀ hsub hgap r N)

/-- The square of a sum of seven extended-nonnegative values is controlled by
a universal multiple of the sum of their squares. The maximum proof remains
valid even when one of the values is `∞`. -/
private theorem sum_fin_seven_sq_le_fortynine_sum_sq (a : Fin 7 → ℝ≥0∞) :
    (∑ r : Fin 7, a r) ^ 2 ≤ 49 * ∑ r : Fin 7, (a r) ^ 2 := by
  let U : Finset (Fin 7) := Finset.univ
  have hU : U.Nonempty := Finset.univ_nonempty
  let m : ℝ≥0∞ := U.sup' hU a
  have ha (r : Fin 7) (hr : r ∈ U) : a r ≤ m := by
    dsimp only [m]
    exact Finset.le_sup' a hr
  have hsum : (∑ r : Fin 7, a r) ≤ 7 * m := by
    have h := U.sum_le_card_nsmul a m ha
    simpa only [U, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using h
  have hmaxsq : m ^ 2 ≤ ∑ r : Fin 7, (a r) ^ 2 := by
    dsimp only [m]
    rw [Finset.sup'_pow]
    apply Finset.sup'_le hU
    intro r hr
    exact Finset.single_le_sum
      (fun i _ ↦ (bot_le : (0 : ℝ≥0∞) ≤ (a i) ^ 2)) hr
  calc
    (∑ r : Fin 7, a r) ^ 2 ≤ (7 * m) ^ 2 := pow_le_pow_left' hsum 2
    _ = 49 * m ^ 2 := by ring
    _ ≤ 49 * ∑ r : Fin 7, (a r) ^ 2 := mul_le_mul' le_rfl hmaxsq

/-- The seven direct residue-tail maxima have a uniform combined `L²`
square-integral bound. The factor `49` comes from the preceding
extended-nonnegative maximum estimate. -/
theorem sum_directResidueTailMax_sq_lintegral_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (N : ℕ) :
    let B : ℝ≥0∞ :=
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖)
    let C : ℝ≥0∞ := ENNReal.ofReal
      ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
        Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)
    (∫⁻ x, (∑ r : Fin 7, finitePieceTailMax N
      (directResidueOutput S A scale (f : ℝ → ℂ) r s) x) ^ 2) ≤
      1372 * (B + C) := by
  dsimp only
  have hpiece (r : Fin 7) (n : ℕ) : AEMeasurable
      (directResidueOutput S A scale (f : ℝ → ℂ) r s n) volume := by
    have hLp : AEMeasurable
      (offsetOutputScaleLp S A scale f (residueScale r n) s : ℝ → ℂ)
        volume :=
      (Lp.aestronglyMeasurable (offsetOutputScaleLp S A scale f
        (residueScale r n) s)).aemeasurable
    have hdirect := hLp.congr
      (offsetOutputScaleLp_ae_eq_directScaleOutput
        S A scale f (residueScale r n) s)
    simpa only [directResidueOutput] using hdirect
  have htail (r : Fin 7) : AEMeasurable
      (finitePieceTailMax N
        (directResidueOutput S A scale (f : ℝ → ℂ) r s)) volume :=
    aemeasurable_finitePieceTailMax (fun n ↦ hpiece r n)
  have hpoint (x : ℝ) :
      (∑ r : Fin 7, finitePieceTailMax N
        (directResidueOutput S A scale (f : ℝ → ℂ) r s) x) ^ 2 ≤
      49 * ∑ r : Fin 7, (finitePieceTailMax N
        (directResidueOutput S A scale (f : ℝ → ℂ) r s) x) ^ 2 := by
    exact sum_fin_seven_sq_le_fortynine_sum_sq
      (fun r : Fin 7 ↦ finitePieceTailMax N
        (directResidueOutput S A scale (f : ℝ → ℂ) r s) x)
  calc
    (∫⁻ x, (∑ r : Fin 7, finitePieceTailMax N
        (directResidueOutput S A scale (f : ℝ → ℂ) r s) x) ^ 2) ≤
        ∫⁻ x, 49 * ∑ r : Fin 7, (finitePieceTailMax N
          (directResidueOutput S A scale (f : ℝ → ℂ) r s) x) ^ 2 :=
      lintegral_mono hpoint
    _ = 49 * ∑ r : Fin 7, ∫⁻ x, (finitePieceTailMax N
          (directResidueOutput S A scale (f : ℝ → ℂ) r s) x) ^ 2 := by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_finsetSum' _ (fun r _ ↦ (htail r).pow_const 2)]
    _ ≤ 49 * ∑ _r : Fin 7, 4 *
        ((4 + 128 *
          (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
          ENNReal.ofReal
            ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
                (2 : ℝ) ^ (-s)) *
              ∫ x in I₀.carrier, ‖f x‖) +
          ENNReal.ofReal
            ((2 * (Real.pi * projectionRemainderConstant) *
              Real.sqrt (3 * M) * Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
                Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)) := by
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum
      intro r hr
      exact finitePieceTailMax_directResidueOutput_sq_lintegral_le_root
        hA hlam scale hscale f hs hM hmass I₀ hsub hgap r N
    _ = 1372 *
        ((4 + 128 *
          (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
          ENNReal.ofReal
            ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
                (2 : ℝ) ^ (-s)) *
              ∫ x in I₀.carrier, ‖f x‖) +
          ENNReal.ofReal
            ((2 * (Real.pi * projectionRemainderConstant) *
              Real.sqrt (3 * M) * Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
                Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)) := by
      simp
      ring

/-- The paper's direct localized quadratic tail operator inherits the
cardinality-free `L²` estimate from the seven residue classes. -/
theorem offsetTailMaximalOn_sq_lintegral_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (ell₀ : ℤ) (N : ℕ)
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N) :
    let B : ℝ≥0∞ :=
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖)
    let C : ℝ≥0∞ := ENNReal.ofReal
      ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
        Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)
    (∫⁻ x, (offsetTailMaximalOn S A scale (f : ℝ → ℂ) ell₀ s x) ^ 2) ≤
      1372 * (B + C) := by
  dsimp only
  calc
    (∫⁻ x, (offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ s x) ^ 2) ≤
        ∫⁻ x, (∑ r : Fin 7, finitePieceTailMax N
          (directResidueOutput S A scale (f : ℝ → ℂ) r s) x) ^ 2 := by
      apply lintegral_mono
      intro x
      exact pow_le_pow_left'
        (offsetTailMaximalOn_le_sum_seven_tailMax_of_geometry
          S A scale (f : ℝ → ℂ) ell₀ s N x hA hscale hnonneg hbound) 2
    _ ≤ 1372 *
        ((4 + 128 *
          (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
          ENNReal.ofReal
            ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
                (2 : ℝ) ^ (-s)) *
              ∫ x in I₀.carrier, ‖f x‖) +
          ENNReal.ofReal
            ((2 * (Real.pi * projectionRemainderConstant) *
              Real.sqrt (3 * M) * Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
                Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)) :=
      sum_directResidueTailMax_sq_lintegral_le_root
        hA hlam scale hscale f hs hM hmass I₀ hsub hgap N

/-- Seminorm form of the direct localized-tail estimate. The square root is
taken in `ℝ≥0∞`, so this statement also avoids an unnecessary choice of a
real-valued representative of the maximal function. -/
theorem eLpNorm_offsetTailMaximalOn_le_root
    {S A : Finset RealInterval} (hA : A ⊆ S)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hgap : ∀ k ∈ A.image scale,
      ∀ I ∈ A.filter (fun I ↦ scale I = k), 0 ≤ scale I + 2 - s)
    (ell₀ : ℤ) (N : ℕ)
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N) :
    let B : ℝ≥0∞ :=
      (4 + 128 *
        (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
        ENNReal.ofReal
          ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
              (2 : ℝ) ^ (-s)) *
            ∫ x in I₀.carrier, ‖f x‖)
    let C : ℝ≥0∞ := ENNReal.ofReal
      ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
        Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
          Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2)
    eLpNorm (offsetTailMaximalOn S A scale
      (f : ℝ → ℂ) ell₀ s) 2 volume ≤ (1372 * (B + C)) ^ (1 / 2 : ℝ) := by
  dsimp only
  let D : ℝ≥0∞ := 1372 *
    ((4 + 128 *
      (20 * ENNReal.ofReal baseLowPassKernelDecayConstant) ^ 2) *
      ENNReal.ofReal
        ((432 * positiveDyadicAmplitudeBound ^ 2 * M *
            (2 : ℝ) ^ (-s)) *
          ∫ x in I₀.carrier, ‖f x‖) +
      ENNReal.ofReal
        ((2 * (Real.pi * projectionRemainderConstant) * Real.sqrt (3 * M) *
          Real.sqrt (8 * (2 : ℝ) ^ (-s)) *
            Real.sqrt (∫ x in I₀.carrier, ‖f x‖)) ^ 2))
  change eLpNorm (offsetTailMaximalOn S A scale
    (f : ℝ → ℂ) ell₀ s) 2 volume ≤ D ^ (1 / 2 : ℝ)
  have hsq :
      (∫⁻ x, (offsetTailMaximalOn S A scale
        (f : ℝ → ℂ) ell₀ s x) ^ 2) ≤ D := by
    simpa only [D] using offsetTailMaximalOn_sq_lintegral_le_root
      hA hlam scale hscale f hs hM hmass I₀ hsub hgap ell₀ N hnonneg hbound
  have hroot : (D ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = D := by
    rw [← ENNReal.rpow_mul]
    norm_num
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [hroot, ENNReal.rpow_two, eLpNorm_two_sq_lintegral _
    (measurable_offsetTailMaximalOn S A scale f.measurable_toFun ell₀ s).aestronglyMeasurable]
  simpa only [enorm_eq_self] using hsq


end
end KrauseLaceyQuadraticDirectTailProjection
end QuadraticCarleson
