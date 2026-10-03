/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2JointInduction

/-! # Material Spatial

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization
open scoped ContDiff
noncomputable section
namespace AVenhance.Infra.Construction

theorem MaterialSpatial.streamVel_component0_iterated_eq {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 0)
      x (fun k => basisVec (J k)) =
    -iteratedFDeriv ℝ (n + 1) f x
        (Fin.snoc (fun k => basisVec (J k)) (basisVec 1)) := by
  have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => fderiv ℝ f y) :=
    hf.fderiv_right (by simp)
  have hclm : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) :=
    hfderiv.clm_apply contDiff_const
  have hclm_n : ContDiff ℝ n (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) :=
    hclm.of_le (by simp)
  have hval := iteratedFDeriv_clm_apply_const_apply hfderiv (i := n)
    (by simp) (x := x) (u := basisVec 1) (m := fun k => basisVec (J k))
  have hnext := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := f) (x := x)
    (Fin.snoc (fun k => basisVec (J k)) (basisVec 1))
  have hcoord : (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 0) =
      fun y => -((fderiv ℝ f y) (basisVec 1)) := by
    funext y
    simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, basisVec]
  rw [hcoord]
  rw [show (fun y : Vec 2 => -((fderiv ℝ f y) (basisVec 1))) =
      fun y => (-1 : ℝ) • ((fderiv ℝ f y) (basisVec 1)) by ext y; simp]
  have hsmul := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := n)
    (f := fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) (x := x)
    (a := (-1 : ℝ)) hclm_n.contDiffAt
  have hneg : iteratedFDeriv ℝ n
      (fun y : Vec 2 => (-1 : ℝ) • ((fderiv ℝ f y) (basisVec 1))) x
      (fun k => basisVec (J k)) =
      -iteratedFDeriv ℝ n
        (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) x
        (fun k => basisVec (J k)) := by
    have h := congrArg (fun T => T (fun k => basisVec (J k))) hsmul
    simpa [smul_eq_mul] using h
  calc
    _ = -iteratedFDeriv ℝ n
        (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 1)) x
        (fun k => basisVec (J k)) := hneg
    _ = -((iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x
          (fun k => basisVec (J k))) (basisVec 1)) := by rw [hval]
    _ = -iteratedFDeriv ℝ (n + 1) f x
          (Fin.snoc (fun k => basisVec (J k)) (basisVec 1)) := by
      simpa using congrArg (fun z : ℝ => -z) hnext.symm

theorem MaterialSpatial.streamVel_component1_iterated_eq {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 1)
      x (fun k => basisVec (J k)) =
    iteratedFDeriv ℝ (n + 1) f x
        (Fin.snoc (fun k => basisVec (J k)) (basisVec 0)) := by
  have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => fderiv ℝ f y) :=
    hf.fderiv_right (by simp)
  have hval := iteratedFDeriv_clm_apply_const_apply hfderiv (i := n)
    (by simp) (x := x) (u := basisVec 0) (m := fun k => basisVec (J k))
  have hnext := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := f) (x := x)
    (Fin.snoc (fun k => basisVec (J k)) (basisVec 0))
  have hcoord : (fun y : Vec 2 => streamVel (fun _ z => f z) 0 y 1) =
      fun y => (fderiv ℝ f y) (basisVec 0) := by
    funext y
    simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, basisVec]
  calc
    _ = iteratedFDeriv ℝ n (fun y : Vec 2 => (fderiv ℝ f y) (basisVec 0)) x
        (fun k => basisVec (J k)) := by rw [hcoord]
    _ = (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x
          (fun k => basisVec (J k))) (basisVec 0) := hval
    _ = iteratedFDeriv ℝ (n + 1) f x
          (Fin.snoc (fun k => basisVec (J k)) (basisVec 0)) := by
      simpa using hnext.symm

theorem MaterialSpatial.basisVec_snoc {n : ℕ} (J : Fin n → Fin 2) (j : Fin 2) :
    Fin.snoc (fun i => basisVec (J i)) (basisVec j) =
      fun k => basisVec ((Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) J j) k) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp [Fin.snoc]
  · intro i
    simp [Fin.snoc]

theorem MaterialSpatial.material_potential_normalization {β : ℝ} {I : Ingredients β}
    (m p N : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) :
    let e := epsilon β I.Λ m
    let R := 2 ^ 8 * e⁻¹
    let B := 2 ^ 5 * a β I.Λ m * e ^ 2 *
      (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3)
    let K := (2 : ℝ) ^ (8 * N + 6) * (N.factorial : ℝ)
    B / (((p : ℝ) + 1) ^ 2 / (p.factorial : ℝ) * R⁻¹ ^ p) ≤
      K * e ^ (β - (p : ℝ)) := by
  let e : ℝ := epsilon β I.Λ m
  let R : ℝ := 2 ^ 8 * e⁻¹
  let B : ℝ := 2 ^ 5 * a β I.Λ m * e ^ 2 *
    (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3)
  let K : ℝ := (2 : ℝ) ^ (8 * N + 6) * (N.factorial : ℝ)
  have he : 0 < e := by
    dsimp [e]
    exact Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have hpoly : ((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3 ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).2
    have hx : 2 ≤ (p : ℝ) + 1 := by linarith
    have hnum : ((p : ℝ) + 2) ^ 2 ≤ 4 * ((p : ℝ) + 1) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 * ((p : ℝ) + 1) ^ 2)
    nlinarith [hnum, hmul]
  have hfact : (p.factorial : ℝ) ≤ (N.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hpN
  have hpowNat : 2 ^ (8 * p) ≤ 2 ^ (8 * N) := by
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.mul_le_mul_left 8 hpN
  have hpow : (2 : ℝ) ^ (8 * p) ≤ (2 : ℝ) ^ (8 * N) := by exact_mod_cast hpowNat
  have hcoeff :
      2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
        (p.factorial : ℝ) / ((p : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (8 * p) ≤ K := by
    have hden : 1 ≤ ((p : ℝ) + 1) ^ 2 := by
      have hpnn : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
      nlinarith
    have hstep :
        2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
          (p.factorial : ℝ) / ((p : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (8 * p) ≤
        2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
          (p.factorial : ℝ) * (2 : ℝ) ^ (8 * p) := by
      have hA : 0 ≤ 2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
          (p.factorial : ℝ) := by positivity
      have hz : 0 ≤ (2 : ℝ) ^ (8 * p) := by positivity
      have hdiv :
          (2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
            (p.factorial : ℝ)) / ((p : ℝ) + 1) ^ 2 ≤
          2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
            (p.factorial : ℝ) :=
        div_le_self hA (by linarith)
      exact mul_le_mul_of_nonneg_right hdiv hz
    have hsmall :
        2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
          (p.factorial : ℝ) * (2 : ℝ) ^ (8 * p) ≤
        2 ^ 6 * (N.factorial : ℝ) * (2 : ℝ) ^ (8 * N) := by
      calc
        _ = (2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3)) *
              (p.factorial : ℝ) * (2 : ℝ) ^ (8 * p) := by ring
        _ ≤ (2 ^ 5 * 2) * (p.factorial : ℝ) * (2 : ℝ) ^ (8 * p) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpoly (by positivity)) (Nat.cast_nonneg _)
          · positivity
        _ ≤ (2 ^ 5 * 2) * (N.factorial : ℝ) * (2 : ℝ) ^ (8 * p) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hfact (by positivity)
          · positivity
        _ ≤ (2 ^ 5 * 2) * (N.factorial : ℝ) * (2 : ℝ) ^ (8 * N) := by
          apply mul_le_mul_of_nonneg_left hpow
          positivity
        _ = 2 ^ 6 * (N.factorial : ℝ) * (2 : ℝ) ^ (8 * N) := by ring
    calc
      _ ≤ 2 ^ 6 * (N.factorial : ℝ) * (2 : ℝ) ^ (8 * N) := hstep.trans hsmall
      _ = K := by
        dsimp [K]
        rw [pow_add]
        ring
  have haE : a β I.Λ m * e ^ 2 = e ^ β := by
    dsimp [a, e]
    rw [← Real.rpow_natCast (epsilon β I.Λ m) 2,
      ← Real.rpow_add (Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)]
    congr 1
    ring
  have hRinv : R⁻¹ = e / (2 ^ 8 : ℝ) := by
    dsimp [R]
    field_simp [ne_of_gt he]
  have hpowR : R⁻¹ ^ p = e ^ p / (2 : ℝ) ^ (8 * p) := by
    rw [hRinv, div_pow]
    simp [pow_mul]
  have hnorm : B / (((p : ℝ) + 1) ^ 2 / (p.factorial : ℝ) * R⁻¹ ^ p) =
      (2 ^ 5 * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) *
        (p.factorial : ℝ) / ((p : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (8 * p)) *
        e ^ (β - (p : ℝ)) := by
    dsimp [B]
    have hB : 2 ^ 5 * a β I.Λ m * e ^ 2 *
        (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) =
        2 ^ 5 * e ^ β * (((p : ℝ) + 2) ^ 2 / ((p : ℝ) + 1) ^ 3) := by
      rw [← haE]
      ring
    rw [hB, hpowR, ← Real.rpow_natCast e p, Real.rpow_sub he]
    field_simp [ne_of_gt he]
  change B / (((p : ℝ) + 1) ^ 2 / (p.factorial : ℝ) * R⁻¹ ^ p) ≤
    K * e ^ (β - (p : ℝ))
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg he.le _)

theorem MaterialSpatial.iteratedFDeriv_component {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Fin 2) (i : Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => f y i) x (fun k => basisVec (J k)) =
      iteratedFDeriv ℝ n f x (fun k => basisVec (J k)) i := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hcomp := P.iteratedFDeriv_comp_left
    (f := f) (x := x) hfN.contDiffAt (i := n) le_rfl
  change iteratedFDeriv ℝ n (P ∘ f) x
    (fun k => basisVec (J k)) = _
  rw [hcomp]
  rfl

theorem MaterialSpatial.iteratedFDeriv_gradient_scalar_eq {g : Vec 2 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (q : ℕ) (x : Vec 2)
    (J : Fin q → Fin 2) (j : Fin 2) :
    iteratedFDeriv ℝ q (fun y : Vec 2 => fderiv ℝ g y (basisVec j)) x
      (fun k => basisVec (J k)) =
    iteratedFDeriv ℝ (q + 1) g x (Fin.snoc (fun k => basisVec (J k)) (basisVec j)) := by
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => fderiv ℝ g y) :=
    hg.fderiv_right (by simp)
  have hval := iteratedFDeriv_clm_apply_const_apply hdf (i := q)
    (by simp) (x := x) (u := basisVec j) (m := fun k => basisVec (J k))
  have hnext := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := g) (x := x)
    (Fin.snoc (fun k => basisVec (J k)) (basisVec j))
  calc
    _ = (iteratedFDeriv ℝ q (fun y : Vec 2 => fderiv ℝ g y) x
        (fun k => basisVec (J k))) (basisVec j) := hval
    _ = iteratedFDeriv ℝ (q + 1) g x
        (Fin.snoc (fun k => basisVec (J k)) (basisVec j)) := by simpa using hnext.symm

theorem MaterialSpatial.fderiv_component_apply {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y : Vec 2 => f y i) x (basisVec j) =
      fderiv ℝ f x (basisVec j) i := by
  have hd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have h := fderiv_apply hd i
  have h' := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) h
  simpa using h'

theorem MaterialSpatial.material_scale_identity_shift2 {β e : ℝ} (he : 0 < e) (n : ℕ) :
    e ^ (β - ((n : ℝ) + 2)) = e ^ (β - 2) * e⁻¹ ^ n := by
  rw [Real.rpow_sub he β ((n : ℝ) + 2), Real.rpow_sub he β 2]
  have hden : e ^ ((n : ℝ) + 2) = e ^ (2 : ℝ) * (e ^ n) := by
    rw [Real.rpow_add he]
    rw [Real.rpow_natCast]
    ring
  rw [hden]
  rw [inv_pow]
  field_simp [ne_of_gt he, ne_of_gt (pow_pos he n)]

theorem MaterialSpatial.material_scale_identity {β e : ℝ} (he : 0 < e) (n : ℕ) :
    e ^ (β - ((n : ℝ) + 1)) = e ^ (β - 1) * e⁻¹ ^ n := by
  rw [Real.rpow_sub he β ((n : ℝ) + 1), Real.rpow_sub he β 1]
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_cast
  rw [hcast, Real.rpow_natCast e (n + 1), Real.rpow_one, pow_succ]
  field_simp [ne_of_gt he]
  simp [ne_of_gt he]

end AVenhance.Infra.Construction
end
