/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevInterpolation
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution

@[expose] public section

/-! Actual uniform-in-time interpolation and its Cauchy consequence. -/

noncomputable section

namespace EulerSobolevPathInterpolation

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevInterpolation
open scoped Topology

/-- A squared difference estimate transfers the Cauchy property without an unproved interpolation premise. -/
theorem cauchySeq_of_square_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℕ → E) (g : ℕ → F) (A : ℝ) (hA : 0 ≤ A) (hf : CauchySeq f)
    (h : ∀ m n, ‖g m-g n‖^2 ≤ A*‖f m-f n‖) : CauchySeq g := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hd : 0 < ε^2/(A+1) := div_pos (sq_pos_of_pos hε) (by linarith)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hf (ε^2/(A+1)) hd
  refine ⟨N,fun m hm n hn => ?_⟩
  have hs := h m n
  have hp := hN m hm n hn
  rw [dist_eq_norm] at hp ⊢
  have hsmall : (A+1)*‖f m-f n‖ < ε^2 := by
    have hh := (lt_div_iff₀ (by linarith : 0 < A+1)).mp hp
    nlinarith only [hh]
  have hf0 := norm_nonneg (f m-f n)
  have hg0 := norm_nonneg (g m-g n)
  nlinarith

/-- Linear interpolation bounds transfer to differences using only the two state bounds. -/
private theorem clm_difference_square_bound {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A B : V →L[ℝ] W) (h : ∀ u, ‖A u‖^2 ≤ ‖B u‖*‖u‖)
    (M : ℝ) (u v : V) (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖A u-A v‖^2 ≤ 2*M*‖B u-B v‖ := by
  have hb := h (u-v)
  rw [map_sub, map_sub] at hb
  have hs : ‖u-v‖ ≤ 2*M :=
    (norm_sub_le u v).trans ((add_le_add hu hv).trans_eq (two_mul M).symm)
  exact hb.trans ((mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq (mul_comm _ _))

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group on each actual Sobolev space. -/
local instance interpolationGroup (s : ℕ) : NormedAddCommGroup (SobolevSpace period s) :=
  inferInstance

/-- The inherited real normed space on each actual Sobolev space. -/
local instance interpolationSpace (s : ℕ) : NormedSpace ℝ (SobolevSpace period s) := inferInstance

/-- One actual Sobolev derivative coordinate as a continuous time-path operator. -/
def wordPathOperator {s n : ℕ} (h : n ≤ s) (w : Fin n → Fin 4) (T : ℝ) :
    C(Icc (0 : ℝ) T,SobolevSpace period s) →L[ℝ] C(Icc (0 : ℝ) T,LiftL2 period) :=
  (wordOperator period ⟨⟨n,Nat.lt_succ_of_le h⟩,w⟩).compLeftContinuous ℝ (Icc (0 : ℝ) T)

/-- The derivative path is its literal derivative coordinate at each time. -/
theorem wordPathOperator_apply {s n : ℕ} (h : n ≤ s) (w : Fin n → Fin 4) (T : ℝ)
    (u : C(Icc (0 : ℝ) T,SobolevSpace period s)) (t : Icc (0 : ℝ) T) :
    wordPathOperator period h w T u t = word period (u t) h w := rfl

/-- The exact strong-derivative interpolation inequality also controls the uniform time-path norm. -/
theorem wordPath_square_bound {s n : ℕ} (h : n+2 ≤ s) (w : Fin n → Fin 4) (i : Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T,SobolevSpace period s)) :
    ‖wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T u‖^2 ≤
      ‖wordPathOperator period (by omega : n ≤ s) w T u‖*‖u‖ := by
  let A := ‖wordPathOperator period (by omega : n ≤ s) w T u‖*‖u‖
  have hA : 0 ≤ A := mul_nonneg
    (norm_nonneg (wordPathOperator period (by omega : n ≤ s) w T u)) (norm_nonneg u)
  have hb : ‖wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T u‖ ≤ Real.sqrt A := by
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg A)).mpr
    intro t
    apply Real.le_sqrt_of_sq_le
    exact (word_square_le_parent period h (u t) w i).trans
      (mul_le_mul ((wordPathOperator period (by omega : n ≤ s) w T u).norm_coe_le_norm t)
        (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg A)).mpr hb
  rw [Real.sq_sqrt hA] at hs
  exact hs

/-- Actual derivative-coordinate paths preserve subtraction. -/
theorem wordPath_sub {s n : ℕ} (h : n ≤ s) (w : Fin n → Fin 4) (T : ℝ)
    (u v : C(Icc (0 : ℝ) T,SobolevSpace period s)) :
    wordPathOperator period h w T (u-v) = wordPathOperator period h w T u-wordPathOperator period h
      w T v := by
  ext t
  rfl

/-- The actual difference interpolation estimate depends only on the two given uniform state bounds. -/
theorem wordPath_difference_square_bound {s n : ℕ} (h : n+2 ≤ s) (w : Fin n → Fin 4) (i : Fin 4)
    (T M : ℝ) (u v : C(Icc (0 : ℝ) T,SobolevSpace period s)) (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T u-
      wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T v‖^2 ≤
      2*M*‖wordPathOperator period (by omega : n ≤ s) w T u-wordPathOperator period (by omega : n ≤
        s) w T v‖ := by
  exact clm_difference_square_bound
    (V := C(Icc (0 : ℝ) T,SobolevSpace period s))
    (W := C(Icc (0 : ℝ) T,LiftL2 period))
    (wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T)
    (wordPathOperator period (by omega : n ≤ s) w T)
    (wordPath_square_bound period h w i T) M u v hu hv

/-- Uniformly bounded actual Sobolev paths transfer Cauchy control from a parent word to a derivative. -/
theorem wordPath_cauchy_step {s n : ℕ} (h : n+2 ≤ s) (w : Fin n → Fin 4) (i : Fin 4)
    (T M : ℝ) (hM : 0 ≤ M) (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period s))
    (hu : ∀ k, ‖u k‖ ≤ M)
    (hw : CauchySeq (fun k => wordPathOperator period (by omega : n ≤ s) w T (u k))) :
    CauchySeq (fun k => wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T (u k)) :=
  cauchySeq_of_square_bound _ _ (2*M) (by positivity) hw
    (fun k l => wordPath_difference_square_bound period h w i T M (u k) (u l) (hu k) (hu l))

end EulerSobolevPathInterpolation
