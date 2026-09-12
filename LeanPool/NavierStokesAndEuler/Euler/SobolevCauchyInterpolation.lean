/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative

/-! Uniform Sobolev bounds and actual L² convergence give strong convergence below the top
derivative order. -/

section

/-! Actual uniform-in-time interpolation and its Cauchy consequence. -/

section

/-! Strong-derivative interpolation on the actual cylinder Sobolev spaces. -/

@[expose] public section

noncomputable section

namespace EulerSobolevInterpolation

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLiftedWeakDerivative
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- One genuine derivative is controlled by its parent word and one available higher derivative. -/
theorem word_square_le_parent {s n : ℕ} (h : n + 2 ≤ s) (u : SobolevSpace period s)
    (w : Fin n → Fin 4) (i : Fin 4) :
    ‖word period u (by omega : n+1 ≤ s) (Fin.cons i w)‖^2 ≤
      ‖word period u (by omega : n ≤ s) w‖*‖u‖ := by
  have hp := translation_derivative_pairing period (standardDirection i)
    (word period u (by omega : n ≤ s) w)
    (word period u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word period u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word period u h (Fin.cons i (Fin.cons i w)))
    (word_hasDerivAt period u (by omega : n < s) w i)
    (word_hasDerivAt period u (by omega : n+1 < s) (Fin.cons i w) i)
  rw [real_inner_self_eq_norm_sq] at hp
  calc
    _ = -inner ℝ (word period u (by omega : n ≤ s) w)
        (word period u h (Fin.cons i (Fin.cons i w))) := hp
    _ ≤ |inner ℝ (word period u (by omega : n ≤ s) w)
        (word period u h (Fin.cons i (Fin.cons i w)))| := neg_le_abs _
    _ ≤ ‖word period u (by omega : n ≤ s) w‖*
        ‖word period u h (Fin.cons i (Fin.cons i w))‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (word_norm_le period u ⟨⟨n+2,Nat.lt_succ_of_le h⟩,Fin.cons i (Fin.cons i w)⟩) (norm_nonneg _)

end EulerSobolevInterpolation

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevPathInterpolation

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevInterpolation
open scoped Topology

/-- A squared difference estimate transfers the Cauchy property without an unproved interpolation
premise. -/
theorem cauchySeq_of_square_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℕ → E) (g : ℕ → F) (A : ℝ) (hA : 0 ≤ A) (hf : CauchySeq f)
    (h : ∀ m n, ‖g m - g n‖ ^ 2 ≤ A * ‖f m - f n‖) : CauchySeq g := by
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
    (A B : V →L[ℝ] W) (h : ∀ u, ‖A u‖ ^ 2 ≤ ‖B u‖ * ‖u‖)
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
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s)) (t : Icc (0 : ℝ) T) :
    wordPathOperator period h w T u t = word period (u t) h w := rfl

/-- The exact strong-derivative interpolation inequality also controls the uniform time-path norm.
-/
theorem wordPath_square_bound {s n : ℕ} (h : n + 2 ≤ s) (w : Fin n → Fin 4) (i : Fin 4)
    (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period s)) :
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
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period s)) :
    wordPathOperator period h w T (u-v) = wordPathOperator period h w T u-wordPathOperator period h
        w T v := by
  ext t
  rfl

/-- The actual difference interpolation estimate depends only on the two given uniform state bounds.
-/
theorem wordPath_difference_square_bound {s n : ℕ} (h : n + 2 ≤ s) (w : Fin n → Fin 4) (i : Fin 4)
    (T M : ℝ) (u v : C(Icc (0 : ℝ) T, SobolevSpace period s)) (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T u -
      wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T v‖^2 ≤
      2*M*‖wordPathOperator period (by
          omega : n ≤ s) w T u-wordPathOperator period (by omega : n ≤ s) w T v‖ := by
  exact clm_difference_square_bound
    (V := C(Icc (0 : ℝ) T,SobolevSpace period s))
    (W := C(Icc (0 : ℝ) T,LiftL2 period))
    (wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T)
    (wordPathOperator period (by omega : n ≤ s) w T)
    (wordPath_square_bound period h w i T) M u v hu hv

/-- Uniformly bounded actual Sobolev paths transfer Cauchy control from a parent word to a
derivative. -/
theorem wordPath_cauchy_step {s n : ℕ} (h : n + 2 ≤ s) (w : Fin n → Fin 4) (i : Fin 4)
    (T M : ℝ) (hM : 0 ≤ M) (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period s))
    (hu : ∀ k, ‖u k‖ ≤ M)
    (hw : CauchySeq (fun k => wordPathOperator period (by omega : n ≤ s) w T (u k))) :
    CauchySeq (fun k => wordPathOperator period (by omega : n+1 ≤ s) (Fin.cons i w) T (u k)) :=
  cauchySeq_of_square_bound _ _ (2*M) (by positivity) hw
    (fun k l => wordPath_difference_square_bound period h w i T M (u k) (u l) (hu k) (hu l))

end EulerSobolevPathInterpolation

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevCauchyInterpolation

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevPathInterpolation
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group on the actual Sobolev state space. -/
local instance cauchySobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

/-- The inherited real normed space on the actual Sobolev state space. -/
local instance cauchySobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- Every actual derivative coordinate below the top uniformly bounded order is a Cauchy path. -/
theorem wordPath_cauchy_of_value {s : ℕ} (T M : ℝ) (hM : 0 ≤ M)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period s)) (hu : ∀ k, ‖u k‖ ≤ M)
    (h0 : CauchySeq (fun k => (valueOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k)))
        :
    ∀ (n : ℕ) (hn : n < s) (w : Fin n → Fin 4),
      CauchySeq (fun k => wordPathOperator period hn.le w T (u k)) := by
  intro n
  induction n with
  | zero =>
    intro hn w
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact h0
  | succ n ih =>
    intro hn w
    have h := wordPath_cauchy_step period (by omega : n+2 ≤ s) (Fin.tail w) (w 0) T M hM u hu
      (ih (by omega) (Fin.tail w))
    simpa only [Fin.cons_self_tail] using h

/-- The complete Sobolev time path expressed by its finitely many literal coordinate paths. -/
def pathCoordinates (q : ℕ) (T : ℝ) :
    C(Icc (0 : ℝ) T,SobolevSpace period q) →L[ℝ]
      (SobolevWord q → C(Icc (0 : ℝ) T,LiftL2 period)) :=
  ContinuousLinearMap.pi (fun w => wordPathOperator period (Nat.le_of_lt_succ w.1.isLt) w.2 T)

/-- The actual finite-coordinate path map preserves the full uniform Sobolev norm exactly. -/
theorem pathCoordinates_norm (q : ℕ) (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    ‖pathCoordinates period q T u‖ = ‖u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro w
    apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
    intro t
    exact (word_norm_le period (u t) w).trans (u.norm_coe_le_norm t)
  · apply (ContinuousMap.norm_le u (norm_nonneg (pathCoordinates period q T u))).mpr
    intro t
    change ‖(u t).val‖ ≤ _
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (pathCoordinates period q T u))).mpr
    intro w
    exact ((pathCoordinates period q T u w).norm_coe_le_norm t).trans
      (norm_le_pi_norm (pathCoordinates period q T u) w)

/-- Cauchy control of every actual coordinate path gives Cauchy control in the complete Sobolev path
space. -/
theorem path_cauchy_of_coordinates (q : ℕ) (T : ℝ)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period q))
    (hu : ∀ w : SobolevWord q, CauchySeq (fun k => pathCoordinates period q T (u k) w)) : CauchySeq
        u := by
  have hi : Isometry (pathCoordinates period q T) :=
    AddMonoidHomClass.isometry_of_norm _ (pathCoordinates_norm period q T)
  have hc : CauchySeq (fun k => pathCoordinates period q T (u k)) := by
    unfold CauchySeq
    apply (cauchy_pi_iff' (fun _ : SobolevWord q => C(Icc (0 : ℝ) T,LiftL2 period))).mpr
    intro w
    simpa only [CauchySeq,Filter.map_map,Function.comp_def] using hu w
  have h := hi.isUniformInducing.cauchy_map_iff (F := Filter.map u Filter.atTop)
  apply h.mp
  simpa only [CauchySeq,Filter.map_map,Function.comp_def] using hc

/-- A uniformly bounded actual Sobolev sequence that is Cauchy in L² is Cauchy at every strictly
lower Sobolev order, uniformly in time. -/
theorem cauchy_restrict_of_value {s q : ℕ} (hq : q < s) (T M : ℝ) (hM : 0 ≤ M)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period s)) (hu : ∀ k, ‖u k‖ ≤ M)
    (h0 : CauchySeq (fun k => (valueOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k)))
        :
    CauchySeq (fun k => (restrictOperator period hq.le).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k))
        := by
  apply path_cauchy_of_coordinates period q T
  intro w
  exact wordPath_cauchy_of_value period T M hM u hu h0 w.1.val
    ((Nat.le_of_lt_succ w.1.isLt).trans_lt hq) w.2

/-- Completeness produces the actual strong lower-order Sobolev limit from those concrete bounds. -/
theorem exists_limit_restrict_of_value {s q : ℕ} (hq : q < s) (T M : ℝ) (hM : 0 ≤ M)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period s)) (hu : ∀ k, ‖u k‖ ≤ M)
    (h0 : CauchySeq (fun k => (valueOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k)))
        :
    ∃ v : C(Icc (0 : ℝ) T,SobolevSpace period q),
      Filter.Tendsto (fun k => (restrictOperator period hq.le).compLeftContinuous ℝ (Icc (0 : ℝ) T)
          (u k))
        Filter.atTop (𝓝 v) :=
  cauchySeq_tendsto_of_complete (cauchy_restrict_of_value period hq T M hM u hu h0)

end EulerSobolevCauchyInterpolation
