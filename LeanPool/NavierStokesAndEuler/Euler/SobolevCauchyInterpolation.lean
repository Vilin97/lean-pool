/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevPathInterpolation
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction

/-! Uniform Sobolev bounds and actual L² convergence give strong convergence below the top
derivative order. -/

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
