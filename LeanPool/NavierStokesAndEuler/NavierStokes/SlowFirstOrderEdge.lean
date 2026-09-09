/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalEdgeFactor
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalHeatCoordinates
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalPressure
import LeanPool.NavierStokesAndEuler.NavierStokes.EdgeWeightJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The first slow-order stress at the terminal edge

The source is the angular axial-viscosity term.  Its primitive is the actual
backward integral with weight `R²`.  The coefficient chart is `(η,δ)`, including
both endpoints `η=±1`; its heat carrier uses the genuine smooth heat extension.
-/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open scoped BigOperators
open NavierStokes.OutgoingTail NavierStokes.TerminalStress
open NavierStokes.TerminalEdgeFactor

namespace NavierStokes.SlowFirstOrderEdge

/-- Beta, given by `(2 * CoordinateAlgebra.D d.h * η * profileChi d η - (1 - η ^ 2) * deriv
(profileChi d) η) / profileL d η`. -/
noncomputable def beta (d : TailData) (η : ℝ) : ℝ :=
  (2 * CoordinateAlgebra.D d.h * η * profileChi d η -
    (1 - η ^ 2) * deriv (profileChi d) η) / profileL d η

theorem beta_contDiff (d : TailData) : ContDiff ℝ ∞ (beta d) :=
  (((contDiff_const.mul contDiff_id).mul (profileChi_contDiff d)).sub
    ((contDiff_const.sub (contDiff_id.pow 2)).mul
      (contDiff_infty_iff_deriv.mp (profileChi_contDiff d)).2)).div
    (profileL_contDiff d) (fun η => (profileL_pos d η).ne')

/-- Taper second factor, given by `-8 * taperSlopeFactor d x + 3 * x ^ 2 * taperSlopeFactor d x
- x ^ 3 * deriv (taperSlopeFactor d) x`. -/
noncomputable def taperSecondFactor (d : TailData) (x : ℝ) : ℝ :=
  -8 * taperSlopeFactor d x + 3 * x ^ 2 * taperSlopeFactor d x -
    x ^ 3 * deriv (taperSlopeFactor d) x

theorem taperSecondFactor_contDiff (d : TailData) : ContDiff ℝ ∞ (taperSecondFactor d) :=
  ((contDiff_const.mul (taperSlopeFactor_contDiff d)).add
    ((contDiff_const.mul (contDiff_id.pow 2)).mul (taperSlopeFactor_contDiff d))).sub
    ((contDiff_id.pow 3).mul (contDiff_infty_iff_deriv.mp (taperSlopeFactor_contDiff d)).2)

theorem taperSecond_factorization (d : TailData) (x : ℝ) :
    deriv (tailShapeDeriv d) (3 - x) =
      (FlatCutoff.edge 4 x / x ^ 6) * taperSecondFactor d x := by
  let W : ℝ → ℝ := fun u => FlatCutoff.edge 4 u / u ^ 3
  have hW : ContDiff ℝ ∞ W := FlatCutoff.edge_div_pow_contDiff (by norm_num) 3
  have hL := ((tailShapeDeriv_contDiff d).differentiable (by simp) (3 - x)).hasDerivAt.comp x
    ((hasDerivAt_id x).const_sub 3)
  have hR := ((hW.differentiable (by simp) x).hasDerivAt).mul
    ((taperSlopeFactor_contDiff d).differentiable (by simp) x).hasDerivAt
  have he : (fun u => tailShapeDeriv d (3 - u)) = fun u => W u * taperSlopeFactor d u :=
    funext (tailShapeDeriv_factorization d)
  change HasDerivAt (fun u => tailShapeDeriv d (3 - u))
    (deriv (tailShapeDeriv d) (3 - x) * -1) x at hL
  rw [he] at hL
  have hh := hL.unique hR
  simp only [mul_neg_one] at hh
  by_cases hx : x = 0
  · subst x
    have hz : deriv W 0 = 0 := by
      apply norm_eq_zero.mp
      have ht := congrArg norm (EdgeWeightJets.edge_div_pow_iteratedFDeriv_zero
        (by norm_num : (0 : ℝ) < 4) 3 1)
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
        norm_zero] using ht
    have hW0 : W 0 = 0 := by simp [W]
    simp only [hz, hW0, zero_mul, add_zero] at hh
    simp only [FlatCutoff.edge_zero, zero_pow (by norm_num : 6 ≠ 0), div_zero, zero_mul]
    linarith
  · have hdW := ((FlatPrimitive.edge_hasDerivAt (by norm_num : (0 : ℝ) < 4) x).div
      ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx)).deriv
    change deriv W x = _ at hdW
    have hdW' : deriv W x = (8 * FlatCutoff.edge 4 x -
        3 * x ^ 2 * FlatCutoff.edge 4 x) / x ^ 6 := by
      rw [hdW]
      dsimp only [id]
      norm_num
      field_simp [hx]
    rw [hdW'] at hh
    calc
      _ = -((8 * FlatCutoff.edge 4 x - 3 * x ^ 2 * FlatCutoff.edge 4 x) / x ^ 6 *
          taperSlopeFactor d x + (FlatCutoff.edge 4 x / x ^ 3) *
            deriv (taperSlopeFactor d) x) := by dsimp only [W] at hh; linarith
      _ = _ := by unfold taperSecondFactor; field_simp [hx] ; ring

/-- The normalized negative axial-viscosity source, before radial integration. -/
noncomputable def profileSource (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  -profileCarrier C d y0 y *
    (profileChi d y.1 ^ 2 * deriv (tailShapeDeriv d) (3 - y.2) +
      beta d y.1 * tailShapeDeriv d (3 - y.2))

/-- Source factor, given by `-profileCarrier C d y0 y * (profileChi d y.1 ^ 2 *
taperSecondFactor d y.2 + beta d y.1 * y.2 ^ 3 * taperSlopeFactor d y.2)`. -/
noncomputable def sourceFactor (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  -profileCarrier C d y0 y *
    (profileChi d y.1 ^ 2 * taperSecondFactor d y.2 +
      beta d y.1 * y.2 ^ 3 * taperSlopeFactor d y.2)

theorem sourceFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (sourceFactor C d y0) :=
  (profileCarrier_contDiff C d y0).neg.mul
    (((((profileChi_contDiff d).comp contDiff_fst).pow 2).mul
      ((taperSecondFactor_contDiff d).comp contDiff_snd)).add
      ((((beta_contDiff d).comp contDiff_fst).mul (contDiff_snd.pow 3)).mul
        ((taperSlopeFactor_contDiff d).comp contDiff_snd)))

theorem profileSource_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) :
    profileSource C d y0 y = (FlatCutoff.edge 4 y.2 / y.2 ^ 6) * sourceFactor C d y0 y := by
  rw [profileSource, taperSecond_factorization, tailShapeDeriv_factorization]
  unfold sourceFactor
  by_cases hx : y.2 = 0
  · simp [hx]
  · field_simp [hx]

theorem profileSource_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileSource C d y0) := by
  have he : profileSource C d y0 = EdgeWeightJets.weighted 4 6 (sourceFactor C d y0) :=
    funext (profileSource_factorization C d y0)
  rw [he]
  exact EdgeWeightJets.weighted_contDiff (by norm_num) 6 (sourceFactor_contDiff C d y0)

/-- Primitive coefficient, given by `(profileRadius y0 y.2 ^ 3 / 2) * sourceFactor C d y0 y`. -/
noncomputable def primitiveCoefficient (C : ℝ) (d : TailData) (y0 : ℝ)
    (y : ℝ × ℝ) : ℝ :=
  (profileRadius y0 y.2 ^ 3 / 2) * sourceFactor C d y0 y

theorem primitiveCoefficient_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (primitiveCoefficient C d y0) :=
  (((profileRadius_contDiff y0).comp contDiff_snd).pow 3).div_const 2 |>.mul
    (sourceFactor_contDiff C d y0)

/-- The source in the positive normalized radial variable `R=√(2X)`. -/
noncomputable def radialSource (C : ℝ) (d : TailData) (y0 η R : ℝ) : ℝ :=
  profileSource C d y0 (η, edgeCoordinate (profileRadius y0 0) R)

/-- The genuine backward weighted radial primitive, with the stress sign convention. -/
noncomputable def radialStress (C : ℝ) (d : TailData) (y0 η R : ℝ) : ℝ :=
  backwardStress (radialSource C d y0 η) R

/-- Profile stress, given by `radialStress C d y0 y.1 (profileRadius y0 y.2)`. -/
noncomputable def profileStress (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  radialStress C d y0 y.1 (profileRadius y0 y.2)

/-- Stress factor, given by `ParametricFlatFactor.factor 4 6 (primitiveCoefficient C d y0) y /
profileRadius y0 y.2 ^ 2`. -/
noncomputable def stressFactor (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) : ℝ :=
  ParametricFlatFactor.factor 4 6 (primitiveCoefficient C d y0) y / profileRadius y0 y.2 ^ 2

theorem stressFactor_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (stressFactor C d y0) :=
  (ParametricFlatFactor.factor_contDiff (by norm_num : (0 : ℝ) < 4) 6
    (primitiveCoefficient_contDiff C d y0)).div
    (((profileRadius_contDiff y0).comp contDiff_snd).pow 2)
    (fun y => (pow_pos (profileRadius_pos y0 y.2) 2).ne')

theorem profileRadius_eq (y0 x : ℝ) :
    profileRadius y0 x = profileRadius y0 0 * Real.exp (-x / 2) := by
  simp [profileRadius]

theorem profileRadius_edgeCoordinate (y0 : ℝ) {R : ℝ} (hR : 0 < R) :
    profileRadius y0 (edgeCoordinate (profileRadius y0 0) R) = R := by
  rw [profileRadius_eq]
  have he : -edgeCoordinate (profileRadius y0 0) R / 2 =
      Real.log (R / profileRadius y0 0) := by unfold edgeCoordinate; ring
  rw [he, Real.exp_log (div_pos hR (profileRadius_pos y0 0))]
  field_simp [(profileRadius_pos y0 0).ne']

theorem edgeCoordinate_profileRadius (y0 x : ℝ) :
    edgeCoordinate (profileRadius y0 0) (profileRadius y0 x) = x := by
  rw [profileRadius_eq y0 x]
  unfold edgeCoordinate
  rw [mul_div_cancel_left₀ _ (profileRadius_pos y0 0).ne', Real.log_exp]
  ring

theorem radialSource_weight (C : ℝ) (d : TailData) (y0 η : ℝ) {R : ℝ} (hR : 0 < R) :
    R ^ 2 * radialSource C d y0 η R =
      radialFlatDensity 4 6 (fun x => primitiveCoefficient C d y0 (η, x))
        (profileRadius y0 0) R := by
  rw [radialSource, profileSource_factorization]
  simp only [radialFlatDensity, FlatPrimitive.integrand, primitiveCoefficient,
    profileRadius_edgeCoordinate y0 hR]
  by_cases hx : edgeCoordinate (profileRadius y0 0) R = 0
  · simp [hx]
  · field_simp [hR.ne', hx]

theorem radialSource_weight_integrable (C : ℝ) (d : TailData) (y0 η : ℝ)
    {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun u => u ^ 2 * radialSource C d y0 η u) (Ioi R) := by
  apply (radialFlatDensity_integrable (by norm_num : (0 : ℝ) < 4)
    (profileRadius_pos y0 0) hR 6
    ((ParametricFlatFactor.coefficient_slice_contDiff
      (primitiveCoefficient_contDiff C d y0) η).continuous)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (radialSource_weight C d y0 η (hR.trans hu)).symm

theorem radialStress_eq_primitive (C : ℝ) (d : TailData) (y0 η : ℝ)
    {R : ℝ} (hR : 0 < R) :
    radialStress C d y0 η R =
      ParametricFlatFactor.primitive 4 6 (primitiveCoefficient C d y0)
        (η, edgeCoordinate (profileRadius y0 0) R) / R ^ 2 := by
  unfold radialStress backwardStress
  congr 1
  unfold ParametricFlatFactor.primitive
  rw [← radialFlatDensity_integral (by norm_num : (0 : ℝ) < 4)
    (profileRadius_pos y0 0) hR 6
    ((ParametricFlatFactor.coefficient_slice_contDiff
      (primitiveCoefficient_contDiff C d y0) η).continuous)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact radialSource_weight C d y0 η (hR.trans hu)

theorem profileStress_eq_primitive (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) :
    profileStress C d y0 y =
      ParametricFlatFactor.primitive 4 6 (primitiveCoefficient C d y0) y /
        profileRadius y0 y.2 ^ 2 := by
  rw [profileStress, radialStress_eq_primitive C d y0 y.1 (profileRadius_pos y0 y.2),
    edgeCoordinate_profileRadius]

theorem profileStress_factorization (C : ℝ) (d : TailData) (y0 : ℝ) (y : ℝ × ℝ) :
    profileStress C d y0 y = (FlatCutoff.edge 4 y.2 / y.2 ^ 3) * stressFactor C d y0 y := by
  rw [profileStress_eq_primitive, ParametricFlatFactor.primitive_eq_scale_mul_factor]
  unfold FlatPrimitive.scale stressFactor
  by_cases hx : y.2 = 0
  · simp [hx]
  · field_simp [hx, (profileRadius_pos y0 y.2).ne']

theorem profileStress_contDiff (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiff ℝ ∞ (profileStress C d y0) := by
  have he : profileStress C d y0 = EdgeWeightJets.weighted 4 3 (stressFactor C d y0) :=
    funext (profileStress_factorization C d y0)
  rw [he]
  exact EdgeWeightJets.weighted_contDiff (by norm_num) 3 (stressFactor_contDiff C d y0)

theorem profileStress_zero_of_nonpos (C : ℝ) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hy : y.2 ≤ 0) : profileStress C d y0 y = 0 := by
  rw [profileStress_factorization, FlatCutoff.edge_of_nonpos 4 hy, zero_div, zero_mul]

theorem profileStress_edge_jets (C : ℝ) (d : TailData) (y0 η : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (profileStress C d y0) (η, 0) = 0 := by
  have he : profileStress C d y0 = EdgeWeightJets.weighted 4 3 (stressFactor C d y0) :=
    funext (profileStress_factorization C d y0)
  rw [he]
  exact EdgeWeightJets.weighted_iteratedFDeriv_zero (by norm_num) 3
    (stressFactor_contDiff C d y0) n η

/-- All full joint derivative tensors, uniformly including both parameter endpoints. -/
theorem profileStress_jets (C : ℝ) (d : TailData) (y0 : ℝ) (n : ℕ)
    {b : ℝ} (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ η ∈ Icc (-1 : ℝ) 1,
      ∀ x : ℝ, 0 < x → x ≤ b →
        ‖iteratedFDeriv ℝ i (profileStress C d y0) (η, x)‖ ≤
          M * FlatCutoff.edge 4 x / x ^ N := by
  have he : profileStress C d y0 = EdgeWeightJets.weighted 4 3 (stressFactor C d y0) :=
    funext (profileStress_factorization C d y0)
  rw [he]
  exact EdgeWeightJets.edge_mul_iteratedFDeriv_bound (by norm_num) 3
    (stressFactor_contDiff C d y0) isCompact_Icc n hb

/-! ## The actual `(X,η)` profile coordinates -/

/-- X chart, given by `(w.2, y0 + 3 - Real.log w.1)`. -/
noncomputable def xChart (y0 : ℝ) (w : ℝ × ℝ) : ℝ × ℝ :=
  (w.2, y0 + 3 - Real.log w.1)

/-- Stress X, given by `profileStress C d y0 (xChart y0 w)`. -/
noncomputable def stressX (C : ℝ) (d : TailData) (y0 : ℝ) (w : ℝ × ℝ) : ℝ :=
  profileStress C d y0 (xChart y0 w)

theorem xChart_contDiffOn (y0 : ℝ) :
    ContDiffOn ℝ ∞ (xChart y0) {w : ℝ × ℝ | 0 < w.1} := by
  intro w hw
  exact (contDiffAt_snd.prodMk (contDiffAt_const.sub
    (contDiffAt_fst.log (show w.1 ≠ 0 from ne_of_gt hw)))).contDiffWithinAt

theorem stressX_contDiffOn (C : ℝ) (d : TailData) (y0 : ℝ) :
    ContDiffOn ℝ ∞ (stressX C d y0) {w : ℝ × ℝ | 0 < w.1} :=
  (profileStress_contDiff C d y0).comp_contDiffOn (xChart_contDiffOn y0)

theorem compact_jets_bound_on {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {S K : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) (hK : IsCompact K) (hKS : K ⊆ S) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb : ∀ i : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ A := by
    intro i
    have hc : ContinuousOn (iteratedFDeriv ℝ i f) S := by
      intro x hx
      have hi : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ i f) x :=
        (hf.contDiffAt (hS.mem_nhds hx)).iteratedFDeriv_right
          (WithTop.coe_le_coe.mpr le_top)
      exact hi.continuousAt.continuousWithinAt
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hc.mono hKS)
    exact ⟨max A 0, le_max_right _ _, fun x hx => (hA x hx).trans (le_max_left _ _)⟩
  choose A hA hbound using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n + 1), A i, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hA i))
  · intro i hi x hx
    have hs := Finset.single_le_sum (fun j _ => hA j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact (hbound i x hx).trans (by linarith)

theorem stressX_jets (C : ℝ) (d : TailData) (y0 : ℝ) (n : ℕ)
    {b : ℝ} (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ X ∈ Ico (Real.exp (y0 + 3 - b)) (Real.exp (y0 + 3)),
      ∀ η ∈ Icc (-1 : ℝ) 1,
        ‖iteratedFDeriv ℝ n (stressX C d y0) (X, η)‖ ≤
          M * FlatCutoff.edge 4 (y0 + 3 - Real.log X) / (y0 + 3 - Real.log X) ^ N := by
  let K := Icc (Real.exp (y0 + 3 - b)) (Real.exp (y0 + 3)) ×ˢ Icc (-1 : ℝ) 1
  have hS : IsOpen {w : ℝ × ℝ | 0 < w.1} := isOpen_lt continuous_const continuous_fst
  have hKS : K ⊆ {w : ℝ × ℝ | 0 < w.1} := fun w hw =>
    (Real.exp_pos _).trans_le hw.1.1
  obtain ⟨D, hD, hchart⟩ := compact_jets_bound_on hS (xChart_contDiffOn y0)
    (isCompact_Icc.prod isCompact_Icc) hKS n
  obtain ⟨A, hA, N, hprof⟩ := profileStress_jets C d y0 n hb
  refine ⟨(n.factorial : ℝ) * A * D ^ n, by positivity, N, ?_⟩
  intro X hX η hη
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX.1
  have hl := Real.log_le_log (Real.exp_pos (y0 + 3 - b)) hX.1
  have hu := Real.log_lt_log hXp hX.2
  rw [Real.log_exp] at hl hu
  have hδ : 0 < y0 + 3 - Real.log X := by linarith
  have hδb : y0 + 3 - Real.log X ≤ b := by linarith
  have hc := norm_iteratedFDerivWithin_comp_le (profileStress_contDiff C d y0).contDiffOn
    (xChart_contDiffOn y0) (EdgeWeightJets.nat_le_infty n) uniqueDiffOn_univ hS.uniqueDiffOn
    (mapsTo_univ _ _) (show (X, η) ∈ {w : ℝ × ℝ | 0 < w.1} from hXp)
    (C := A * FlatCutoff.edge 4 (y0 + 3 - Real.log X) / (y0 + 3 - Real.log X) ^ N)
    (D := D)
    (by
      intro i hi
      rw [iteratedFDerivWithin_univ]
      exact hprof i hi η hη _ hδ hδb)
    (by
      intro i hi hin
      rw [iteratedFDerivWithin_of_isOpen i hS hXp]
      exact (hchart i hin (X, η) ⟨⟨hX.1, hX.2.le⟩, hη⟩).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  rw [iteratedFDerivWithin_of_isOpen n hS hXp] at hc
  change ‖iteratedFDeriv ℝ n (stressX C d y0) (X, η)‖ ≤ _ at hc
  convert! hc using 1
  ring

/-- The two logarithmic Gaussian factors specified in (20). -/
noncomputable def zeta (cL a y0 X : ℝ) : ℝ :=
  FlatCutoff.edge cL (Real.log (X / a)) * FlatCutoff.edge 4 (y0 + 3 - Real.log X)

/-- Edge distance, given by `min 1 (min (Real.log (X / a)) (y0 + 3 - Real.log X))`. -/
noncomputable def edgeDistance (a y0 X : ℝ) : ℝ :=
  min 1 (min (Real.log (X / a)) (y0 + 3 - Real.log X))

theorem stressX_zero_outside (C : ℝ) (d : TailData) (y0 : ℝ)
    {X : ℝ} (hX : Real.exp (y0 + 3) ≤ X) (η : ℝ) : stressX C d y0 (X, η) = 0 := by
  have hl := Real.log_le_log (Real.exp_pos (y0 + 3)) hX
  rw [Real.log_exp] at hl
  exact profileStress_zero_of_nonpos C d y0 (by dsimp [xChart]; linarith)

theorem edge_mono_positive {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (hxy : x ≤ y) :
    FlatCutoff.edge c x ≤ FlatCutoff.edge c y := by
  rw [FlatCutoff.edge_of_pos c hx, FlatCutoff.edge_of_pos c (hx.trans_le hxy)]
  apply Real.exp_le_exp.mpr
  simp only [neg_div]
  apply neg_le_neg
  exact div_le_div_of_nonneg_left hc (sq_pos_of_pos hx) (by nlinarith)

/-- The full weight from (20), with the lesser of the two log distances and one.
The only geometric condition is that the closed outer collar avoids the inner edge. -/
theorem stressX_weighted_jets (C : ℝ) (d : TailData) (y0 : ℝ) (n : ℕ)
    {b a cL : ℝ} (hb : 0 < b) (ha : 0 < a) (hcL : 0 < cL)
    (hcollar : a < Real.exp (y0 + 3 - b)) :
    ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ X ∈ Ico (Real.exp (y0 + 3 - b)) (Real.exp (y0 + 3)),
      ∀ η ∈ Icc (-1 : ℝ) 1,
        ‖iteratedFDeriv ℝ n (stressX C d y0) (X, η)‖ ≤
          M * zeta cL a y0 X / edgeDistance a y0 X ^ N := by
  let l := Real.log (Real.exp (y0 + 3 - b) / a)
  have hl : 0 < l := Real.log_pos ((one_lt_div ha).mpr hcollar)
  let e := FlatCutoff.edge cL l
  have he : 0 < e := FlatCutoff.edge_pos cL hl
  obtain ⟨A, hA, N, hbnd⟩ := stressX_jets C d y0 n hb
  refine ⟨A / e, div_pos hA he, N, ?_⟩
  intro X hX η hη
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX.1
  have hlog : l ≤ Real.log (X / a) :=
    Real.log_le_log (div_pos (Real.exp_pos _) ha) (div_le_div_of_nonneg_right hX.1 ha.le)
  have hi : 0 < Real.log (X / a) := hl.trans_le hlog
  have hu := Real.log_lt_log hXp hX.2
  rw [Real.log_exp] at hu
  have ho : 0 < y0 + 3 - Real.log X := by linarith
  have hd : 0 < edgeDistance a y0 X := lt_min zero_lt_one (lt_min hi ho)
  have hdo : edgeDistance a y0 X ≤ y0 + 3 - Real.log X :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hinner : e ≤ FlatCutoff.edge cL (Real.log (X / a)) := edge_mono_positive hcL.le hl hlog
  have hw : A * FlatCutoff.edge 4 (y0 + 3 - Real.log X) ≤ (A / e) * zeta cL a y0 X := by
    unfold zeta
    have hm : A ≤ (A / e) * FlatCutoff.edge cL (Real.log (X / a)) := by
      calc
        A = (A / e) * e := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hinner (div_nonneg hA.le he.le)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm
      (FlatCutoff.edge_nonneg 4 (y0 + 3 - Real.log X))
  calc
    _ ≤ A * FlatCutoff.edge 4 (y0 + 3 - Real.log X) / (y0 + 3 - Real.log X) ^ N :=
      hbnd X hX η hη
    _ ≤ ((A / e) * zeta cL a y0 X) / (y0 + 3 - Real.log X) ^ N :=
      div_le_div_of_nonneg_right hw (pow_nonneg ho.le N)
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (div_nonneg hA.le he.le)
        (mul_nonneg (FlatCutoff.edge_nonneg _ _) (FlatCutoff.edge_nonneg _ _)))
      (pow_pos hd N) (pow_le_pow_left₀ hd.le hdo N)

/-! ## Literal axial derivatives in physical coordinates -/

open SimilarityProfile

/-- Physical point: an abbreviation for `SimilarityProfile.PhysicalPoint`. -/
abbrev PhysicalPoint := SimilarityProfile.PhysicalPoint

/-- Physical chi, given by `q d.h p ^ (-CoordinateAlgebra.D d.h) * profileChi d (eta d.h p)`. -/
noncomputable def physicalChi (d : TailData) (p : PhysicalPoint) : ℝ :=
  q d.h p ^ (-CoordinateAlgebra.D d.h) * profileChi d (eta d.h p)

theorem physicalChi_eq_logScale (d : TailData) {p : PhysicalPoint} (ht : p.1 < 1) :
    physicalChi d p = TerminalPressure.logScaleDerivative d.h p := by
  rw [TerminalPressure.logScaleDerivative_eq (q_pos d.h_pos d.h_lt_half ht)]
  unfold physicalChi profileChi
  rw [profileL_eq d (eta_sq_lt_one d.h_pos d.h_lt_half ht).le,
    Real.rpow_neg (q_pos d.h_pos d.h_lt_half ht).le]
  ring

theorem physicalChi_hasDerivAt_z (d : TailData) {p : PhysicalPoint} (ht : p.1 < 1) :
    HasDerivAt (fun z => physicalChi d (p.1, (p.2.1, z)))
      (-(q d.h p ^ (-2 * CoordinateAlgebra.D d.h) * beta d (eta d.h p))) p.2.2 := by
  have hq := q_pos d.h_pos d.h_lt_half ht
  have hχ := ((profileChi_contDiff d).differentiable (by simp) (eta d.h p)).hasDerivAt.comp p.2.2
    (eta_hasDerivAt_z d.h_pos d.h_lt_half ht)
  have hm := ((q_hasDerivAt_z d.h_pos d.h_lt_half ht).rpow_const
    (p := -CoordinateAlgebra.D d.h) (Or.inl hq.ne')).mul hχ
  apply hm.congr_deriv
  have he := CoordinateAlgebra.axial_chain_coefficient hq (-CoordinateAlgebra.D d.h)
    d.h (eta d.h p) 0 (profileChi d (eta d.h p)) 0 (deriv (profileChi d) (eta d.h p))
  simp only [zero_mul, zero_add] at he
  calc
    _ = q d.h p ^ (-CoordinateAlgebra.D d.h - CoordinateAlgebra.D d.h) *
        CoordinateAlgebra.axialCoeff (-CoordinateAlgebra.D d.h) d.h (eta d.h p)
          0 (profileChi d (eta d.h p)) 0 (deriv (profileChi d) (eta d.h p)) := by
      simpa only [Function.comp_apply, Prod.eta, mul_comm, mul_left_comm, mul_assoc] using he
    _ = _ := by
      rw [show -CoordinateAlgebra.D d.h - CoordinateAlgebra.D d.h =
        -2 * CoordinateAlgebra.D d.h by ring]
      unfold CoordinateAlgebra.axialCoeff beta CoordinateAlgebra.d
      rw [profileL_eq d (eta_sq_lt_one d.h_pos d.h_lt_half ht).le]
      ring

/-- Physical taper, given by `tailShape d (Real.log (X d.h p) - y0)`. -/
noncomputable def physicalTaper (d : TailData) (y0 : ℝ) (p : PhysicalPoint) : ℝ :=
  tailShape d (Real.log (X d.h p) - y0)

theorem physicalTaper_hasDerivAt_z (d : TailData) (y0 : ℝ) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1) :
    HasDerivAt (fun z => physicalTaper d y0 (p.1, (p.2.1, z)))
      (-physicalChi d p * tailShapeDeriv d (Real.log (X d.h p) - y0)) p.2.2 := by
  have hh := (tailShape_hasDerivAt d (Real.log (X d.h p) - y0)).comp p.2.2
    ((TerminalPressure.logX_hasDerivAt_z d.h_pos d.h_lt_half ht hs).sub_const y0)
  apply hh.congr_deriv
  rw [physicalChi_eq_logScale d ht]
  ring

theorem physicalTaper_second_z (d : TailData) (y0 : ℝ) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1) :
    deriv (deriv (fun z => physicalTaper d y0 (p.1, (p.2.1, z)))) p.2.2 =
      q d.h p ^ (-2 * CoordinateAlgebra.D d.h) *
        (profileChi d (eta d.h p) ^ 2 * deriv (tailShapeDeriv d) (Real.log (X d.h p) - y0) +
          beta d (eta d.h p) * tailShapeDeriv d (Real.log (X d.h p) - y0)) := by
  have he : deriv (fun z => physicalTaper d y0 (p.1, (p.2.1, z))) =
      fun z => -physicalChi d (p.1, (p.2.1, z)) *
        tailShapeDeriv d (Real.log (X d.h (p.1, (p.2.1, z))) - y0) := by
    funext z
    exact (physicalTaper_hasDerivAt_z d y0 (p := (p.1, (p.2.1, z))) ht hs).deriv
  rw [he]
  have hh := ((tailShapeDeriv_contDiff d).differentiable (by simp)
    (Real.log (X d.h p) - y0)).hasDerivAt.comp p.2.2
      ((TerminalPressure.logX_hasDerivAt_z d.h_pos d.h_lt_half ht hs).sub_const y0)
  have hd := (physicalChi_hasDerivAt_z d ht).fun_neg.fun_mul hh
  simp only [Function.comp_def, Prod.eta] at hd
  rw [hd.deriv, ← physicalChi_eq_logScale d ht]
  have hsq : physicalChi d p ^ 2 = q d.h p ^ (-2 * CoordinateAlgebra.D d.h) *
      profileChi d (eta d.h p) ^ 2 := by
    unfold physicalChi
    rw [mul_pow, pow_two (q d.h p ^ _), ← Real.rpow_add (q_pos d.h_pos d.h_lt_half ht)]
    rw [show -CoordinateAlgebra.D d.h + -CoordinateAlgebra.D d.h =
      -2 * CoordinateAlgebra.D d.h by ring]
  calc
    _ = q d.h p ^ (-2 * CoordinateAlgebra.D d.h) * beta d (eta d.h p) *
        tailShapeDeriv d (Real.log (X d.h p) - y0) +
        physicalChi d p ^ 2 * deriv (tailShapeDeriv d) (Real.log (X d.h p) - y0) := by ring
    _ = _ := by rw [hsq]; ring

theorem profileS_xChart (y0 : ℝ) {w : ℝ × ℝ} (hX : 0 < w.1) :
    profileS y0 (xChart y0 w).2 = w.1 := by
  unfold profileS xChart
  rw [show y0 + 3 - (y0 + 3 - Real.log w.1) = Real.log w.1 by ring, Real.exp_log hX]

theorem physicalHeat_eq_profileCarrier (C : ℝ) (d : TailData) (y0 : ℝ)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    physicalHeat C (1 + d.h) p =
      q d.h p ^ (-CoordinateAlgebra.A d.h) *
        profileCarrier C d y0 (xChart y0 (inner d.h p)) := by
  have hq := q_pos d.h_pos d.h_lt_half ht
  have hX : 0 < X d.h p := div_pos hs hq
  have hη := eta_sq_lt_one d.h_pos d.h_lt_half ht
  have hS := profileS_xChart y0 (w := SimilarityProfile.inner d.h p) hX
  have hZ : profileZ y0 (xChart y0 (inner d.h p)) = 2 * (1 - p.1) / p.2.1 := by
    unfold profileZ
    rw [hS]
    exact PhysicalHeatCoordinates.heat_argument d.h_pos d.h_lt_half ht hs
  have hz : 0 ≤ profileZ y0 (xChart y0 (inner d.h p)) := by
    rw [hZ]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.le)) hs.le
  have ha : RadialHeatProfile.spatialExponent (1 + d.h) = -CoordinateAlgebra.A d.h := by
    unfold RadialHeatProfile.spatialExponent CoordinateAlgebra.A
    ring
  rw [profileCarrier, HeatProfileExtension.extension_eq_profile _ hz, hZ, hS, ha]
  unfold physicalHeat RadialHeatProfile.spatialProfile
  rw [ha]
  have hp : q d.h p ^ (-CoordinateAlgebra.A d.h) *
      X d.h p ^ (-CoordinateAlgebra.A d.h) = p.2.1 ^ (-CoordinateAlgebra.A d.h) := by
    unfold X
    rw [Real.div_rpow hs.le hq.le]
    field_simp [(Real.rpow_pos_of_pos hq (-CoordinateAlgebra.A d.h)).ne']
  calc
    _ = C * (p.2.1 ^ (-CoordinateAlgebra.A d.h) *
        RadialHeatProfile.profile (1 + d.h) (2 * (1 - p.1) / p.2.1)) := rfl
    _ = _ := by rw [← hp]; dsimp only [SimilarityProfile.inner]; ring

/-- Literal physical angular velocity on the switched terminal collar. -/
noncomputable def physicalAngular (C : ℝ) (d : TailData) (y0 : ℝ) (p : PhysicalPoint) : ℝ :=
  physicalHeat C (1 + d.h) p * physicalTaper d y0 p

/-- Literal negative second axial derivative; no independent jet is supplied. -/
noncomputable def physicalSource (C : ℝ) (d : TailData) (y0 : ℝ) (p : PhysicalPoint) : ℝ :=
  -deriv (deriv (fun z => physicalAngular C d y0 (p.1, (p.2.1, z)))) p.2.2

theorem physicalSource_eq (C : ℝ) (d : TailData) (y0 : ℝ) {p : PhysicalPoint}
    :
    physicalSource C d y0 p =
      -physicalHeat C (1 + d.h) p *
        deriv (deriv (fun z => physicalTaper d y0 (p.1, (p.2.1, z)))) p.2.2 := by
  change -deriv (deriv (fun z => physicalHeat C (1 + d.h) p *
    physicalTaper d y0 (p.1, (p.2.1, z)))) p.2.2 = _
  rw [deriv_const_mul_field', deriv_const_mul_field]
  ring

/-- The residual order is `q^(-A-1+2h)`, before one radial integration. -/
theorem physicalSource_scaled (C : ℝ) (d : TailData) (y0 : ℝ) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1) :
    physicalSource C d y0 p =
      q d.h p ^ (-CoordinateAlgebra.A d.h - 1 + 2 * d.h) *
        profileSource C d y0 (xChart y0 (inner d.h p)) := by
  rw [physicalSource_eq C d y0, physicalTaper_second_z d y0 ht hs,
    physicalHeat_eq_profileCarrier C d y0 ht hs]
  have he : -CoordinateAlgebra.A d.h - 1 + 2 * d.h =
      -CoordinateAlgebra.A d.h + (-2 * CoordinateAlgebra.D d.h) := by
    unfold CoordinateAlgebra.D
    ring
  rw [he, Real.rpow_add (q_pos d.h_pos d.h_lt_half ht)]
  simp only [profileSource, xChart, SimilarityProfile.inner]
  rw [show 3 - (y0 + 3 - Real.log (X d.h p)) = Real.log (X d.h p) - y0 by ring]
  ring

theorem profileRadius_xChart (y0 : ℝ) {w : ℝ × ℝ} (hX : 0 < w.1) :
    profileRadius y0 (xChart y0 w).2 = Real.sqrt (2 * w.1) := by
  have hh := profileRadius_square y0 (xChart y0 w).2
  rw [profileS_xChart y0 hX] at hh
  have hs := Real.sq_sqrt (show 0 ≤ 2 * w.1 by positivity)
  nlinarith [profileRadius_pos y0 (xChart y0 w).2, Real.sqrt_nonneg (2 * w.1)]

theorem edgeCoordinate_eq_log (y0 : ℝ) {R : ℝ} (hR : 0 < R) :
    edgeCoordinate (profileRadius y0 0) R = y0 + 3 - Real.log (R ^ 2 / 2) := by
  have hX : 0 < R ^ 2 / 2 := by positivity
  have hr := profileRadius_xChart y0 (w := (R ^ 2 / 2, (0 : ℝ))) hX
  have hs : Real.sqrt (2 * (R ^ 2 / 2)) = R := by
    rw [show 2 * (R ^ 2 / 2) = R ^ 2 by ring, Real.sqrt_sq hR.le]
  rw [hs] at hr
  calc
    _ = edgeCoordinate (profileRadius y0 0)
        (profileRadius y0 (xChart y0 (R ^ 2 / 2, (0 : ℝ))).2) := by rw [hr]
    _ = _ := edgeCoordinate_profileRadius y0 _

theorem stressX_eq_radialStress (C : ℝ) (d : TailData) (y0 : ℝ)
    {w : ℝ × ℝ} (hX : 0 < w.1) :
    stressX C d y0 w = radialStress C d y0 w.2 (Real.sqrt (2 * w.1)) := by
  unfold stressX profileStress
  rw [profileRadius_xChart y0 hX]
  rfl

/-- Physical scale, given by `q d.h (t, (0, z))`. -/
noncomputable def physicalScale (d : TailData) (t z : ℝ) : ℝ := q d.h (t, (0, z))
/-- Physical eta, given by `eta d.h (t, (0, z))`. -/
noncomputable def physicalEta (d : TailData) (t z : ℝ) : ℝ := eta d.h (t, (0, z))

theorem physicalScale_pos (d : TailData) {t z : ℝ} (ht : t < 1) :
    0 < physicalScale d t z := q_pos d.h_pos d.h_lt_half ht

theorem scaledRadius_identity {Q R : ℝ} (hQ : 0 < Q) :
    (R / Real.sqrt Q) ^ 2 / 2 = (R ^ 2 / 2) / Q := by
  rw [div_pow, Real.sq_sqrt hQ.le]
  ring

theorem physicalSource_radial_scaled (C : ℝ) (d : TailData) (y0 : ℝ)
    {t r z : ℝ} (ht : t < 1) (hr : 0 < r) :
    physicalSource C d y0 (radiusPoint t r z) =
      physicalScale d t z ^ (-CoordinateAlgebra.A d.h - 1 + 2 * d.h) *
        radialSource C d y0 (physicalEta d t z) (r / Real.sqrt (physicalScale d t z)) := by
  rw [physicalSource_scaled C d y0 ht (by dsimp [radiusPoint]; positivity)]
  unfold radialSource
  rw [edgeCoordinate_eq_log y0 (div_pos hr (Real.sqrt_pos.mpr (physicalScale_pos d ht))),
    scaledRadius_identity (physicalScale_pos d ht)]
  rfl

/-- Backward radial integration contributes exactly one half power of `q`. -/
theorem backwardStress_scale (b : ℝ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) (g : ℝ → ℝ) :
    backwardStress (fun u => Q ^ b * g (u / Real.sqrt Q)) r =
      Q ^ (b + 1 / 2) * backwardStress g (r / Real.sqrt Q) := by
  have hf : (fun u => u ^ 2 * (Q ^ b * g (u / Real.sqrt Q))) =
      fun u => (Q * Q ^ b) * ((u / Real.sqrt Q) ^ 2 * g (u / Real.sqrt Q)) := by
    funext u
    rw [div_pow, Real.sq_sqrt hQ.le]
    field_simp [hQ.ne']
  unfold backwardStress
  rw [hf, integral_const_mul]
  have hs := integral_comp_mul_right_Ioi (fun R => R ^ 2 * g R) r
    (inv_pos.mpr (Real.sqrt_pos.mpr hQ))
  simp only [inv_inv, smul_eq_mul, ← div_eq_mul_inv] at hs
  rw [hs]
  have hp : Q * Q ^ b * Real.sqrt Q = Q * Q ^ (b + 1 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_add hQ]
    ring
  rw [← mul_assoc, hp, div_pow, Real.sq_sqrt hQ.le]
  field_simp [hQ.ne', hr.ne']

/-- Physical stress, given by `backwardStress (fun u => physicalSource C d y0 (radiusPoint t u
z)) r`. -/
noncomputable def physicalStress (C : ℝ) (d : TailData) (y0 t z r : ℝ) : ℝ :=
  backwardStress (fun u => physicalSource C d y0 (radiusPoint t u z)) r

theorem physicalStress_scaled_radial (C : ℝ) (d : TailData) (y0 : ℝ)
    {t r z : ℝ} (ht : t < 1) (hr : 0 < r) :
    physicalStress C d y0 t z r =
      physicalScale d t z ^ (-CoordinateAlgebra.A d.h - 1 / 2 + 2 * d.h) *
        radialStress C d y0 (physicalEta d t z) (r / Real.sqrt (physicalScale d t z)) := by
  have hi : physicalStress C d y0 t z r =
      backwardStress (fun u => physicalScale d t z ^ (-CoordinateAlgebra.A d.h - 1 + 2 * d.h) *
        radialSource C d y0 (physicalEta d t z) (u / Real.sqrt (physicalScale d t z))) r := by
    unfold physicalStress backwardStress
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [physicalSource_radial_scaled C d y0 ht (hr.trans hu)]
  rw [hi, backwardStress_scale _ (physicalScale_pos d ht) hr]
  rw [show -CoordinateAlgebra.A d.h - 1 + 2 * d.h + 1 / 2 =
    -CoordinateAlgebra.A d.h - 1 / 2 + 2 * d.h by ring]
  rfl

/-- Identification of the actual physical backward primitive with the first-order
profile coefficient, using the manuscript's exact tensor power. -/
theorem physicalStress_scaled (C : ℝ) (d : TailData) (y0 : ℝ)
    {t r z : ℝ} (ht : t < 1) (hr : 0 < r) :
    physicalStress C d y0 t z r =
      physicalScale d t z ^ (-CoordinateAlgebra.A d.h - 1 / 2 + 2 * d.h) *
        stressX C d y0 ((r ^ 2 / 2) / physicalScale d t z, physicalEta d t z) := by
  have hX : 0 < (r ^ 2 / 2) / physicalScale d t z :=
    div_pos (by positivity) (physicalScale_pos d ht)
  rw [physicalStress_scaled_radial C d y0 ht hr,
    stressX_eq_radialStress C d y0 hX]
  have he : Real.sqrt (2 * ((r ^ 2 / 2) / physicalScale d t z)) =
      r / Real.sqrt (physicalScale d t z) := by
    rw [← scaledRadius_identity (physicalScale_pos d ht)]
    rw [show 2 * ((r / Real.sqrt (physicalScale d t z)) ^ 2 / 2) =
      (r / Real.sqrt (physicalScale d t z)) ^ 2 by ring]
    exact Real.sqrt_sq (div_pos hr (Real.sqrt_pos.mpr (physicalScale_pos d ht))).le
  rw [he]

/-- Global moment closure is supplied by the separate renormalized-moment and
slow-order moment theorems.  Only agreement on the exterior ray is needed here. -/
theorem forward_eq_physicalStress (C : ℝ) (d : TailData) (y0 t z : ℝ)
    {F : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hi : IntegrableOn (fun u => u ^ 2 * F u) (Ioi 0))
    (hzero : (∫ u in Ioi (0 : ℝ), u ^ 2 * F u) = 0)
    (hmatch : ∀ u, r ≤ u → F u = physicalSource C d y0 (radiusPoint t u z)) :
    forwardStress F r = physicalStress C d y0 t z r := by
  rw [(forward_eq_backward_iff hr hi).mpr hzero]
  unfold physicalStress backwardStress
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [hmatch u hu.le]

theorem stressX_edge_jets (C : ℝ) (d : TailData) (y0 η : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (stressX C d y0) (Real.exp (y0 + 3), η) = 0 := by
  let w : ℝ × ℝ := (Real.exp (y0 + 3), η)
  have hS : IsOpen {w : ℝ × ℝ | 0 < w.1} := isOpen_lt continuous_const continuous_fst
  have hw : w ∈ {w : ℝ × ℝ | 0 < w.1} := Real.exp_pos _
  obtain ⟨D, hD, hchart⟩ := compact_jets_bound_on hS (xChart_contDiffOn y0)
    (isCompact_singleton (x := w)) (singleton_subset_iff.mpr hw) n
  have he : xChart y0 w = (η, 0) := by simp [xChart, w]
  have hc := norm_iteratedFDerivWithin_comp_le (profileStress_contDiff C d y0).contDiffOn
    (xChart_contDiffOn y0) (EdgeWeightJets.nat_le_infty n) uniqueDiffOn_univ hS.uniqueDiffOn
    (mapsTo_univ _ _) hw (C := 0) (D := D)
    (by
      intro i hi
      rw [iteratedFDerivWithin_univ, he, profileStress_edge_jets, norm_zero])
    (by
      intro i hi hin
      rw [iteratedFDerivWithin_of_isOpen i hS hw]
      exact (hchart i hin w (mem_singleton w)).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  rw [iteratedFDerivWithin_of_isOpen n hS hw] at hc
  apply norm_le_zero_iff.mp
  simp only [mul_zero, zero_mul] at hc
  exact hc

theorem physicalSource_weight_integrable (C : ℝ) (d : TailData) (y0 : ℝ)
    {t r z : ℝ} (ht : t < 1) (hr : 0 < r) :
    IntegrableOn (fun u => u ^ 2 * physicalSource C d y0 (radiusPoint t u z)) (Ioi r) := by
  let Q := physicalScale d t z
  let g : ℝ → ℝ := fun R => R ^ 2 * radialSource C d y0 (physicalEta d t z) R
  have hQ : 0 < Q := physicalScale_pos d ht
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hg : IntegrableOn g (Ioi (r / Real.sqrt Q)) :=
    radialSource_weight_integrable C d y0 (physicalEta d t z) (div_pos hr hs)
  have hi : IntegrableOn (fun u => g (u / Real.sqrt Q)) (Ioi r) := by
    have hh := (integrableOn_Ioi_comp_mul_right_iff g r (inv_pos.mpr hs)).mpr
      (by simpa only [div_eq_mul_inv] using hg)
    simpa only [div_eq_mul_inv] using hh
  apply (hi.const_mul (Q * Q ^ (-CoordinateAlgebra.A d.h - 1 + 2 * d.h))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [physicalSource_radial_scaled C d y0 ht (hr.trans hu)]
  dsimp only [g]
  change Q * Q ^ (-CoordinateAlgebra.A d.h - 1 + 2 * d.h) *
      ((u / Real.sqrt Q) ^ 2 * radialSource C d y0 (physicalEta d t z) (u / Real.sqrt Q)) =
    u ^ 2 * (Q ^ (-CoordinateAlgebra.A d.h - 1 + 2 * d.h) *
      radialSource C d y0 (physicalEta d t z) (u / Real.sqrt Q))
  rw [div_pow, Real.sq_sqrt hQ.le]
  field_simp [hQ.ne']

/-- The literal terminal velocity is the actual fully switched heat edit from
the outgoing schedule, with its original amplitude and log origin. -/
theorem editedAngular_eq_physicalAngular (d : TailData) {K : ℝ} (hK : 0 < K)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 ≤ Real.log (X d.h p / K) + 1 / 5) :
    PhysicalHeatCoordinates.editedAngular d K p =
      physicalAngular (PhysicalHeatCoordinates.normalization d K) d (Real.log K - 1 / 5) p := by
  rw [PhysicalHeatCoordinates.editedAngular_eq_heat d hK d.h_lt_half ht hs hfull]
  unfold physicalAngular physicalTaper flattening PhysicalHeatCoordinates.shape
  congr 2
  ring

theorem forward_eq_radialStress (C : ℝ) (d : TailData) (y0 η : ℝ)
    {F : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hi : IntegrableOn (fun u => u ^ 2 * F u) (Ioi 0))
    (hzero : (∫ u in Ioi (0 : ℝ), u ^ 2 * F u) = 0)
    (hmatch : ∀ u, R ≤ u → F u = radialSource C d y0 η u) :
    forwardStress F R = radialStress C d y0 η R := by
  rw [(forward_eq_backward_iff hR hi).mpr hzero]
  unfold radialStress backwardStress
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [hmatch u hu.le]

end NavierStokes.SlowFirstOrderEdge
