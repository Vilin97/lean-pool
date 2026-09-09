/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ChartScales
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisymmetricFields
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhaseCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.CoordinateAlgebra
public import LeanPool.NavierStokesAndEuler.NavierStokes.PolarCharts
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Physical derivatives of the native graph

The graph, the integer covering, and the rounded carrier here are the actual
ones of Definition 8.1 and equation (26). Bounds use actual Fréchet jets.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PhysicalGraphBounds

open Set Function
open ProblemStatement
open scoped ContDiff Topology BigOperators

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ

/-- Radial direction, given by `(1, 1 - Real.sqrt 2)`. -/
noncomputable def radialDirection : Plane := (1, 1 - Real.sqrt 2)
/-- Time direction, given by `(Real.sqrt 2 - 1, 1)`. -/
noncomputable def timeDirection : Plane := (Real.sqrt 2 - 1, 1)

theorem cover_radialDirection :
    SlotGeometry.cover radialDirection = ChartScales.Lambda • radialDirection := by
  ext <;> simp [SlotGeometry.cover_apply, radialDirection, ChartScales.Lambda] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem cover_timeDirection :
    SlotGeometry.cover timeDirection = ChartScales.Tg • timeDirection := by
  ext <;> simp [SlotGeometry.cover_apply, timeDirection, ChartScales.Tg, SlotColoring.coverGrowth]
      <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem cover_pow_radialDirection (i : ℕ) :
    (SlotGeometry.cover ^ i) radialDirection = ChartScales.Lambda ^ i • radialDirection := by
  induction i with
  | zero => simp
  | succ i hi =>
      rw [pow_succ', _root_.mul_apply_eq_comp, hi, map_smul, cover_radialDirection,
        smul_smul, pow_succ]

theorem cover_pow_timeDirection (i : ℕ) :
    (SlotGeometry.cover ^ i) timeDirection = ChartScales.Tg ^ i • timeDirection := by
  induction i with
  | zero => simp
  | succ i hi =>
      rw [pow_succ', _root_.mul_apply_eq_comp, hi, map_smul, cover_timeDirection,
        smul_smul, pow_succ]

/-- Radial projection as an element of `SpaceTime →L[ℝ] Plane`. -/
noncomputable def radialProjection : SpaceTime →L[ℝ] Plane :=
  ((AxisymmetricFields.projection 0).comp (ContinuousLinearMap.snd ℝ ℝ Space)).prod
    ((AxisymmetricFields.projection 1).comp (ContinuousLinearMap.snd ℝ ℝ Space))

@[simp] theorem radialProjection_apply (p : SpaceTime) :
    radialProjection p = (p.2 0, p.2 1) := rfl

theorem norm_radialProjection_le : ‖radialProjection‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro p
  rw [one_mul]
  change max ‖p.2 0‖ ‖p.2 1‖ ≤ ‖p‖
  exact max_le ((PiLp.norm_apply_le p.2 0).trans (le_max_right _ _))
    ((PiLp.norm_apply_le p.2 1).trans (le_max_right _ _))

/-- Radius power, given by `(y.1 ^ 2 + y.2 ^ 2) ^ (d / 2)`. -/
noncomputable def radiusPower (d : ℝ) (y : Plane) : ℝ :=
  (y.1 ^ 2 + y.2 ^ 2) ^ (d / 2)

/-- Radial profile, given by `radiusPower d y • radialDirection`. -/
noncomputable def radialProfile (d : ℝ) (y : Plane) : Plane :=
  radiusPower d y • radialDirection

theorem radiusPower_eq (d : ℝ) (y : Plane) :
    radiusPower d y = (Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) ^ d := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ y.1 ^ 2 + y.2 ^ 2)]
  unfold radiusPower
  congr 1
  ring

theorem sum_sq_pos {y : Plane} (hy : y ≠ 0) : 0 < y.1 ^ 2 + y.2 ^ 2 := by
  by_contra hn
  have h1 : y.1 = 0 := by nlinarith [sq_nonneg y.2]
  have h2 : y.2 = 0 := by nlinarith [sq_nonneg y.1]
  exact hy (Prod.ext h1 h2)

theorem contDiffOn_radialProfile (d : ℝ) :
    ContDiffOn ℝ ∞ (radialProfile d) {y : Plane | y ≠ 0} := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  exact (((contDiffAt_fst.pow 2).add (contDiffAt_snd.pow 2)).rpow_const_of_ne
    (sum_sq_pos hy).ne').smul contDiffAt_const

theorem radiusPower_smul (d : ℝ) {a : ℝ} (ha : 0 < a) (y : Plane) :
    radiusPower d (a • y) = a ^ d * radiusPower d y := by
  unfold radiusPower
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show (a * y.1) ^ 2 + (a * y.2) ^ 2 = a ^ 2 * (y.1 ^ 2 + y.2 ^ 2) by ring,
    Real.mul_rpow (sq_nonneg a) (by positivity), ← Real.rpow_natCast_mul ha.le]
  rw [show ((2 : ℕ) : ℝ) * (d / 2) = d by norm_num; ring]

/-- The universal-cover representative of `Y_i=J_g^i(v_r r^d+v_t t)`. -/
noncomputable def nativeGraph (h : ℝ) (n : ℕ) (p : SpaceTime) : Plane :=
  (SlotGeometry.cover ^ ChartScales.nativeIndex h n)
    (radialProfile (ChartScales.radialExponent h) (radialProjection p) + p.1 • timeDirection)

theorem nativeGraph_eq (h : ℝ) (n : ℕ) (p : SpaceTime) :
    nativeGraph h n p =
      ChartScales.Lambda ^ ChartScales.nativeIndex h n •
        radialProfile (ChartScales.radialExponent h) (radialProjection p) +
      ChartScales.Tg ^ ChartScales.nativeIndex h n • (p.1 • timeDirection) := by
  unfold nativeGraph radialProfile
  rw [map_add, map_smul, map_smul, cover_pow_radialDirection, cover_pow_timeDirection]
  simp only [smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- Scaled radial, given by `ChartScales.Q n ^ (-(1 / 2 : ℝ)) • radialProjection`. -/
noncomputable def scaledRadial (n : ℕ) : SpaceTime →L[ℝ] Plane :=
  ChartScales.Q n ^ (-(1 / 2 : ℝ)) • radialProjection

theorem norm_scaledRadial_le (n : ℕ) :
    ‖scaledRadial n‖ ≤ ChartScales.Q n ^ (-(1 / 2 : ℝ)) := by
  have hp := Real.rpow_nonneg (ChartScales.Q_pos n).le (-(1 / 2 : ℝ))
  refine ContinuousLinearMap.opNorm_le_bound _ hp ?_
  intro p
  change ‖ChartScales.Q n ^ (-(1 / 2 : ℝ)) • radialProjection p‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg hp]
  apply mul_le_mul_of_nonneg_left _ hp
  calc
    ‖radialProjection p‖ ≤ ‖radialProjection‖ * ‖p‖ := radialProjection.le_opNorm p
    _ ≤ ‖p‖ := mul_le_of_le_one_left (norm_nonneg p) norm_radialProjection_le

theorem unscale_radial (n : ℕ) (p : SpaceTime) :
    ChartScales.Q n ^ (1 / 2 : ℝ) • scaledRadial n p = radialProjection p := by
  simp only [scaledRadial, _root_.smul_apply, smul_smul]
  rw [← Real.rpow_add (ChartScales.Q_pos n)]
  norm_num

theorem nativeGraph_normalized (h : ℝ) (n : ℕ) (p : SpaceTime) :
    nativeGraph h n p =
      ChartScales.radialCoefficient h n •
        radialProfile (ChartScales.radialExponent h) (scaledRadial n p) +
      ChartScales.Tg ^ ChartScales.nativeIndex h n • (p.1 • timeDirection) := by
  have hr : radiusPower (ChartScales.radialExponent h) (radialProjection p) =
      ChartScales.Q n ^ (ChartScales.radialExponent h / 2) *
        radiusPower (ChartScales.radialExponent h) (scaledRadial n p) := by
    rw [← unscale_radial n p, radiusPower_smul _
      (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _), ← Real.rpow_mul (ChartScales.Q_pos n).le]
    rw [show (1 / 2 : ℝ) * ChartScales.radialExponent h = ChartScales.radialExponent h / 2 by ring]
  simp only [nativeGraph_eq, radialProfile, hr, ChartScales.radialCoefficient, smul_smul, mul_assoc]

/-- A fixed compact transverse annulus in normalized Cartesian coordinates. -/
noncomputable def annulus (a b : ℝ) : Set Plane :=
  Metric.closedBall 0 b ∩ {y | a ≤ ‖y‖}

theorem isCompact_annulus (a b : ℝ) : IsCompact (annulus a b) :=
  (isCompact_closedBall 0 b).inter_right (isClosed_le continuous_const continuous_norm)

theorem annulus_axisFree {a b : ℝ} (ha : 0 < a) :
    annulus a b ⊆ {y : Plane | y ≠ 0} := by
  intro y hy hz
  have : a ≤ ‖y‖ := hy.2
  rw [hz, norm_zero] at this
  linarith

/-- Compactness is used only for one fixed smooth profile on one fixed annulus. -/
theorem compact_jet_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ k ≤ m, ∀ y ∈ K, ‖iteratedFDeriv ℝ k f y‖ ≤ C := by
  have hsingle (k : ℕ) : ∃ C : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ k f y‖ ≤ C := by
    have hc := (hf.continuousOn_iteratedFDerivWithin (m := k) (nat_le_infty k)
        hU.uniqueDiffOn).mono hKU
    have he : ContinuousOn (iteratedFDeriv ℝ k f) K := by
      apply hc.congr
      intro y hy
      exact (iteratedFDerivWithin_of_isOpen k hU (hKU hy)).symm
    exact hK.exists_bound_of_continuousOn he
  induction m with
  | zero =>
      obtain ⟨C, hC⟩ := hsingle 0
      refine ⟨max 1 C, le_max_left _ _, ?_⟩
      intro k hk y hy
      have : k = 0 := by omega
      subst k
      exact (hC y hy).trans (le_max_right _ _)
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      obtain ⟨D, hD⟩ := hsingle (m + 1)
      refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
      intro k hk y hy
      by_cases hkm : k ≤ m
      · exact (hbound k hkm y hy).trans (le_max_left _ _)
      · have : k = m + 1 := by omega
        subst k
        exact (hD y hy).trans (le_max_right _ _)

/-- Exact linear-rescaling estimate for actual higher derivatives on an open domain. -/
theorem norm_jet_comp_linear {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {U : Set F} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (L : E →L[ℝ] F) {x : E} (hx : L x ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L‖ ^ k := by
  have hp := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hp.uniqueDiffOn hx
    (i := k) (nat_le_infty k)
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hU hx] at he
  rw [he]
  simpa using (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

theorem axisFree_open : IsOpen {y : Plane | y ≠ 0} := isClosed_singleton.isOpen_compl

theorem S_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ ChartScales.S n := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold ChartScales.S
  nlinarith

/-- The actual floor index has a fixed time-frequency power bound. -/
theorem native_time_power_le {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) :
    ChartScales.Tg ^ ChartScales.nativeIndex h n ≤ ChartScales.Q n ^ (-2 : ℝ) := by
  calc
    ChartScales.Tg ^ ChartScales.nativeIndex h n ≤
        ChartScales.Q n ^ (-1 - h) / ChartScales.S n :=
      (ChartScales.native_power_bounds h hh hn).1
    _ ≤ ChartScales.Q n ^ (-1 - h) := div_le_self
      (Real.rpow_nonneg (ChartScales.Q_pos n).le _) (S_ge_one (by omega))
    _ ≤ ChartScales.Q n ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge
      (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by linarith)

/-- A coarse fixed power controls the actual normalized radial graph frequency. -/
theorem native_radial_power_le {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    {n : ℕ} (hn : 4 ≤ n) :
    ChartScales.radialCoefficient h n ≤ ChartScales.Q n ^ (-1 : ℝ) := by
  have hs : ChartScales.S n ^ (-ChartScales.rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (S_ge_one (by
        omega)) (neg_nonpos.mpr ChartScales.rho_pos.le)
  calc
    ChartScales.radialCoefficient h n ≤
        ChartScales.epsilon h n ^ (-ChartScales.kappa) * ChartScales.S n ^ (-ChartScales.rho) :=
      (ChartScales.radialCoefficient_bounds h hh hn).2
    _ ≤ ChartScales.epsilon h n ^ (-ChartScales.kappa) :=
      mul_le_of_le_one_right (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _) hs
    _ = ChartScales.Q n ^ (-h * ChartScales.kappa) := by
      unfold ChartScales.epsilon
      rw [← Real.rpow_mul (ChartScales.Q_pos n).le]
      congr 1
      ring
    _ ≤ ChartScales.Q n ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by
        unfold ChartScales.kappa
        linarith)

theorem norm_scaledRadial_coarse_le (n : ℕ) :
    ‖scaledRadial n‖ ≤ ChartScales.Q n ^ (-1 : ℝ) :=
  (norm_scaledRadial_le n).trans (Real.rpow_le_rpow_of_exponent_ge
    (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by norm_num))

theorem norm_positive_jet_linear_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (x : E) {k : ℕ} (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k L x‖ ≤ ‖L‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have hd : fderiv ℝ L = fun _ => L := by funext y; exact L.fderiv
  rw [hd]
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, norm_nonneg]

/-- Time profile, given by `(ContinuousLinearMap.fst ℝ ℝ Space).smulRight timeDirection`. -/
noncomputable def timeProfile : SpaceTime →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ Space).smulRight timeDirection

@[simp] theorem timeProfile_apply (p : SpaceTime) : timeProfile p = p.1 • timeDirection := rfl

theorem norm_timeProfile_le : ‖timeProfile‖ ≤ ‖timeDirection‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro p
  rw [timeProfile_apply, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)

theorem timeProfile_jet_bound (p : SpaceTime) (ht : |p.1| ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k timeProfile p‖ ≤ ‖timeDirection‖ := by
  cases k with
  | zero =>
      rw [norm_iteratedFDeriv_zero, timeProfile_apply, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) ht
  | succ k => exact (norm_positive_jet_linear_le timeProfile p (by omega)).trans norm_timeProfile_le

theorem contDiffAt_nativeGraph (h : ℝ) (n : ℕ) {p : SpaceTime}
    (hp : radialProjection p ≠ 0) : ContDiffAt ℝ ∞ (nativeGraph h n) p := by
  have hr := ((contDiffOn_radialProfile (ChartScales.radialExponent h)).contDiffAt
    (axisFree_open.mem_nhds hp)).comp p radialProjection.contDiff.contDiffAt
  exact (SlotGeometry.cover ^ ChartScales.nativeIndex h n).contDiff.contDiffAt.comp p
    (hr.add timeProfile.contDiff.contDiffAt)

theorem scaledRadial_ne_zero {n : ℕ} {p : SpaceTime} (hp : scaledRadial n p ≠ 0) :
    radialProjection p ≠ 0 := by
  intro hz
  apply hp
  simp [scaledRadial, hz]

/-- The bound is uniform in the dyadic band and contains no stage index.
The compact annulus supplies constants; all powers come from the actual
covering index and the actual physical rescaling. -/
theorem nativeGraph_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (ha : 0 < a)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (nativeGraph h n) p‖ ≤
        C * ChartScales.Q n ^ (-((m : ℝ) + 2)) := by
  obtain ⟨C, hC, hbound⟩ := compact_jet_bound axisFree_open
    (contDiffOn_radialProfile (ChartScales.radialExponent h)) (isCompact_annulus a b)
    (annulus_axisFree ha) m
  refine ⟨C + ‖timeDirection‖, by linarith [norm_nonneg timeDirection], ?_⟩
  intro n hn p hp ht k hk
  have hq := ChartScales.Q_pos n
  have hq1 := ChartScales.Q_le_one n
  have hC0 : 0 ≤ C := by linarith
  have haxis := annulus_axisFree ha hp
  have hr : ContDiffAt ℝ k
      (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) p :=
    (((contDiffOn_radialProfile (ChartScales.radialExponent h)).contDiffAt
      (axisFree_open.mem_nhds haxis)).comp p (scaledRadial n).contDiff.contDiffAt).of_le
        (nat_le_infty k)
  have he : nativeGraph h n = fun z =>
      ChartScales.radialCoefficient h n •
        (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) z +
      ChartScales.Tg ^ ChartScales.nativeIndex h n • timeProfile z := by
    funext z
    exact nativeGraph_normalized h n z
  rw [he, fun_iteratedFDeriv_add_apply (hr.const_smul _)
    ((timeProfile.contDiff.contDiffAt (x := p)).const_smul _),
    iteratedFDeriv_const_smul_apply' hr,
    iteratedFDeriv_const_smul_apply' timeProfile.contDiff.contDiffAt]
  apply (norm_add_le _ _).trans
  have hrad : ‖ChartScales.radialCoefficient h n •
      iteratedFDeriv ℝ k (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) p‖ ≤
      C * ChartScales.Q n ^ (-((m : ℝ) + 2)) := by
    rw [norm_smul (ChartScales.radialCoefficient h n)
      (iteratedFDeriv ℝ k (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) p)]
    rw [Real.norm_of_nonneg (ChartScales.radialCoefficient_pos h n).le]
    have hj := norm_jet_comp_linear axisFree_open
      (contDiffOn_radialProfile (ChartScales.radialExponent h)) (scaledRadial n) haxis k
    have hl := pow_le_pow_left₀ (norm_nonneg (scaledRadial n)) (norm_scaledRadial_coarse_le n) k
    have hfull := mul_le_mul_of_nonneg_left
      (hj.trans (mul_le_mul (hbound k hk _ hp) hl (by positivity) hC0))
      (ChartScales.radialCoefficient_pos h n).le
    have hM := native_radial_power_le hh hh1 hn
    have hprod := hfull.trans (mul_le_mul_of_nonneg_right hM (by positivity))
    have hpow : ChartScales.Q n ^ (-1 : ℝ) * (C * (ChartScales.Q n ^ (-1 : ℝ)) ^ k) =
        C * ChartScales.Q n ^ (-((k : ℝ) + 1)) := by
      rw [← Real.rpow_mul_natCast hq.le]
      rw [mul_left_comm, ← Real.rpow_add hq]
      congr 2
      ring
    rw [hpow] at hprod
    exact hprod.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by
        have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
        linarith)) hC0)
  have htime : ‖ChartScales.Tg ^ ChartScales.nativeIndex h n • iteratedFDeriv ℝ k timeProfile p‖ ≤
      ‖timeDirection‖ * ChartScales.Q n ^ (-((m : ℝ) + 2)) := by
    rw [norm_smul (ChartScales.Tg ^ ChartScales.nativeIndex h n)
      (iteratedFDeriv ℝ k timeProfile p)]
    rw [Real.norm_of_nonneg (pow_nonneg ChartScales.Tg_pos.le _)]
    calc
      _ ≤ ChartScales.Q n ^ (-2 : ℝ) * ‖timeDirection‖ :=
        mul_le_mul (native_time_power_le hh hh1 hn) (timeProfile_jet_bound p ht k)
          (norm_nonneg _) (Real.rpow_nonneg hq.le _)
      _ ≤ ChartScales.Q n ^ (-((m : ℝ) + 2)) * ‖timeDirection‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by
          have := Nat.cast_nonneg (α := ℝ) m
          linarith)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ C * ChartScales.Q n ^ (-((m : ℝ) + 2)) +
        ‖timeDirection‖ * ChartScales.Q n ^ (-((m : ℝ) + 2)) := add_le_add hrad htime
    _ = _ := by ring

/-- Chart point: an abbreviation for `ℝ × (ℝ × (ℝ × ℝ))`. -/
abbrev ChartPoint := ℝ × (ℝ × (ℝ × ℝ))
/-- Lift point: an abbreviation for `ChartPoint × Plane`. -/
abbrev LiftPoint := ChartPoint × Plane

/-- Coordinate projection, given by `(AxisymmetricFields.projection j).comp
(ContinuousLinearMap.snd ℝ ℝ Space)`. -/
noncomputable def coordinateProjection (j : Fin 3) : SpaceTime →L[ℝ] ℝ :=
  (AxisymmetricFields.projection j).comp (ContinuousLinearMap.snd ℝ ℝ Space)

@[simp] theorem coordinateProjection_apply (j : Fin 3) (p : SpaceTime) :
    coordinateProjection j p = p.2 j := rfl

/-- Cartesian form of the exact chart `(T, R cos θ, R sin θ, Z)`. -/
noncomputable def chartLinear (h : ℝ) (n : ℕ) : SpaceTime →L[ℝ] ChartPoint :=
  (-ChartScales.Q n ^ (-1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ Space).prod
    ((ChartScales.Q n ^ (-(1 / 2 : ℝ)) • coordinateProjection 0).prod
      ((ChartScales.Q n ^ (-(1 / 2 : ℝ)) • coordinateProjection 1).prod
        (ChartScales.Q n ^ (-CoordinateAlgebra.D h) • coordinateProjection 2)))

@[simp] theorem chartLinear_apply (h : ℝ) (n : ℕ) (p : SpaceTime) :
    chartLinear h n p = (-ChartScales.Q n ^ (-1 : ℝ) * p.1,
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * p.2 0,
        (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * p.2 1,
          ChartScales.Q n ^ (-CoordinateAlgebra.D h) * p.2 2))) := by
  simp [chartLinear, smul_eq_mul]

/-- Physical chart, given by `chartLinear h n p + (ChartScales.Q n ^ (-1 : ℝ), 0)`. -/
noncomputable def physicalChart (h : ℝ) (n : ℕ) (p : SpaceTime) : ChartPoint :=
  chartLinear h n p + (ChartScales.Q n ^ (-1 : ℝ), 0)

theorem physicalChart_time (h : ℝ) (n : ℕ) (p : SpaceTime) :
    (physicalChart h n p).1 = (1 - p.1) / ChartScales.Q n := by
  simp only [physicalChart, Prod.fst_add, chartLinear_apply]
  rw [Real.rpow_neg_one]
  ring

theorem norm_chartLinear_le {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ‖chartLinear h n‖ ≤ ChartScales.Q n ^ (-1 : ℝ) := by
  have hq := ChartScales.Q_pos n
  have hscale := Real.rpow_nonneg hq.le (-1 : ℝ)
  have hhalf : ChartScales.Q n ^ (-(1 / 2 : ℝ)) ≤ ChartScales.Q n ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hq (ChartScales.Q_le_one n) (by norm_num)
  have hax : ChartScales.Q n ^ (-CoordinateAlgebra.D h) ≤ ChartScales.Q n ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hq (ChartScales.Q_le_one n) (by
      unfold CoordinateAlgebra.D
      linarith)
  refine ContinuousLinearMap.opNorm_le_bound _ hscale ?_
  intro p
  have hcoord (j : Fin 3) : ‖p.2 j‖ ≤ ‖p‖ :=
    (PiLp.norm_apply_le p.2 j).trans (le_max_right _ _)
  have hs (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ ChartScales.Q n ^ (-1 : ℝ)) (j : Fin 3) :
      ‖c * p.2 j‖ ≤ ChartScales.Q n ^ (-1 : ℝ) * ‖p‖ := by
    rw [norm_mul, Real.norm_of_nonneg hc]
    exact mul_le_mul hc1 (hcoord j) (norm_nonneg _) hscale
  rw [chartLinear_apply]
  change max ‖-ChartScales.Q n ^ (-1 : ℝ) * p.1‖
    (max ‖ChartScales.Q n ^ (-(1 / 2 : ℝ)) * p.2 0‖
      (max ‖ChartScales.Q n ^ (-(1 / 2 : ℝ)) * p.2 1‖
        ‖ChartScales.Q n ^ (-CoordinateAlgebra.D h) * p.2 2‖)) ≤ _
  apply max_le
  · rw [norm_mul, norm_neg, Real.norm_of_nonneg hscale]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hscale
  · exact max_le (hs _ (Real.rpow_nonneg hq.le _) hhalf 0)
      (max_le (hs _ (Real.rpow_nonneg hq.le _) hhalf 1)
        (hs _ (Real.rpow_nonneg hq.le _) hax 2))

theorem physicalChart_smooth (h : ℝ) (n : ℕ) : ContDiff ℝ ∞ (physicalChart h n) :=
  (chartLinear h n).contDiff.add contDiff_const

theorem physicalChart_jet_bound {h : ℝ} (hh : 0 ≤ h) (n : ℕ) (p : SpaceTime)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (physicalChart h n) p‖ ≤ ChartScales.Q n ^ (-1 : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold physicalChart
  rw [fun_iteratedFDeriv_add_apply (chartLinear h n).contDiff.contDiffAt contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero]
  exact (norm_positive_jet_linear_le _ _ (by omega)).trans (norm_chartLinear_le hh n)

theorem iteratedFDeriv_pair {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E} {k : ℕ}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    iteratedFDeriv ℝ k (fun y => (f y, g y)) x =
      (iteratedFDeriv ℝ k f x).prod (iteratedFDeriv ℝ k g x) := by
  have h1 := (ContinuousLinearMap.fst ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  have h2 := (ContinuousLinearMap.snd ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  apply ContinuousMultilinearMap.ext
  intro v
  apply Prod.ext
  · exact (congrArg (fun M => M v) h1).symm
  · exact (congrArg (fun M => M v) h2).symm

/-- Actual graph restriction together with the exact physical chart scaling. -/
noncomputable def physicalLift (h : ℝ) (n : ℕ) (p : SpaceTime) : LiftPoint :=
  (physicalChart h n p, nativeGraph h n p)

theorem physicalLift_smooth (h : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (physicalLift h n) {p | radialProjection p ≠ 0} := by
  intro p hp
  exact ((physicalChart_smooth h n).contDiffAt.prodMk
    (contDiffAt_nativeGraph h n hp)).contDiffWithinAt

theorem physicalLift_positive_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (ha : 0 < a) (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (physicalLift h n) p‖ ≤
        C * ChartScales.Q n ^ (-((m : ℝ) + 2)) := by
  obtain ⟨C, hC, hbound⟩ := nativeGraph_jet_bound hh (by linarith : h ≤ 1) ha m
  refine ⟨C, hC, ?_⟩
  intro n hn p hp ht k hk hkm
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hp)
  change ‖iteratedFDeriv ℝ k (fun z => (physicalChart h n z, nativeGraph h n z)) p‖ ≤ _
  rw [iteratedFDeriv_pair
    ((physicalChart_smooth h n).contDiffAt.of_le (nat_le_infty k))
    ((contDiffAt_nativeGraph h n haxis).of_le (nat_le_infty k)),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · calc
      _ ≤ ChartScales.Q n ^ (-1 : ℝ) := physicalChart_jet_bound hh n p hk
      _ ≤ ChartScales.Q n ^ (-((m : ℝ) + 2)) :=
        Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by
          have := Nat.cast_nonneg (α := ℝ) m
          linarith)
      _ ≤ C * ChartScales.Q n ^ (-((m : ℝ) + 2)) :=
        le_mul_of_one_le_left (Real.rpow_nonneg (ChartScales.Q_pos n).le _) hC
  · exact hbound n hn p hp ht k hkm

/-- The fixed derivative loss for graph composition; it depends on jet order alone. -/
noncomputable def graphLoss (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 2)

/-- A genuine all-order chain estimate for the concrete native graph. The
stripped coefficient is an actual smooth function; its stage-dependent jet
bound enters only multiplicatively. -/
theorem graphRestriction_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 →
      ∀ F : LiftPoint → E, ContDiff ℝ ∞ F → ∀ B : ℝ, 0 ≤ B →
      (∀ k ≤ m, ‖iteratedFDeriv ℝ k F (physicalLift h n p)‖ ≤ B) →
      ‖iteratedFDeriv ℝ m (F ∘ physicalLift h n) p‖ ≤
        C * B * ChartScales.Q n ^ (-graphLoss m) := by
  obtain ⟨C, hC, hbound⟩ := physicalLift_positive_jet_bound hh hh1 ha m
  refine ⟨(m.factorial : ℝ) * C ^ m, mul_pos (by positivity) (pow_pos (by linarith) _), ?_⟩
  intro n hn p hp ht F hF B hB hFB
  let U : Set SpaceTime := {p | radialProjection p ≠ 0}
  have hU : IsOpen U := axisFree_open.preimage radialProjection.continuous
  have hx : p ∈ U := scaledRadial_ne_zero (annulus_axisFree ha hp)
  let D := C * ChartScales.Q n ^ (-((m : ℝ) + 2))
  have hpower : 1 ≤ ChartScales.Q n ^ (-((m : ℝ) + 2)) := by
    have he := Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n)
      (ChartScales.Q_le_one n) (show -((m : ℝ) + 2) ≤ 0 by
        have := Nat.cast_nonneg (α := ℝ) m
        linarith)
    simpa only [Real.rpow_zero] using he
  have hD : 1 ≤ D := by dsimp [D]; nlinarith
  have hj := norm_iteratedFDerivWithin_comp_le hF.contDiffOn (physicalLift_smooth h n)
    (nat_le_infty m) uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hx
    (C := B) (D := D)
    (fun k hk => by simpa only [iteratedFDerivWithin_univ] using hFB k hk)
    (fun k hk hkm => by
      rw [iteratedFDerivWithin_of_isOpen k hU hx]
      exact (hbound n hn p hp ht k hk hkm).trans (by
        simpa only [pow_one] using (pow_le_pow_right₀ hD hk)))
  rw [iteratedFDerivWithin_of_isOpen m hU hx] at hj
  apply hj.trans_eq
  dsimp [D]
  rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  have he : -((m : ℝ) + 2) * (m : ℝ) = -graphLoss m := by unfold graphLoss; ring
  rw [he]
  ring

/-- The dual coordinate along `v_t` in the manuscript's slot rectangle. -/
noncomputable def etaCoordinate : Plane →L[ℝ] ℝ :=
  (1 + (Real.sqrt 2 - 1) ^ 2)⁻¹ •
    ((Real.sqrt 2 - 1) • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem etaCoordinate_radial : etaCoordinate radialDirection = 0 := by
  simp [etaCoordinate, radialDirection, smul_eq_mul]
  ring

theorem etaCoordinate_time : etaCoordinate timeDirection = 1 := by
  have hd : 1 + (Real.sqrt 2 - 1) ^ 2 ≠ 0 := by positivity
  change (1 + (Real.sqrt 2 - 1) ^ 2)⁻¹ * ((Real.sqrt 2 - 1) * (Real.sqrt 2 - 1) + 1) = 1
  field_simp; ring

theorem etaCoordinate_nativeGraph (h : ℝ) (n : ℕ) (p : SpaceTime) :
    etaCoordinate (nativeGraph h n p) = ChartScales.Tg ^ ChartScales.nativeIndex h n * p.1 := by
  rw [nativeGraph_eq, map_add, map_smul, map_smul]
  simp only [radialProfile, map_smul, etaCoordinate_radial, etaCoordinate_time, smul_eq_mul,
      mul_one, mul_zero, zero_add]

/-- `center` includes the periodically reindexed lattice-copy translation. -/
noncomputable def slotTime (h : ℝ) (n : ℕ) (center : Plane) (r0 : ℝ)
    (p : SpaceTime) : ℝ :=
  (etaCoordinate (nativeGraph h n p - center) + r0) / ChartScales.timeCoefficient h n

theorem slotTime_affine (h : ℝ) (n : ℕ) (center : Plane) (r0 : ℝ) (p : SpaceTime) :
    slotTime h n center r0 p =
      ChartScales.Q n ^ (-1 - h) * p.1 +
        (r0 - etaCoordinate center) / ChartScales.timeCoefficient h n := by
  have ht : ChartScales.Tg ^ ChartScales.nativeIndex h n ≠ 0 :=
    (pow_pos ChartScales.Tg_pos _).ne'
  have hQ : ChartScales.Q n ^ (1 + h) ≠ 0 :=
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).ne'
  have hp : ChartScales.Q n ^ (-1 - h) = (ChartScales.Q n ^ (1 + h))⁻¹ := by
    rw [show -1 - h = -(1 + h) by ring, Real.rpow_neg (ChartScales.Q_pos n).le]
  unfold slotTime
  rw [map_sub, etaCoordinate_nativeGraph, hp]
  unfold ChartScales.timeCoefficient
  field_simp; ring

theorem hasFDerivAt_slotTime (h : ℝ) (n : ℕ) (center : Plane) (r0 : ℝ) (p : SpaceTime) :
    HasFDerivAt (slotTime h n center r0)
      (ChartScales.Q n ^ (-1 - h) • ContinuousLinearMap.fst ℝ ℝ Space) p := by
  have he : slotTime h n center r0 = fun z =>
      ChartScales.Q n ^ (-1 - h) * z.1 +
        (r0 - etaCoordinate center) / ChartScales.timeCoefficient h n := by
    funext z
    exact slotTime_affine h n center r0 z
  rw [he]
  exact ((ContinuousLinearMap.fst ℝ ℝ Space).hasFDerivAt.const_mul _).add_const _

theorem slotTime_derivative (h : ℝ) (n : ℕ) (center : Plane) (r0 : ℝ)
    (p v : SpaceTime) :
    fderiv ℝ (slotTime h n center r0) p v = ChartScales.Q n ^ (-1 - h) * v.1 := by
  rw [(hasFDerivAt_slotTime h n center r0 p).fderiv]
  rfl

theorem slotTime_spatial_derivative (h : ℝ) (n : ℕ) (center : Plane) (r0 : ℝ)
    (p : SpaceTime) (v : Space) : fderiv ℝ (slotTime h n center r0) p (0, v) = 0 := by
  simp [slotTime_derivative]

/-- Exact integer rounding gives a uniform upper carrier power. -/
theorem carrier_upper {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    (ChartScales.carrier h n : ℝ) ≤ 2 * ChartScales.Q n ^ (-h / 2) := by
  have he := ChartScales.epsilon_pos h n
  have hs : Real.sqrt (ChartScales.epsilon h n) ≤ 1 :=
    Real.sqrt_le_one.mpr (ChartScales.epsilon_le_one h hh n)
  have hk := (Scaling.carrier_frequency_sqrt_bounds he).2
  have hk2 : (ChartScales.carrier h n : ℝ) * Real.sqrt (ChartScales.epsilon h n) ≤ 2 := by
    exact hk.trans (by linarith)
  calc
    _ ≤ 2 / Real.sqrt (ChartScales.epsilon h n) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr he)).mpr hk2
    _ = _ := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg he.le]
      unfold ChartScales.epsilon
      rw [← Real.rpow_mul (ChartScales.Q_pos n).le]
      congr 2
      ring

/-- Phase factor, given by `(c : ℂ) * Complex.I`. -/
noncomputable def phaseFactor (c : ℝ) : ℂ := (c : ℂ) * Complex.I

/-- Character, given by `Complex.exp (phaseFactor c * (t : ℂ))`. -/
noncomputable def character (c : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (phaseFactor c * (t : ℂ))

@[simp] theorem norm_character (c t : ℝ) : ‖character c t‖ = 1 := by
  have he : phaseFactor c * (t : ℂ) = ((c * t : ℝ) : ℂ) * Complex.I := by
    simp only [phaseFactor, Complex.ofReal_mul]
    ring
  rw [character, he, Complex.norm_exp_ofReal_mul_I]

theorem character_smooth (c : ℝ) : ContDiff ℝ ∞ (character c) := by
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem hasDerivAt_character (c t : ℝ) :
    HasDerivAt (character c) (phaseFactor c * character c t) t := by
  have hd := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (phaseFactor c)
  convert! hd.cexp using 1
  simp [character, phaseFactor]
  ring

theorem iteratedDeriv_character (c : ℝ) (m : ℕ) :
    iteratedDeriv m (character c) = fun t => phaseFactor c ^ m * character c t := by
  induction m with
  | zero => simp
  | succ m hm =>
      rw [iteratedDeriv_succ, hm]
      funext t
      rw [deriv_const_mul_field]
      rw [(hasDerivAt_character c t).deriv, pow_succ]
      ring

/-- Every carrier derivative is computed exactly, including derivative order zero. -/
theorem norm_character_jet (c : ℝ) (m : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ m (character c) t‖ = |c| ^ m := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_character]
  simp [norm_character, phaseFactor, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]

/-- Stage harmonics change the multiplicative constant, never the power loss. -/
theorem rounded_carrier_jet_bound {h : ℝ} (hh : 0 ≤ h) (n m : ℕ)
    (j : ℤ) {H : ℝ} (hH : |(j : ℝ)| ≤ H) (t : ℝ) :
    ‖iteratedFDeriv ℝ m (character ((ChartScales.carrier h n : ℝ) * (j : ℝ))) t‖ ≤
      (2 * H) ^ m * ChartScales.Q n ^ (-(h * (m : ℝ) / 2)) := by
  rw [norm_character_jet, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hh0 : 0 ≤ H := (abs_nonneg _).trans hH
  have hk := mul_le_mul (carrier_upper hh n) hH (abs_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (ChartScales.Q_pos n).le _))
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (ChartScales.carrier h n : ℝ) * |(j : ℝ)|) hk m
  apply hp.trans_eq
  rw [mul_right_comm, mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  congr 2
  ring

theorem pointwise_product_jet_bound {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A] {f g : E → A} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : E) {m k : ℕ} (hk : k ≤ m) {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hfb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ P)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g x‖ ≤ Q) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ m * P * Q := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (nat_le_infty k)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * P * Q := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i him) (Nat.cast_nonneg _))
        (hgb (k - i) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hP)
    _ = (2 : ℝ) ^ k * P * Q := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ (2 : ℝ) ^ m * P * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hk) hP) hQ

/-- The actual oscillatory exponential obeys a finite-jet bound in any
smooth real phase. No formal carrier derivative is substituted for a real derivative. -/
theorem character_comp_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (x : E) (m : ℕ) {c B M : ℝ}
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hΦb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (character c ∘ Φ) x‖ ≤
      (m.factorial : ℝ) * M ^ m * B ^ m := by
  intro k hk
  have hbound := norm_iteratedFDeriv_comp_le (character_smooth c) hΦ (nat_le_infty k) x
    (C := M ^ m) (D := B)
    (fun i hi => by
      rw [norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans
        (pow_le_pow_right₀ hM (hi.trans hk)))
    (fun i hi him => (hΦb i (him.trans hk)).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hB hi))
  apply hbound.trans
  have hfac : (k.factorial : ℝ) ≤ m.factorial := by
    exact_mod_cast Nat.factorial_le hk
  exact mul_le_mul (mul_le_mul_of_nonneg_right hfac (by positivity))
    (pow_le_pow_right₀ hB hk) (by positivity) (by positivity)

/-- Combining amplitude, the actual rounded carrier, and the actual native
graph gives a physical loss independent of the harmonic cutoff `H`. -/
theorem carrier_graph_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (ha : 0 < a) (m : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 →
      ∀ (A : LiftPoint → ℂ) (Φ : LiftPoint → ℝ),
      ContDiff ℝ ∞ A → ContDiff ℝ ∞ Φ → ∀ (P B H : ℝ) (j : ℤ),
      0 ≤ P → 1 ≤ B → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i A (physicalLift h n p)‖ ≤ P) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i Φ (physicalLift h n p)‖ ≤ B) →
      ‖iteratedFDeriv ℝ m
        ((fun y => A y * character ((ChartScales.carrier h n : ℝ) * (j : ℝ)) (Φ y)) ∘
          physicalLift h n) p‖ ≤
        C * P * B ^ m * (1 + 2 * H) ^ m *
          ChartScales.Q n ^ (-(graphLoss m + h * (m : ℝ) / 2)) := by
  obtain ⟨C, hC, hbound⟩ := graphRestriction_jet_bound (E := ℂ) (b := b) hh hh1 ha m
  refine ⟨C * (2 : ℝ) ^ m * m.factorial, by positivity, ?_⟩
  intro n hn p hp ht A Φ hA hΦ P B H j hP hB hH hAb hΦb
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hH
  have hq := ChartScales.Q_pos n
  let M := (1 + 2 * H) * ChartScales.Q n ^ (-h / 2)
  have hQpow : 1 ≤ ChartScales.Q n ^ (-h / 2) := by
    have he := Real.rpow_le_rpow_of_exponent_ge hq (ChartScales.Q_le_one n)
      (show -h / 2 ≤ 0 by linarith)
    simpa only [Real.rpow_zero] using he
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
  have hc : |(ChartScales.carrier h n : ℝ) * (j : ℝ)| ≤ M := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have he := mul_le_mul (carrier_upper hh n) hH (abs_nonneg _)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hq.le _))
    exact he.trans (by dsimp [M]; nlinarith)
  have hw := character_comp_jet_bound hΦ (physicalLift h n p) m hB hM hc hΦb
  have hwsm := (character_smooth ((ChartScales.carrier h n : ℝ) * (j : ℝ))).comp hΦ
  have hb : 0 ≤ (2 : ℝ) ^ m * P * ((m.factorial : ℝ) * M ^ m * B ^ m) := by positivity
  have hphysical := hbound n hn p hp ht (fun y => A y * character
    ((ChartScales.carrier h n : ℝ) * (j : ℝ)) (Φ y)) (hA.mul hwsm)
    _ hb (fun i hi => pointwise_product_jet_bound hA hwsm (physicalLift h n p)
      hi hP (by positivity) hAb hw)
  apply hphysical.trans_eq
  dsimp [M]
  rw [mul_pow, ← Real.rpow_mul_natCast hq.le]
  rw [show -h / 2 * (m : ℝ) = -(h * (m : ℝ) / 2) by ring]
  have he : ChartScales.Q n ^ (-(h * (m : ℝ) / 2)) * ChartScales.Q n ^ (-graphLoss m) =
      ChartScales.Q n ^ (-(graphLoss m + h * (m : ℝ) / 2)) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  calc
    _ = C * 2 ^ m * (m.factorial : ℝ) * P * B ^ m * (1 + 2 * H) ^ m *
        (ChartScales.Q n ^ (-(h * (m : ℝ) / 2)) * ChartScales.Q n ^ (-graphLoss m)) := by ring
    _ = _ := by rw [he]

/-- Every real power transfers across the actual factor-two dyadic overlap.
Its exponent can contain the stage gain; only the constant changes. -/
theorem comparable_rpow {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q)
    (hlo : q / 2 ≤ Q) (hhi : Q ≤ 2 * q) (e : ℝ) :
    Q ^ e ≤ 2 ^ |e| * q ^ e := by
  by_cases he : 0 ≤ e
  · calc
      Q ^ e ≤ (2 * q) ^ e := Real.rpow_le_rpow hQ.le hhi he
      _ = 2 ^ |e| * q ^ e := by rw [Real.mul_rpow (by norm_num) hq.le, abs_of_nonneg he]
  · have he' : e ≤ 0 := le_of_not_ge he
    calc
      Q ^ e ≤ (q / 2) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) hlo he'
      _ = q ^ e / (2 : ℝ) ^ e := Real.div_rpow hq.le (by norm_num) e
      _ = 2 ^ |e| * q ^ e := by
        rw [abs_of_nonpos he', Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-- Arbitrary fixed powers of the slow scale can be absorbed with one
fixed power loss; the constant may depend on the slow power. -/
theorem slow_power_absorption (a : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    ChartScales.S n ^ a ≤ C * ChartScales.Q n ^ (-1 : ℝ) := by
  have ht := ChartScales.slow_power_epsilon_tendsto_zero (h := 1) (by norm_num) a 1 (by norm_num)
  have ht' : Filter.Tendsto (fun n => ChartScales.S n ^ a * ChartScales.Q n)
      Filter.atTop (nhds 0) := by simpa [ChartScales.epsilon] using ht
  obtain ⟨C, hC, hCb⟩ := (Metric.isBounded_range_of_tendsto _ ht').exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro n
  have hb := hCb (ChartScales.S n ^ a * ChartScales.Q n) (mem_range_self n)
  have hS : 0 ≤ ChartScales.S n := sq_nonneg (n : ℝ)
  have hn0 : 0 ≤ ChartScales.S n ^ a * ChartScales.Q n :=
    mul_nonneg (Real.rpow_nonneg hS a) (ChartScales.Q_pos n).le
  rw [Real.norm_of_nonneg hn0] at hb
  rw [Real.rpow_neg_one, ← div_eq_mul_inv]
  exact (le_div_iff₀ (ChartScales.Q_pos n)).mpr hb

/-- A stripped coefficient class with arbitrary stage-dependent slow powers
has a fixed physical loss `graphLoss m + 1` on dyadic active supports. -/
theorem stripped_class_physical_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (m : ℕ) (g d A : ℝ) (hA : 0 ≤ A) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ F : LiftPoint → E, ContDiff ℝ ∞ F →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (physicalLift h n p)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ d) →
      ‖iteratedFDeriv ℝ m (F ∘ physicalLift h n) p‖ ≤
        C * q ^ (g - (graphLoss m + 1)) := by
  obtain ⟨C, hC, hbound⟩ := graphRestriction_jet_bound (E := E) (b := b) hh hh1 ha m
  obtain ⟨D, hD, hslow⟩ := slow_power_absorption d
  refine ⟨C * A * D * 2 ^ |g - (graphLoss m + 1)|, by positivity, ?_⟩
  intro n hn p hp ht q hq hlo hhi F hF hFb
  have hQ := ChartScales.Q_pos n
  have hS : 0 ≤ ChartScales.S n := sq_nonneg (n : ℝ)
  have hb := hbound n hn p hp ht F hF _ (by positivity) hFb
  calc
    _ ≤ C * (A * ChartScales.Q n ^ g * (D * ChartScales.Q n ^ (-1 : ℝ))) *
        ChartScales.Q n ^ (-graphLoss m) := by
      apply hb.trans
      gcongr
      exact hslow n
    _ = (C * A * D) * ChartScales.Q n ^ (g - (graphLoss m + 1)) := by
      have he : ChartScales.Q n ^ g * ChartScales.Q n ^ (-1 : ℝ) *
          ChartScales.Q n ^ (-graphLoss m) =
          ChartScales.Q n ^ (g - (graphLoss m + 1)) := by
        rw [← Real.rpow_add hQ, ← Real.rpow_add hQ]
        congr 1
        ring
      calc
        _ = (C * A * D) * (ChartScales.Q n ^ g * ChartScales.Q n ^ (-1 : ℝ) *
          ChartScales.Q n ^ (-graphLoss m)) := by ring
        _ = _ := by rw [he]
    _ ≤ (C * A * D) * (2 ^ |g - (graphLoss m + 1)| * q ^ (g - (graphLoss m + 1))) :=
      mul_le_mul_of_nonneg_left (comparable_rpow hQ hq hlo hhi _) (by positivity)
    _ = _ := by ring

theorem norm_jet_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) (c : ℝ) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => c * f y) x‖ = |c| * ‖iteratedFDeriv ℝ k f x‖ := by
  change ‖iteratedFDeriv ℝ k (fun y => c • f y) x‖ = _
  rw [iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (nat_le_infty k)),
    norm_smul c (iteratedFDeriv ℝ k f x), Real.norm_eq_abs]

theorem linear_jet_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (x : E)
    {M N : ℝ} (hM : 1 ≤ M) (hx : ‖x‖ ≤ M) (hN : 0 ≤ N) (hL : ‖L‖ ≤ N) (k : ℕ) :
    ‖iteratedFDeriv ℝ k L x‖ ≤ N * M := by
  cases k with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (L.le_opNorm x).trans (mul_le_mul hL hx (norm_nonneg _) hN)
  | succ k =>
      exact ((norm_positive_jet_linear_le L x (by omega)).trans hL).trans
        (le_mul_of_one_le_right hN hM)

theorem norm_fstCLM_le (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ‖ContinuousLinearMap.fst ℝ E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖x.1‖ ≤ 1 * max ‖x.1‖ ‖x.2‖
  simpa only [one_mul] using le_max_left ‖x.1‖ ‖x.2‖

theorem norm_sndCLM_le (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ‖ContinuousLinearMap.snd ℝ E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖x.2‖ ≤ 1 * max ‖x.1‖ ‖x.2‖
  simpa only [one_mul] using le_max_right ‖x.1‖ ‖x.2‖

theorem jet_comp_linear_bound {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (x : E) {B : ℝ} (hB : 0 ≤ B) (m : ℕ)
    (hb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k f (L x)‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B := by
  intro k hk
  have hl := norm_jet_comp_linear isOpen_univ hf.contDiffOn L (mem_univ (L x)) k
  exact hl.trans ((mul_le_mul (hb k hk) (pow_le_one₀ (norm_nonneg _) hL)
    (by positivity) hB).trans_eq (mul_one B))

/-- Slot: an abbreviation for `PhaseCalculus.Slot`. -/
abbrev Slot := PhaseCalculus.Slot
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- Slot R, given by `(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.fst ℝ Slow
(ℝ × ℝ))`. -/
noncomputable def slotR : Slot →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.fst ℝ Slow (ℝ × ℝ))
/-- Slot Z, given by `(ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ ×
ℝ)).comp (ContinuousLinearMap.fst ℝ Slow (ℝ × ℝ)))`. -/
noncomputable def slotZ : Slot →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.fst ℝ Slow (ℝ × ℝ)))
/-- Slot theta, given by `(ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Slow
(ℝ × ℝ))`. -/
noncomputable def slotTheta : Slot →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Slow (ℝ × ℝ))
/-- Slot V, given by `(ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Slow (ℝ ×
ℝ))`. -/
noncomputable def slotV : Slot →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Slow (ℝ × ℝ))

theorem norm_slotV_le : ‖slotV‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  rw [one_mul]
  exact (le_max_right ‖x.2.1‖ ‖x.2.2‖).trans (le_max_right ‖x.1‖ ‖x.2‖)

/-- Phase linear, given by `p • slotTheta + (pz / ε) • slotZ + x0 • slotR`. -/
noncomputable def phaseLinear (ε p pz x0 : ℝ) : Slot →L[ℝ] ℝ :=
  p • slotTheta + (pz / ε) • slotZ + x0 • slotR

theorem norm_phaseLinear_le (ε p pz x0 : ℝ) :
    ‖phaseLinear ε p pz x0‖ ≤ |p| + |pz / ε| + |x0| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro q
  have hr : |q.1.1| ≤ ‖q‖ := (le_max_left ‖q.1.1‖ ‖q.1.2‖).trans (le_max_left _ _)
  have hz : |q.1.2.1| ≤ ‖q‖ :=
    (le_max_left ‖q.1.2.1‖ ‖q.1.2.2‖).trans ((le_max_right ‖q.1.1‖ ‖q.1.2‖).trans (le_max_left _ _))
  have hθ : |q.2.1| ≤ ‖q‖ := (le_max_left ‖q.2.1‖ ‖q.2.2‖).trans (le_max_right _ _)
  change |p * q.2.1 + (pz / ε) * q.1.2.1 + x0 * q.1.1| ≤ _
  calc
    _ ≤ |p| * |q.2.1| + |pz / ε| * |q.1.2.1| + |x0| * |q.1.1| := by
      simpa only [abs_mul] using (abs_add_le (p * q.2.1 + (pz / ε) * q.1.2.1) (x0 * q.1.1)).trans
        (add_le_add_left (abs_add_le _ _) _)
    _ ≤ |p| * ‖q‖ + |pz / ε| * ‖q‖ + |x0| * ‖q‖ := by gcongr
    _ = _ := by ring

/-- All jets of the exact phase (26) are bounded directly from genuine base
profile jets. The only inverse fast scale is the displayed `pz/ε` term. -/
theorem phase_slot_jet_bound (ε p pz x0 : ℝ) {F G : Slow → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (q : Slot) (m : ℕ)
    {M B : ℝ} (hM : 1 ≤ M) (hq : ‖q‖ ≤ M) (hB : 0 ≤ B)
    (hFb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k F q.1‖ ≤ B)
    (hGb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k G q.1‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (PhaseCalculus.phase ε p pz x0 F G) q‖ ≤
      (|p| + |pz / ε| + |x0|) * M + (2 : ℝ) ^ m * M * ((|p| + |pz|) * B) := by
  let L : Slot →L[ℝ] Slow := ContinuousLinearMap.fst ℝ Slow (ℝ × ℝ)
  let A : Slot → ℝ := fun y => p * F y.1 + pz * G y.1
  have hFl : ContDiff ℝ ∞ (F ∘ L) := hF.comp L.contDiff
  have hGl : ContDiff ℝ ∞ (G ∘ L) := hG.comp L.contDiff
  have hA : ContDiff ℝ ∞ A := (contDiff_const.mul hFl).add (contDiff_const.mul hGl)
  have hFbl := jet_comp_linear_bound hF L (norm_fstCLM_le _ _) q hB m hFb
  have hGbl := jet_comp_linear_bound hG L (norm_fstCLM_le _ _) q hB m hGb
  have hAb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k A q‖ ≤ (|p| + |pz|) * B := by
    intro k hk
    change ‖iteratedFDeriv ℝ k (fun y => p * (F ∘ L) y + pz * (G ∘ L) y) q‖ ≤ _
    rw [fun_iteratedFDeriv_add_apply ((contDiff_const.mul hFl).contDiffAt.of_le (nat_le_infty k))
      ((contDiff_const.mul hGl).contDiffAt.of_le (nat_le_infty k))]
    apply (norm_add_le _ _).trans
    rw [norm_jet_const_mul hFl q p k, norm_jet_const_mul hGl q pz k]
    calc
      _ ≤ |p| * B + |pz| * B := add_le_add
        (mul_le_mul_of_nonneg_left (hFbl k hk) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hGbl k hk) (abs_nonneg _))
      _ = _ := by ring
  have hVb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k slotV q‖ ≤ M := by
    intro k hk
    simpa only [one_mul] using linear_jet_bound slotV q hM hq zero_le_one norm_slotV_le k
  have he : PhaseCalculus.phase ε p pz x0 F G = fun y => phaseLinear ε p pz x0 y - slotV y * A y :=
      rfl
  intro k hk
  rw [he]
  simp only [sub_eq_add_neg]
  rw [fun_iteratedFDeriv_add_apply ((phaseLinear ε p pz x0).contDiff.contDiffAt.of_le (nat_le_infty
      k))
    ((slotV.contDiff.mul hA).neg.contDiffAt.of_le (nat_le_infty k))]
  have hneg : iteratedFDeriv ℝ k (fun y : Slot => -(slotV y * A y)) q =
      -iteratedFDeriv ℝ k (fun y : Slot => slotV y * A y) q :=
    iteratedFDeriv_neg_apply
  rw [hneg]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  exact add_le_add
    (linear_jet_bound (phaseLinear ε p pz x0) q hM hq (by
        positivity) (norm_phaseLinear_le _ _ _ _) k)
    (pointwise_product_jet_bound slotV.contDiff hA q hk (by linarith) (by positivity) hVb hAb)

theorem pointwise_composition_jet_bound {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E)
    (m : ℕ) {B D : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ B)
    (hfb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i f x‖ ≤ D) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ (m.factorial : ℝ) * B * D ^ m := by
  intro k hk
  have he := norm_iteratedFDeriv_comp_le hg hf (nat_le_infty k) x
    (fun i hi => hgb i (hi.trans hk))
    (fun i hi him => (hfb i hi (him.trans hk)).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  have hfac : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hk
  exact he.trans (mul_le_mul (mul_le_mul_of_nonneg_right hfac hB)
    (pow_le_pow_right₀ hD hk) (by positivity) (by positivity))

theorem norm_jet_linear_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (L : F →L[ℝ] G) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (L ∘ f) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k f x‖ := by
  rw [L.iteratedFDeriv_comp_left (hf.contDiffAt.of_le (nat_le_infty k)) le_rfl]
  exact L.norm_compContinuousMultilinearMap_le _

/-- Lift XY as an element of `LiftPoint →L[ℝ] Plane`. -/
noncomputable def liftXY : LiftPoint →L[ℝ] Plane :=
  (((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ)))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ)))))).comp
    (ContinuousLinearMap.fst ℝ ChartPoint Plane)

/-- Lift ZT as an element of `LiftPoint →L[ℝ] Plane`. -/
noncomputable def liftZT : LiftPoint →L[ℝ] Plane :=
  (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))))).prod
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × (ℝ × ℝ)))).comp
    (ContinuousLinearMap.fst ℝ ChartPoint Plane)

@[simp] theorem liftXY_apply (y : LiftPoint) : liftXY y = (y.1.2.1, y.1.2.2.1) := rfl
@[simp] theorem liftZT_apply (y : LiftPoint) : liftZT y = (y.1.2.2.2, y.1.1) := rfl

theorem norm_liftXY_le : ‖liftXY‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro y
  rw [one_mul]
  exact max_le
    ((le_max_left ‖y.1.2.1‖ ‖y.1.2.2‖).trans ((le_max_right ‖y.1.1‖ ‖y.1.2‖).trans (le_max_left _
        _)))
    ((le_max_left ‖y.1.2.2.1‖ ‖y.1.2.2.2‖).trans
      ((le_max_right ‖y.1.2.1‖ ‖y.1.2.2‖).trans ((le_max_right ‖y.1.1‖ ‖y.1.2‖).trans (le_max_left
          _ _))))

theorem norm_liftZT_le : ‖liftZT‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro y
  rw [one_mul]
  exact max_le
    ((le_max_right ‖y.1.2.2.1‖ ‖y.1.2.2.2‖).trans
      ((le_max_right ‖y.1.2.1‖ ‖y.1.2.2‖).trans ((le_max_right ‖y.1.1‖ ‖y.1.2‖).trans (le_max_left
          _ _))))
    ((le_max_left ‖y.1.1‖ ‖y.1.2‖).trans (le_max_left _ _))

/-- Embed polar, given by `((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] Plane)).prod
((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] ℝ))`. -/
noncomputable def embedPolar : Plane →L[ℝ] Slot :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] Plane)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] ℝ))

theorem norm_embedPolar_le : ‖embedPolar‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro y
  simp [embedPolar, Prod.norm_def, Real.norm_eq_abs, abs_nonneg]

/-- Slot linear as an element of `LiftPoint →L[ℝ] Slot`. -/
noncomputable def slotLinear (ci : ℝ) : LiftPoint →L[ℝ] Slot :=
  ((0 : LiftPoint →L[ℝ] ℝ).prod liftZT).prod
    ((0 : LiftPoint →L[ℝ] ℝ).prod
      ((ci⁻¹ • etaCoordinate).comp (ContinuousLinearMap.snd ℝ ChartPoint Plane)))

/-- Slot constant, given by `((0, (0, 0)), (0, (r0 - etaCoordinate center) / ci))`. -/
noncomputable def slotConstant (ci : ℝ) (center : Plane) (r0 : ℝ) : Slot :=
  ((0, (0, 0)), (0, (r0 - etaCoordinate center) / ci))

/-- The actual native slot coordinates, using a chosen smooth polar chart. -/
noncomputable def slotMap (κ : Plane → Plane) (ci : ℝ) (center : Plane) (r0 : ℝ)
    (y : LiftPoint) : Slot := embedPolar (κ (liftXY y)) + slotLinear ci y + slotConstant ci center
        r0

theorem slotMap_formula (κ : Plane → Plane) (ci : ℝ) (center : Plane) (r0 : ℝ) (y : LiftPoint) :
    slotMap κ ci center r0 y =
      (((κ (liftXY y)).1, (y.1.2.2.2, y.1.1)),
        ((κ (liftXY y)).2, (etaCoordinate (y.2 - center) + r0) / ci)) := by
  simp only [slotMap, embedPolar, slotLinear, slotConstant]
  ext <;> simp [liftZT, map_sub, div_eq_mul_inv]
  ring

theorem slotMap_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    (ci : ℝ) (center : Plane) (r0 : ℝ) : ContDiff ℝ ∞ (slotMap κ ci center r0) :=
  ((embedPolar.contDiff.comp (hκ.comp liftXY.contDiff)).add (slotLinear ci).contDiff).add
      contDiff_const

theorem norm_slotLinear_le (ci : ℝ) : ‖slotLinear ci‖ ≤ 1 + |ci⁻¹| * ‖etaCoordinate‖ := by
  have hcoef : 0 ≤ |ci⁻¹| * ‖etaCoordinate‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro y
  have hzt : ‖liftZT y‖ ≤ ‖y‖ :=
    ((liftZT.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg y) norm_liftZT_le))
  have he : |ci⁻¹ * etaCoordinate y.2| ≤ (|ci⁻¹| * ‖etaCoordinate‖) * ‖y‖ := by
    rw [abs_mul]
    calc
      _ ≤ |ci⁻¹| * (‖etaCoordinate‖ * ‖y.2‖) :=
        mul_le_mul_of_nonneg_left (etaCoordinate.le_opNorm y.2) (abs_nonneg _)
      _ ≤ |ci⁻¹| * (‖etaCoordinate‖ * ‖y‖) := by gcongr; exact le_max_right _ _
      _ = _ := by ring
  change max (max ‖(0 : ℝ)‖ ‖liftZT y‖) (max ‖(0 : ℝ)‖ |ci⁻¹ * etaCoordinate y.2|) ≤ _
  simp only [norm_zero]
  rw [max_eq_right (norm_nonneg (liftZT y)), max_eq_right (abs_nonneg (ci⁻¹ * etaCoordinate y.2))]
  apply max_le
  · exact hzt.trans (by nlinarith [norm_nonneg y])
  · exact he.trans (by nlinarith [norm_nonneg y])

theorem positive_jet_affine_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (c : F)
    (x : E) {k : ℕ} (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (fun y => L y + c) x‖ ≤ ‖L‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [fun_iteratedFDeriv_add_apply L.contDiff.contDiffAt contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero]
  exact norm_positive_jet_linear_le L x (by omega)

theorem slotMap_positive_jet_bound {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    (ci : ℝ) (center : Plane) (r0 : ℝ) (y : LiftPoint) (m : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hκb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i κ (liftXY y)‖ ≤ K) :
    ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i (slotMap κ ci center r0) y‖ ≤
      K + 1 + |ci⁻¹| * ‖etaCoordinate‖ := by
  have hbase : ContDiff ℝ ∞ (κ ∘ liftXY) := hκ.comp liftXY.contDiff
  have hbaseb := jet_comp_linear_bound hκ liftXY norm_liftXY_le y hK m hκb
  intro i hi him
  have he : slotMap κ ci center r0 = fun y => embedPolar (κ (liftXY y)) +
      (slotLinear ci y + slotConstant ci center r0) := by funext z; simp only [slotMap, add_assoc]
  have hleftsmooth : ContDiff ℝ ∞ (fun z : LiftPoint => embedPolar (κ (liftXY z))) :=
    embedPolar.contDiff.comp hbase
  have hrightsmooth : ContDiff ℝ ∞ (fun z : LiftPoint => slotLinear ci z + slotConstant ci center
      r0) :=
    (slotLinear ci).contDiff.add contDiff_const
  rw [he, fun_iteratedFDeriv_add_apply
    (hleftsmooth.contDiffAt.of_le (nat_le_infty i))
    (hrightsmooth.contDiffAt.of_le (nat_le_infty i))]
  apply (norm_add_le _ _).trans
  have hleft := norm_jet_linear_comp hbase embedPolar y i
  have hright := (positive_jet_affine_bound (slotLinear ci) (slotConstant ci center r0) y hi).trans
    (norm_slotLinear_le ci)
  have hleft' : ‖iteratedFDeriv ℝ i (embedPolar ∘ κ ∘ liftXY) y‖ ≤ K :=
    hleft.trans ((mul_le_mul norm_embedPolar_le (hbaseb i him) (norm_nonneg _)
        zero_le_one).trans_eq (one_mul K))
  simpa only [add_assoc, Function.comp_def] using add_le_add hleft' hright

theorem slotMap_physical (κ : Plane → Plane) (h : ℝ) (n : ℕ)
    (center : Plane) (r0 : ℝ) (p : SpaceTime) :
    slotMap κ (ChartScales.timeCoefficient h n) center r0 (physicalLift h n p) =
      (((κ (scaledRadial n p)).1,
        (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * p.2 2, (1 - p.1) / ChartScales.Q n)),
       ((κ (scaledRadial n p)).2, slotTime h n center r0 p)) := by
  rw [slotMap_formula]
  have hxy : liftXY (physicalLift h n p) = scaledRadial n p := by
    simp [liftXY_apply, physicalLift, physicalChart, chartLinear_apply, scaledRadial,
      radialProjection_apply, smul_eq_mul]
  rw [hxy]
  ext <;> simp [physicalLift, physicalChart, chartLinear_apply, slotTime,
    Real.rpow_neg_one, div_eq_mul_inv]
  ring

/-- Composition of (26) with the actual native slot map. This is the phase
whose exponential is used in the physical carrier estimate. -/
noncomputable def liftedPhase (κ : Plane → Plane) (h : ℝ) (n : ℕ)
    (center : Plane) (r0 p pz x0 : ℝ) (F G : Slow → ℝ) : LiftPoint → ℝ :=
  PhaseCalculus.phase (ChartScales.epsilon h n) p pz x0 F G ∘
    slotMap κ (ChartScales.timeCoefficient h n) center r0

theorem liftedPhase_jet_bound {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    (h : ℝ) (n : ℕ) (center : Plane) (r0 p pz x0 : ℝ) {F G : Slow → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (y : LiftPoint) (m : ℕ)
    {K M B : ℝ} (hK : 0 ≤ K) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hκb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i κ (liftXY y)‖ ≤ K)
    (hpoint : ‖slotMap κ (ChartScales.timeCoefficient h n) center r0 y‖ ≤ M)
    (hFb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F
      (slotMap κ (ChartScales.timeCoefficient h n) center r0 y).1‖ ≤ B)
    (hGb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i G
      (slotMap κ (ChartScales.timeCoefficient h n) center r0 y).1‖ ≤ B) :
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (liftedPhase κ h n center r0 p pz x0 F G) y‖ ≤
      (m.factorial : ℝ) *
        ((|p| + |pz / ChartScales.epsilon h n| + |x0|) * M +
          (2 : ℝ) ^ m * M * ((|p| + |pz|) * B)) *
        (K + 1 + |(ChartScales.timeCoefficient h n)⁻¹| * ‖etaCoordinate‖) ^ m := by
  apply pointwise_composition_jet_bound (slotMap_smooth hκ _ _ _)
    (PhaseCalculus.contDiff_phase _ _ _ _ _ _ hF hG) y m (by positivity)
    (by
        have := mul_nonneg (abs_nonneg ((ChartScales.timeCoefficient h n)⁻¹)) (norm_nonneg
            etaCoordinate); linarith)
  · exact phase_slot_jet_bound _ _ _ _ hF hG _ m hM hpoint hB hFb hGb
  · exact slotMap_positive_jet_bound hκ _ _ _ y m hK hκb

theorem slotMap_norm_bound (κ : Plane → Plane) (ci : ℝ) (center : Plane) (r0 : ℝ)
    (y : LiftPoint) {K Z V : ℝ} (hK : 0 ≤ K) (hZ : 0 ≤ Z) (hV : 0 ≤ V)
    (hk : ‖κ (liftXY y)‖ ≤ K) (hz : ‖liftZT y‖ ≤ Z)
    (hv : |(etaCoordinate (y.2 - center) + r0) / ci| ≤ V) :
    ‖slotMap κ ci center r0 y‖ ≤ K + Z + V := by
  rw [slotMap_formula]
  have hk0 := (le_max_left ‖(κ (liftXY y)).1‖ ‖(κ (liftXY y)).2‖).trans hk
  have hk1 := (le_max_right ‖(κ (liftXY y)).1‖ ‖(κ (liftXY y)).2‖).trans hk
  change max (max ‖(κ (liftXY y)).1‖ ‖liftZT y‖)
    (max ‖(κ (liftXY y)).2‖ |(etaCoordinate (y.2 - center) + r0) / ci|) ≤ _
  exact max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))

theorem Q_inv_ge_one (n : ℕ) : 1 ≤ ChartScales.Q n ^ (-1 : ℝ) := by
  have h := Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n)
    (ChartScales.Q_le_one n) (show (-1 : ℝ) ≤ 0 by norm_num)
  simpa only [Real.rpow_zero] using h

theorem epsilon_inv_le {h : ℝ} (hh : h ≤ 1) (n : ℕ) :
    (ChartScales.epsilon h n)⁻¹ ≤ ChartScales.Q n ^ (-1 : ℝ) := by
  have he : (ChartScales.epsilon h n)⁻¹ = ChartScales.Q n ^ (-h) := by
    simp [ChartScales.epsilon, Real.rpow_neg (ChartScales.Q_pos n).le]
  rw [he]
  exact Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by
      linarith)

/-- The exact phase (26) has one fixed inverse-`Q` loss. The integer degree
of the slow factor may grow with the base profile class; it affects no power
of `Q`. Slot translations and the choice of polar chart are uniform. -/
theorem liftedPhase_power_bound {h K Z r0 P B d : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hK : 1 ≤ K)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (hd : 0 ≤ d) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ κ : Plane → Plane, ContDiff ℝ ∞ κ →
      ∀ n : ℕ, 4 ≤ n → ∀ (center : Plane) (p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P → ∀ (F G : Slow → ℝ),
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → ∀ y : LiftPoint,
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i κ (liftXY y)‖ ≤ K) →
      ‖liftZT y‖ ≤ Z → |etaCoordinate (y.2 - center)| ≤ r0 →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F
        (slotMap κ (ChartScales.timeCoefficient h n) center r0 y).1‖ ≤ B * ChartScales.S n ^ d) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i G
        (slotMap κ (ChartScales.timeCoefficient h n) center r0 y).1‖ ≤ B * ChartScales.S n ^ d) →
      ∀ i ≤ m, ‖iteratedFDeriv ℝ i (liftedPhase κ h n center r0 p pz x0 F G) y‖ ≤
        C * ChartScales.S n ^ (d + (m : ℝ) + 1) * ChartScales.Q n ^ (-1 : ℝ) := by
  let M0 := K + Z + 2 * r0 * ChartScales.Tg + 1
  let D0 := K + 1 + ChartScales.Tg * ‖etaCoordinate‖
  let C0 := (m.factorial : ℝ) * (3 + (2 : ℝ) ^ (m + 1)) * P * M0 * B * D0 ^ m
  have hM0 : 1 ≤ M0 := by dsimp [M0]; nlinarith [ChartScales.Tg_pos]
  have hD0 : 1 ≤ D0 := by dsimp [D0]; nlinarith [ChartScales.Tg_pos, norm_nonneg etaCoordinate]
  refine ⟨max 1 C0, le_max_left _ _, ?_⟩
  intro κ hκ n hn center p pz x0 hp hpz hx0 F G hF hG y hκb hz hslot hFb hGb i hi
  have hS := S_ge_one (show 1 ≤ n by omega)
  have hS0 := ChartScales.S_pos (show 1 ≤ n by omega)
  have hQ := ChartScales.Q_pos n
  have hTg := ChartScales.Tg_pos
  have hQ1 := Q_inv_ge_one n
  have hSd : 1 ≤ ChartScales.S n ^ d := Real.one_le_rpow hS hd
  have hbase : 1 ≤ B * ChartScales.S n ^ d := by nlinarith
  have hM : 1 ≤ M0 * ChartScales.S n := by nlinarith
  have hci : |(ChartScales.timeCoefficient h n)⁻¹| ≤ ChartScales.Tg * ChartScales.S n := by
    rw [abs_of_pos (inv_pos.mpr (ChartScales.timeCoefficient_pos h n))]
    exact ChartScales.timeCoefficient_inv_upper h hh hn
  have hv : |(etaCoordinate (y.2 - center) + r0) / ChartScales.timeCoefficient h n| ≤
      2 * r0 * ChartScales.Tg * ChartScales.S n := by
    rw [abs_div, abs_of_pos (ChartScales.timeCoefficient_pos h n), div_eq_mul_inv]
    have he : |etaCoordinate (y.2 - center) + r0| ≤ 2 * r0 := by
      have ht := abs_add_le (etaCoordinate (y.2 - center)) r0
      rw [abs_of_nonneg hr0] at ht
      linarith
    calc
      _ ≤ (2 * r0) * (ChartScales.Tg * ChartScales.S n) :=
        mul_le_mul he (ChartScales.timeCoefficient_inv_upper h hh hn)
          (inv_nonneg.mpr (ChartScales.timeCoefficient_pos h n).le) (by positivity)
      _ = _ := by ring
  have hpoint : ‖slotMap κ (ChartScales.timeCoefficient h n) center r0 y‖ ≤ M0 * ChartScales.S n :=
      by
    have hκ0 : ‖κ (liftXY y)‖ ≤ K := by
        simpa only [norm_iteratedFDeriv_zero] using hκb 0 (Nat.zero_le _)
    apply (slotMap_norm_bound κ _ center r0 y (by linarith) hZ (by positivity) hκ0 hz hv).trans
    dsimp [M0]
    nlinarith
  have hlin : |p| + |pz / ChartScales.epsilon h n| + |x0| ≤
      3 * P * ChartScales.Q n ^ (-1 : ℝ) := by
    have hP0 : 0 ≤ P := by linarith
    have hp' := hp.trans (le_mul_of_one_le_right hP0 hQ1)
    have hx' := hx0.trans (le_mul_of_one_le_right hP0 hQ1)
    have hz' : |pz / ChartScales.epsilon h n| ≤ P * ChartScales.Q n ^ (-1 : ℝ) := by
      rw [abs_div, abs_of_pos (ChartScales.epsilon_pos h n), div_eq_mul_inv]
      exact mul_le_mul hpz (epsilon_inv_le hh1 n)
        (inv_nonneg.mpr (ChartScales.epsilon_pos h n).le) hP0
    linarith
  have hsum : |p| + |pz| ≤ 2 * P := by linarith
  have hD : K + 1 + |(ChartScales.timeCoefficient h n)⁻¹| * ‖etaCoordinate‖ ≤
      D0 * ChartScales.S n := by
    have he := mul_le_mul_of_nonneg_right hci (norm_nonneg etaCoordinate)
    dsimp [D0]
    nlinarith
  have he := liftedPhase_jet_bound hκ h n center r0 p pz x0 hF hG y m
    (by linarith) hM (by linarith) hκb hpoint hFb hGb i hi
  have hinside :
      (|p| + |pz / ChartScales.epsilon h n| + |x0|) * (M0 * ChartScales.S n) +
        (2 : ℝ) ^ m * (M0 * ChartScales.S n) * ((|p| + |pz|) * (B * ChartScales.S n ^ d)) ≤
      (3 + (2 : ℝ) ^ (m + 1)) * P * (M0 * ChartScales.S n) *
        (B * ChartScales.S n ^ d) * ChartScales.Q n ^ (-1 : ℝ) := by
    calc
      _ ≤ (3 * P * ChartScales.Q n ^ (-1 : ℝ)) * (M0 * ChartScales.S n) +
          (2 : ℝ) ^ m * (M0 * ChartScales.S n) * ((2 * P) * (B * ChartScales.S n ^ d)) := by
        gcongr
      _ ≤ ((3 * P * ChartScales.Q n ^ (-1 : ℝ)) * (M0 * ChartScales.S n)) * (B * ChartScales.S n ^
          d) +
          ((2 : ℝ) ^ m * (M0 * ChartScales.S n) * ((2 * P) * (B * ChartScales.S n ^ d))) *
            ChartScales.Q n ^ (-1 : ℝ) := by
        apply add_le_add
        · exact le_mul_of_one_le_right (by positivity) hbase
        · exact le_mul_of_one_le_right (by positivity) hQ1
      _ = _ := by rw [pow_succ]; ring
  have hmajor : ‖iteratedFDeriv ℝ i (liftedPhase κ h n center r0 p pz x0 F G) y‖ ≤
      (m.factorial : ℝ) *
        ((3 + (2 : ℝ) ^ (m + 1)) * P * (M0 * ChartScales.S n) * (B * ChartScales.S n ^ d) *
          ChartScales.Q n ^ (-1 : ℝ)) * (D0 * ChartScales.S n) ^ m := by
    apply he.trans
    gcongr
  have hpowers : ChartScales.S n * ChartScales.S n ^ d * ChartScales.S n ^ m =
      ChartScales.S n ^ (d + (m : ℝ) + 1) := by
    calc
      _ = ChartScales.S n ^ (1 : ℝ) * ChartScales.S n ^ d * ChartScales.S n ^ (m : ℝ) := by
        rw [Real.rpow_one, Real.rpow_natCast]
      _ = _ := by
        rw [← Real.rpow_add hS0, ← Real.rpow_add hS0]
        congr 1
        ring
  calc
    _ ≤ (m.factorial : ℝ) *
        ((3 + (2 : ℝ) ^ (m + 1)) * P * (M0 * ChartScales.S n) * (B * ChartScales.S n ^ d) *
          ChartScales.Q n ^ (-1 : ℝ)) * (D0 * ChartScales.S n) ^ m := hmajor
    _ = C0 * ChartScales.S n ^ (d + (m : ℝ) + 1) * ChartScales.Q n ^ (-1 : ℝ) := by
      rw [mul_pow]
      dsimp [C0]
      calc
        _ = ((m.factorial : ℝ) * (3 + (2 : ℝ) ^ (m + 1)) * P * M0 * B * D0 ^ m) *
            (ChartScales.S n * ChartScales.S n ^ d * ChartScales.S n ^ m) * ChartScales.Q n ^ (-1 :
                ℝ) := by
                ring
        _ = _ := by rw [hpowers]
    _ ≤ _ := by gcongr; exact le_max_right 1 C0

/-- Wave loss, given by `graphLoss m + (m : ℝ) + h * (m : ℝ) / 2 + 1`. -/
noncomputable def waveLoss (h : ℝ) (m : ℕ) : ℝ :=
  graphLoss m + (m : ℝ) + h * (m : ℝ) / 2 + 1

theorem carrier_weight_identity {q S : ℝ} (hq : 0 < q) (hS : 0 < S)
    (C A B H g d e E : ℝ) (m : ℕ) :
    C * (A * q ^ g * S ^ d) * (B * S ^ e * q ^ (-1 : ℝ)) ^ m * (1 + 2 * H) ^ m * q ^ (-E) =
      (C * A * B ^ m * (1 + 2 * H) ^ m) * S ^ (d + e * (m : ℝ)) * q ^ (g - E - (m : ℝ)) := by
  have hs : S ^ d * (S ^ e) ^ m = S ^ (d + e * (m : ℝ)) := by
    rw [← Real.rpow_mul_natCast hS.le, ← Real.rpow_add hS]
  have hq' : q ^ g * (q ^ (-1 : ℝ)) ^ m * q ^ (-E) = q ^ (g - E - (m : ℝ)) := by
    rw [← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq, ← Real.rpow_add hq]
    congr 1
    ring
  calc
    _ = (C * A * B ^ m * (1 + 2 * H) ^ m) *
        (S ^ d * (S ^ e) ^ m) * (q ^ g * (q ^ (-1 : ℝ)) ^ m * q ^ (-E)) := by
      rw [mul_pow, mul_pow]
      ring
    _ = _ := by rw [hs, hq']

/-- The complete fixed loss for waves with the exact carrier frequency.
Amplitude gain `g`, harmonic cutoff `H`, and slow degrees `d,e` affect only
the final constant. The phase class is supplied by `liftedPhase_power_bound`. -/
theorem carrier_class_physical_bound {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (ha : 0 < a) (m : ℕ) (g d e A B H : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (he : 0 ≤ e) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (amp : LiftPoint → ℂ) (Φ : LiftPoint → ℝ) (j : ℤ),
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ Φ → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (physicalLift h n p)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ d) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i Φ (physicalLift h n p)‖ ≤
        B * ChartScales.S n ^ e * ChartScales.Q n ^ (-1 : ℝ)) →
      ‖iteratedFDeriv ℝ m
        ((fun y => amp y * character ((ChartScales.carrier h n : ℝ) * (j : ℝ)) (Φ y)) ∘
          physicalLift h n) p‖ ≤ C * q ^ (g - waveLoss h m) := by
  obtain ⟨C, hC, hbound⟩ := carrier_graph_jet_bound (b := b) hh hh1 ha m
  obtain ⟨D, hD, hslow⟩ := slow_power_absorption (d + e * (m : ℝ))
  let W := C * A * B ^ m * (1 + 2 * H) ^ m
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨W * D * 2 ^ |g - waveLoss h m|, by positivity, ?_⟩
  intro n hn p hp ht q hq hlo hhi amp Φ j hamp hΦ hj hab hph
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have hSb : 1 ≤ ChartScales.S n ^ e := Real.one_le_rpow (S_ge_one (by omega)) he
  have hQ1 := Q_inv_ge_one n
  have hphaseB : 1 ≤ B * ChartScales.S n ^ e * ChartScales.Q n ^ (-1 : ℝ) := by
    have : 1 ≤ B * ChartScales.S n ^ e := by nlinarith
    nlinarith
  have hAmp0 : 0 ≤ A * ChartScales.Q n ^ g * ChartScales.S n ^ d := by positivity
  have hb := hbound n hn p hp ht amp Φ hamp hΦ _ _ H j hAmp0 hphaseB hj hab hph
  rw [carrier_weight_identity hQ hS] at hb
  change _ ≤ W * ChartScales.S n ^ (d + e * (m : ℝ)) *
    ChartScales.Q n ^ (g - (graphLoss m + h * (m : ℝ) / 2) - (m : ℝ)) at hb
  have hpow : -1 + (g - (graphLoss m + h * (m : ℝ) / 2) - (m : ℝ)) = g - waveLoss h m := by
    unfold waveLoss
    ring
  calc
    _ ≤ W * (D * ChartScales.Q n ^ (-1 : ℝ)) *
        ChartScales.Q n ^ (g - (graphLoss m + h * (m : ℝ) / 2) - (m : ℝ)) := by
      apply hb.trans
      gcongr
      exact hslow n
    _ = (W * D) * ChartScales.Q n ^ (g - waveLoss h m) := by
      calc
        _ = (W * D) * (ChartScales.Q n ^ (-1 : ℝ) *
            ChartScales.Q n ^ (g - (graphLoss m + h * (m : ℝ) / 2) - (m : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hQ, hpow]
    _ ≤ (W * D) * (2 ^ |g - waveLoss h m| * q ^ (g - waveLoss h m)) :=
      mul_le_mul_of_nonneg_left (comparable_rpow hQ hq hlo hhi _) (mul_nonneg hW hD.le)
    _ = _ := by ring

/-- The four actual polar chart extensions supply one common constant for
all normalized Cartesian phase derivatives; a sector always exists. -/
theorem physical_polar_chart_available {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, ∀ p : SpaceTime, scaledRadial n p ∈ annulus a b →
      ∃ j : PolarCharts.Index,
        scaledRadial n p ∈ PolarCharts.sector a b j ∧
        ContDiff ℝ ∞ (PolarCharts.chart a j) ∧
        (∀ k ≤ m, ‖iteratedFDeriv ℝ k (PolarCharts.chart a j) (scaledRadial n p)‖ ≤ K) ∧
        PolarCharts.polar (PolarCharts.chart a j (scaledRadial n p)) = scaledRadial n p := by
  obtain ⟨K, hK, hbound⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  refine ⟨K, hK, ?_⟩
  intro n p hp
  obtain ⟨j, hj⟩ := PolarCharts.annulus_covered ha hp
  exact ⟨j, hj, PolarCharts.chart_contDiff ha j,
    (fun k hk => hbound j k hk _ hp.1),
    PolarCharts.polar_chart ha j (PolarCharts.sector_subset_chartDomain ha j hj)⟩

theorem liftXY_physicalLift (h : ℝ) (n : ℕ) (p : SpaceTime) :
    liftXY (physicalLift h n p) = scaledRadial n p := by
  simp [liftXY_apply, physicalLift, physicalChart, chartLinear_apply, scaledRadial,
    radialProjection_apply, smul_eq_mul]

theorem liftedPhase_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    (h : ℝ) (n : ℕ) (center : Plane) (r0 p pz x0 : ℝ) {F G : Slow → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (liftedPhase κ h n center r0 p pz x0 F G) :=
  (PhaseCalculus.contDiff_phase _ _ _ _ _ _ hF hG).comp (slotMap_smooth hκ _ _ _)

theorem character_phase_eq_harmonic (k : ℝ) (j : ℤ) (ε p pz x0 : ℝ)
    (F G : Slow → ℝ) (s : Slot) :
    character (k * (j : ℝ)) (PhaseCalculus.phase ε p pz x0 F G s) =
      PhaseCalculus.harmonic k j ε p pz x0 F G s := by
  unfold character phaseFactor PhaseCalculus.harmonic
  congr 1
  push_cast
  ring

/-- On a covering sector, the phase is the literal Cartesian realization
of (26), with `R=√(x²+y²)/√Q` and an actual local arctangent angle. -/
theorem liftedPhase_physical_formula {a b : ℝ} (ha : 0 < a)
    (chart : PolarCharts.Index) (h : ℝ) (n : ℕ) (center : Plane)
    (r0 p pz x0 : ℝ) (F G : Slow → ℝ) (w : SpaceTime)
    (hw : scaledRadial n w ∈ PolarCharts.sector a b chart) :
    let R := PolarCharts.radius (scaledRadial n w)
    let θ := Real.arctan ((PolarCharts.rotate chart (scaledRadial n w)).2 /
      (PolarCharts.rotate chart (scaledRadial n w)).1) + PolarCharts.offset chart
    let Z := ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2
    let T := (1 - w.1) / ChartScales.Q n
    liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G (physicalLift h n w) =
      p * θ + (pz / ChartScales.epsilon h n) * Z + x0 * R -
        slotTime h n center r0 w * (p * F (R, (Z, T)) + pz * G (R, (Z, T))) := by
  dsimp only
  unfold liftedPhase
  rw [Function.comp_apply, slotMap_physical,
    PolarCharts.chart_eq_localChart ha chart (PolarCharts.sector_subset_chartDomain ha chart hw),
    PolarCharts.localChart_apply]
  rfl

/-- All polar branches share the same physical bound for the actual phase
(26). No derivative hypothesis on the phase or on the native graph occurs:
only the stripped amplitude and base profiles have class hypotheses. -/
theorem native_carrier_physical_bound {h a b Z r0 P B dBase : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (hdBase : 0 ≤ dBase)
    (m : ℕ) (g dAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      ‖liftZT (physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (chart : PolarCharts.Index) (center : Plane) (p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P →
      |etaCoordinate (nativeGraph h n w - center)| ≤ r0 →
      ∀ (amp : LiftPoint → ℂ) (F G : Slow → ℝ) (j : ℤ),
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (physicalLift h n w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ dAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F
        (slotMap (PolarCharts.chart a chart) (ChartScales.timeCoefficient h n) center r0
          (physicalLift h n w)).1‖ ≤ B * ChartScales.S n ^ dBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i G
        (slotMap (PolarCharts.chart a chart) (ChartScales.timeCoefficient h n) center r0
          (physicalLift h n w)).1‖ ≤ B * ChartScales.S n ^ dBase) →
      ‖iteratedFDeriv ℝ m
        ((fun y => amp y * character ((ChartScales.carrier h n : ℝ) * (j : ℝ))
          (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G y)) ∘
          physicalLift h n) w‖ ≤ C * q ^ (g - waveLoss h m) := by
  obtain ⟨K, hK, hpolar⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  obtain ⟨BPhase, hBPhase, hphase⟩ :=
    liftedPhase_power_bound hh (show h ≤ 1 by linarith) hK hZ hr0 hP hB hdBase m
  obtain ⟨C, hC, hbound⟩ := carrier_class_physical_bound (b := b) hh hh1 ha m
    g dAmp (dBase + (m : ℝ) + 1) A BPhase H hA hBPhase (by positivity) hH
  refine ⟨C, hC, ?_⟩
  intro n hn w hw ht hz q hq hlo hhi chart center p pz x0 hp hpz hx0 hslot
    amp F G j hamp hF hG hj hab hFb hGb
  have hκ := PolarCharts.chart_contDiff ha chart
  have hκb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (PolarCharts.chart a chart)
      (liftXY (physicalLift h n w))‖ ≤ K := by
    intro i hi
    rw [liftXY_physicalLift]
    exact hpolar chart i hi _ hw.1
  apply hbound n hn w hw ht q hq hlo hhi amp
    (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G) j
    hamp (liftedPhase_smooth hκ _ _ _ _ _ _ _ hF hG) hj hab
  exact hphase (PolarCharts.chart a chart) hκ n hn center p pz x0 hp hpz hx0 F G hF hG
    (physicalLift h n w) hκb hz hslot hFb hGb

end NavierStokes.PhysicalGraphBounds
