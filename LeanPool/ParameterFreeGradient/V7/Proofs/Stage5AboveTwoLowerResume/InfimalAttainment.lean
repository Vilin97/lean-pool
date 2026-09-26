/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5ARepair.InfimalLocality
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AFinalRepair.OriginFrechet
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AGlobalC2.Calculus

/-!
Attainment and interior-radius bounds for the kernel's infimal-convolution minimizers.
-/

@[expose] public section

open scoped BigOperators

namespace V7.Stage5AboveTwoLowerResume

open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AFinalRepair
open Stage5AboveTwoLower

/-- Continuity of the literal finite-dimensional `ell_p` norm in the ambient
product topology. -/
lemma continuous_lpNorm {p : ℝ} (hp : 1 ≤ p) {d : ℕ} :
    Continuous (fun z : Point d ↦ lpNorm p z) := by
  let e : ENNReal := ENNReal.ofReal p
  let _ : Fact (1 ≤ e) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have hto : Continuous
      (fun z : Point d ↦ (WithLp.toLp e z : PiLp e (fun _ : Fin d ↦ ℝ))) :=
    PiLp.continuous_toLp e (fun _ : Fin d ↦ ℝ)
  have hn := continuous_norm.comp hto
  apply hn.congr
  intro z
  exact (O3.Stage2RouteC.lpNorm_eq_piLpNorm hp z).symm

/-- Closed `ell_p` balls are compact in the actual finite-dimensional ambient
topology used by the V7 carriers. -/
lemma isCompact_lpNorm_le {p chi : ℝ} (hp : 1 ≤ p) {d : ℕ} :
    IsCompact {v : Point d | lpNorm p v ≤ chi} := by
  have hclosed : IsClosed {v : Point d | lpNorm p v ≤ chi} :=
    isClosed_Iic.preimage (continuous_lpNorm hp)
  have hsubset : {v : Point d | lpNorm p v ≤ chi} ⊆
      Metric.closedBall 0 chi := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_lpNorm hp v).trans hv
  exact (isCompact_closedBall (0 : Point d) chi).of_isClosed_subset
    hclosed hsubset

/-- A function that is one-Lipschitz for the literal `ell_p` norm is
continuous in the ambient product topology. -/
lemma continuous_of_isOneLipschitz {p : ℝ} (hp : 1 ≤ p)
    {ell : Point d → ℝ} (hlip : IsOneLipschitz p ell) : Continuous ell := by
  let K : NNReal := ⟨lpAmbientConstant p d, lpAmbientConstant_nonneg p d⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) fun x y ↦ ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (hlip x y).trans (lpNorm_le_ambientConstant hp (x - y))

/-- Continuity of the concrete infimal cost follows from the frozen
one-Lipschitz input and continuity of the selected kernel. -/
lemma continuous_smoothingCost (kernel : SmoothingKernelData p d)
    {chi : ℝ} {ell : Point d → ℝ} (hp : 1 ≤ p)
    (hlip : IsOneLipschitz p ell) (hphi : Continuous kernel.phi)
    (x : Point d) : Continuous (smoothingCost kernel chi ell x) := by
  unfold smoothingCost
  exact ((continuous_of_isOneLipschitz hp hlip).comp
      (continuous_const.add continuous_id)).add
    (continuous_const.mul
      (hphi.comp (continuous_const_smul (1 / chi))))

/-- Monotonicity of the unnormalised finite-dimensional `ell_p` norms in the
exponent, proved in the literal `lpNorm` representation used by V7. -/
lemma lpNorm_le_lpNorm_of_exponent_le {r p : ℝ}
    (hr : 1 ≤ r) (hrp : r ≤ p) {d : ℕ} (x : Point d) :
    lpNorm p x ≤ lpNorm r x := by
  have hp : 1 ≤ p := hr.trans hrp
  by_cases hx : x = 0
  · subst x
    simp [O3.lpNorm_zero (lt_of_lt_of_le zero_lt_one hp),
      O3.lpNorm_zero (lt_of_lt_of_le zero_lt_one hr)]
  · let A : ℝ := lpNorm r x
    let y : Point d := (1 / A) • x
    have hA : 0 < A := O3.lpNorm_pos_of_ne_zero hx
    have hyr : lpNorm r y = 1 := by
      change O3.lpNorm r ((1 / A) • x) = 1
      rw [O3.Stage2RouteC.lpNorm_smul hr, abs_of_pos (one_div_pos.mpr hA)]
      change (1 / A) * A = 1
      field_simp [hA.ne']
    have hpower : O3.lpPower p y ≤ O3.lpPower r y := by
      unfold O3.lpPower
      apply Finset.sum_le_sum
      intro i _
      have hcoord : |y i| ≤ 1 := by
        have hi := norm_apply_le_lpNorm hr y i
        simpa [Real.norm_eq_abs, hyr] using hi
      exact Real.rpow_le_rpow_of_exponent_ge'
        (abs_nonneg (y i)) hcoord (by linarith) hrp
    have hpowerOne : O3.lpPower p y ≤ 1 := by
      calc
        O3.lpPower p y ≤ O3.lpPower r y := hpower
        _ = lpNorm r y ^ r :=
          (O3.Experimental.lpNorm_rpow_eq_lpPower (by linarith : r ≠ 0) y).symm
        _ = 1 := by rw [hyr, Real.one_rpow]
    have hyp : lpNorm p y ≤ 1 := by
      unfold lpNorm O3.lpNorm
      exact Real.rpow_le_one (O3.lpPower_nonneg p y) hpowerOne
        (by positivity)
    have hxy : A • y = x := by
      change A • ((1 / A) • x) = x
      rw [← mul_smul]
      field_simp [hA.ne']
      simp
    calc
      lpNorm p x = lpNorm p (A • y) := congrArg (lpNorm p) hxy.symm
      _ = A * lpNorm p y := by
        change O3.lpNorm p (A • y) = A * O3.lpNorm p y
        rw [O3.Stage2RouteC.lpNorm_smul hp, abs_of_pos hA]
      _ ≤ A := by nlinarith
      _ = lpNorm r x := rfl

/-- The concrete kernel has the required all-radii barrier once the standard
finite-dimensional monotonicity `‖u‖_p ≤ ‖u‖_r` for `r ≤ p` is available. -/
lemma lowerKernelPhi_radial_of_lpNorm_le {p r theta : ℝ}
    (hr : r ≠ 0) (htheta : 1 < theta) {d : ℕ}
    (hmono : ∀ u : Point d, lpNorm p u ≤ lpNorm r u) :
    ∀ u : Point d, 1 ≤ lpNorm p u →
      lpNorm p u < lowerKernelPhi r theta u := by
  intro u hu
  rw [lowerKernelPhi_eq_norm_power hr]
  have hbase : lpNorm p u ≤ lpNorm r u := hmono u
  have hexp : 1 < 2 * theta := by linarith
  have hself : lpNorm p u ≤ lpNorm p u ^ (2 * theta) := by
    rcases hu.eq_or_lt with heq | hlt
    · rw [← heq]
      simp
    · exact (Real.self_lt_rpow_of_one_lt hlt hexp).le
  have hpow : lpNorm p u ^ (2 * theta) ≤ lpNorm r u ^ (2 * theta) :=
    Real.rpow_le_rpow (O3.lpNorm_nonneg p u) hbase (by linarith)
  have hnonneg : 0 ≤ lpNorm r u ^ (2 * theta) :=
    Real.rpow_nonneg (O3.lpNorm_nonneg r u) _
  nlinarith

/-- Concrete all-radii barrier for the current `lowerKernelPhi`. -/
theorem lowerKernelPhi_radial {p r theta : ℝ}
    (hr : 1 ≤ r) (hrp : r ≤ p) (htheta : 1 < theta) {d : ℕ} :
    ∀ u : Point d, 1 ≤ lpNorm p u →
      lpNorm p u < lowerKernelPhi r theta u := by
  exact lowerKernelPhi_radial_of_lpNorm_le (by linarith : r ≠ 0) htheta
    (fun u ↦ lpNorm_le_lpNorm_of_exponent_le hr hrp u)

lemma self_lt_two_mul_rpow_of_three_four_lt {t a : ℝ}
    (ht : 3 / 4 < t) (ht1 : t ≤ 1) (ha : 0 ≤ a) (ha3 : a < 3) :
    t < 2 * t ^ a := by
  have ht0 : 0 < t := by linarith
  have hcubic : t ^ (3 : ℝ) ≤ t ^ a :=
    Real.rpow_le_rpow_of_exponent_ge' ht0.le ht1 ha ha3.le
  have hthree : t ^ (3 : ℝ) = t ^ (3 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hthree] at hcubic
  have htSq : 9 / 16 < t ^ (2 : ℕ) := by nlinarith
  have hpoly : t < 2 * t ^ (3 : ℕ) := by
    rw [pow_succ]
    nlinarith
  nlinarith

/-- The concrete kernel cost already beats the Lipschitz loss on the fixed
outer quarter of the smoothing ball when `theta < 5/4`. -/
theorem lowerKernelPhi_dominates_outer_quarter {p r theta : ℝ}
    (hr : 1 ≤ r) (hrp : r ≤ p) (htheta : 1 < theta)
    (hthetaUpper : theta < 5 / 4) {d : ℕ} (u : Point d)
    (huLower : 3 / 4 < lpNorm p u) (huUpper : lpNorm p u ≤ 1) :
    lpNorm p u < lowerKernelPhi r theta u := by
  rw [lowerKernelPhi_eq_norm_power (by linarith : r ≠ 0)]
  have hmono := lpNorm_le_lpNorm_of_exponent_le hr hrp u
  have hpow := Real.rpow_le_rpow (O3.lpNorm_nonneg p u) hmono
    (by linarith : 0 ≤ 2 * theta)
  have hscalar := self_lt_two_mul_rpow_of_three_four_lt huLower huUpper
    (by linarith : 0 ≤ 2 * theta) (by linarith : 2 * theta < 3)
  nlinarith

/-- A continuous smoothing cost whose value outside the closed smoothing ball
is strictly larger than the zero-displacement cost has a global minimizer,
and every global minimizer lies strictly inside that ball. This is the exact
finite-dimensional compact-ball reduction required before the concrete kernel
barrier is discharged. -/
theorem exists_infimal_minimizer_of_closed_ball_barrier
    (kernel : SmoothingKernelData p d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (x : Point d)
    (hp : 1 ≤ p)
    (hcontinuous : Continuous (smoothingCost kernel chi ell x))
    (hbarrier : ∀ v : Point d, chi ≤ lpNorm p v →
      smoothingCost kernel chi ell x 0 < smoothingCost kernel chi ell x v) :
    ∃ v : Point d,
      IsInfimalMinimizer kernel chi ell x v ∧ lpNorm p v < chi := by
  let ball : Set (Point d) := {v | lpNorm p v ≤ chi}
  have hcompact : IsCompact ball := isCompact_lpNorm_le hp
  have hzeroNorm : lpNorm p (0 : Point d) = 0 :=
    O3.lpNorm_zero (lt_of_lt_of_le zero_lt_one hp)
  have hzero : (0 : Point d) ∈ ball := by
    change lpNorm p (0 : Point d) ≤ chi
    rw [hzeroNorm]
    exact hchi.le
  obtain ⟨v, hvball, hvmin⟩ :=
    hcompact.exists_isMinOn ⟨0, hzero⟩ hcontinuous.continuousOn
  have hvglobal : IsInfimalMinimizer kernel chi ell x v := by
    intro w
    by_cases hw : lpNorm p w ≤ chi
    · exact hvmin hw
    · have hvzero := hvmin hzero
      exact hvzero.trans (hbarrier w (le_of_not_ge hw)).le
  refine ⟨v, hvglobal, lt_of_le_of_ne hvball ?_⟩
  intro heq
  have hstrict := hbarrier v heq.ge
  exact (not_lt_of_ge (hvglobal 0)) hstrict

/-- The compact-ball theorem specialized to the radial barrier used by the
V7 smoothing kernel. The remaining concrete kernel obligation is precisely
to prove this radial inequality from `lowerKernelPhi` and `r0 ≤ p`. -/
theorem exists_infimal_minimizer_of_radial_kernel
    (kernel : SmoothingKernelData p d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (x : Point d)
    (hp : 1 ≤ p) (hlip : IsOneLipschitz p ell)
    (hphi : Continuous kernel.phi) (hphi0 : kernel.phi 0 = 0)
    (hradial : ∀ u : Point d, 1 ≤ lpNorm p u →
      lpNorm p u < kernel.phi u) :
    ∃ v : Point d,
      IsInfimalMinimizer kernel chi ell x v ∧ lpNorm p v < chi := by
  apply exists_infimal_minimizer_of_closed_ball_barrier kernel hchi ell x hp
    (continuous_smoothingCost kernel hp hlip hphi x)
  intro v hv
  have hscale : lpNorm p ((1 / chi) • v) = lpNorm p v / chi := by
    change O3.lpNorm p ((1 / chi) • v) = O3.lpNorm p v / chi
    rw [O3.Stage2RouteC.lpNorm_smul hp, abs_of_pos (one_div_pos.mpr hchi)]
    ring
  have hone : 1 ≤ lpNorm p ((1 / chi) • v) := by
    rw [hscale, le_div_iff₀ hchi]
    simpa using hv
  have hkernel := hradial ((1 / chi) • v) hone
  have hkernelScaled : lpNorm p v < chi * kernel.phi ((1 / chi) • v) := by
    have := mul_lt_mul_of_pos_left hkernel hchi
    rw [hscale] at this
    rw [show lpNorm p v = chi * (lpNorm p v / chi) by
      field_simp [hchi.ne']]
    exact this
  have hell := hlip (x + v) x
  have hellLower : ell x - lpNorm p v ≤ ell (x + v) := by
    rw [show x + v - x = v by abel] at hell
    linarith [neg_le_of_abs_le hell]
  simp only [smoothingCost, add_zero, hphi0, smul_zero, mul_zero, add_zero]
  nlinarith

/-- Finite-dimensional attainment and strict interiority for the actual
kernel selected by the Stage-5 construction. -/
theorem exists_infimal_minimizer_lowerKernelPhi
    (kernel : SmoothingKernelData p d) {r theta chi : ℝ}
    (hr : 2 < r) (hrp : r ≤ p) (htheta : 1 < theta)
    (htr : 2 * theta < r) (hchi : 0 < chi)
    (hkernelPhi : kernel.phi = lowerKernelPhi r theta)
    (ell : Point d → ℝ) (hlip : IsOneLipschitz p ell) (x : Point d) :
    ∃ v : Point d,
      IsInfimalMinimizer kernel chi ell x v ∧ lpNorm p v < chi := by
  apply exists_infimal_minimizer_of_radial_kernel kernel hchi ell x
    (by linarith : 1 ≤ p) hlip
  · rw [hkernelPhi]
    exact (Stage5AboveTwoLower.S5AGlobalC2.contDiff_two_lowerKernelPhi
      hr htheta htr).continuous
  · rw [hkernelPhi]
    exact lowerKernelPhi_zero (by linarith : 0 < r) (by linarith : 0 < theta)
  · intro u hu
    rw [hkernelPhi]
    exact lowerKernelPhi_radial (by linarith : 1 ≤ r) hrp htheta u hu

/-- The actual minimizer can be chosen with the uniform outer-quarter margin
`‖v‖_p ≤ 3 chi / 4`, independently of the centre and of the one-Lipschitz
objective. -/
theorem exists_infimal_minimizer_lowerKernelPhi_with_margin
    (kernel : SmoothingKernelData p d) {r theta chi : ℝ}
    (hr : 2 < r) (hrp : r ≤ p) (htheta : 1 < theta)
    (hthetaUpper : theta < 5 / 4) (htr : 2 * theta < r)
    (hchi : 0 < chi) (hkernelPhi : kernel.phi = lowerKernelPhi r theta)
    (ell : Point d → ℝ) (hlip : IsOneLipschitz p ell) (x : Point d) :
    ∃ v : Point d,
      IsInfimalMinimizer kernel chi ell x v ∧
        lpNorm p v ≤ chi - chi / 4 := by
  obtain ⟨v, hvmin, hvInterior⟩ :=
    exists_infimal_minimizer_lowerKernelPhi kernel hr hrp htheta htr hchi
      hkernelPhi ell hlip x
  refine ⟨v, hvmin, ?_⟩
  by_contra hmargin
  have hvLower : 3 * chi / 4 < lpNorm p v := by
    have : chi - chi / 4 < lpNorm p v := lt_of_not_ge hmargin
    linarith
  have hp : 1 ≤ p := by linarith
  have hscale : lpNorm p ((1 / chi) • v) = lpNorm p v / chi := by
    change O3.lpNorm p ((1 / chi) • v) = O3.lpNorm p v / chi
    rw [O3.Stage2RouteC.lpNorm_smul hp, abs_of_pos (one_div_pos.mpr hchi)]
    ring
  have huLower : 3 / 4 < lpNorm p ((1 / chi) • v) := by
    rw [hscale, lt_div_iff₀ hchi]
    nlinarith
  have huUpper : lpNorm p ((1 / chi) • v) ≤ 1 := by
    rw [hscale, div_le_one hchi]
    exact hvInterior.le
  have hkernel : lpNorm p ((1 / chi) • v) <
      kernel.phi ((1 / chi) • v) := by
    rw [hkernelPhi]
    exact lowerKernelPhi_dominates_outer_quarter (by linarith : 1 ≤ r)
      hrp htheta hthetaUpper _ huLower huUpper
  have hkernelScaled : lpNorm p v <
      chi * kernel.phi ((1 / chi) • v) := by
    have hs := mul_lt_mul_of_pos_left hkernel hchi
    rw [hscale] at hs
    rw [show lpNorm p v = chi * (lpNorm p v / chi) by
      field_simp [hchi.ne']]
    exact hs
  have hell := hlip (x + v) x
  have hellLower : ell x - lpNorm p v ≤ ell (x + v) := by
    rw [show x + v - x = v by abel] at hell
    linarith [neg_le_of_abs_le hell]
  have hphi0 : kernel.phi 0 = 0 := by
    rw [hkernelPhi]
    exact lowerKernelPhi_zero (by linarith : 0 < r) (by linarith : 0 < theta)
  have hstrict : smoothingCost kernel chi ell x 0 <
      smoothingCost kernel chi ell x v := by
    simp only [smoothingCost, add_zero, hphi0, smul_zero, mul_zero, add_zero]
    nlinarith
  exact (not_lt_of_ge (hvmin 0)) hstrict

/-- Exact approximation bounds for the concrete infimal value. -/
theorem localSmoothingValue_bounds_lowerKernelPhi
    (kernel : SmoothingKernelData p d) {r theta chi : ℝ}
    (hr : 2 < r) (hrp : r ≤ p) (htheta : 1 < theta)
    (htr : 2 * theta < r) (hchi : 0 < chi)
    (hkernelPhi : kernel.phi = lowerKernelPhi r theta)
    (ell : Point d → ℝ) (hlip : IsOneLipschitz p ell) (x : Point d) :
    ell x - chi ≤ localSmoothingValue kernel chi ell x ∧
      localSmoothingValue kernel chi ell x ≤ ell x := by
  obtain ⟨v, hvmin, hvInterior⟩ :=
    exists_infimal_minimizer_lowerKernelPhi kernel hr hrp htheta htr hchi
      hkernelPhi ell hlip x
  rw [localSmoothingValue_eq_of_minimizer kernel chi ell x v hvmin]
  have hell := hlip (x + v) x
  have hellLower : ell x - lpNorm p v ≤ ell (x + v) := by
    rw [show x + v - x = v by abel] at hell
    linarith [neg_le_of_abs_le hell]
  have hphiNonneg : 0 ≤ kernel.phi ((1 / chi) • v) := by
    rw [hkernelPhi]
    exact lowerKernelPhi_nonneg _
  have hlower : ell x - chi ≤ smoothingCost kernel chi ell x v := by
    unfold smoothingCost
    nlinarith [mul_nonneg hchi.le hphiNonneg]
  have hphi0 : kernel.phi 0 = 0 := by
    rw [hkernelPhi]
    exact lowerKernelPhi_zero (by linarith : 0 < r) (by linarith : 0 < theta)
  have hupper := hvmin 0
  simp only [smoothingCost, add_zero, smul_zero, hphi0, mul_zero, add_zero] at hupper
  exact ⟨hlower, hupper⟩

end V7.Stage5AboveTwoLowerResume
