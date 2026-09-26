/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Contract
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.AnalyticBridge

/-!
The completed above-two phases imply the requested physical terminal-gradient accuracy.
-/

@[expose] public section

namespace V7.Stage4AboveTwoFinalTrial

open V7.Stage3BelowTwoS3F

theorem terminal_gradient_le (p eps M D : ℝ) (hp : 2 < p)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (inst : PositiveInstance p d x0) (hDR : inst.R ≤ D)
    (hP : ∀ k < nF p eps M D, cocoPairHolds p M
      (phaseOneObs p eps M D x0 inst.oracle k)
      (phaseOneObs p eps M D x0 inst.oracle (k + 1)))
    (hQ : ∀ k < nD p eps M D, cocoPairHolds p M
      (phaseTwoObs p eps M D x0 inst.oracle k)
      (phaseTwoObs p eps M D x0 inst.oracle (k + 1))) :
    lpNorm (conjugateExponent p)
      (phaseTwoObs p eps M D x0 inst.oracle (nD p eps M D)).gradient ≤ eps := by
  let nf := nF p eps M D
  let nd := nD p eps M D
  let delta0 := delta eps M D
  have hp1 : 1 < p := by linarith
  have hdelta : 0 < delta0 := delta_pos heps hM hD
  have hnf : 1 ≤ nf := one_le_nF hp heps hM hD
  have hnd : 1 ≤ nd := one_le_nD hp heps hM hD
  obtain ⟨xstar, hxstar, hradius⟩ := exists_minimizer_at_radius inst hp1
  have hxD : lpNorm p (xstar - x0) ≤ D := hradius.trans_le hDR
  let z : Point d := (1 / D) • (xstar - x0)
  have hzphys : x0 + D • z = xstar := by
    dsimp [z]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hD.ne']
    ring
  have hznorm : lpNorm p z ≤ 1 := by
    change O3.lpNorm p ((1 / D) • (xstar - x0)) ≤ 1
    rw [O3.Stage2RouteC.lpNorm_smul hp1.le,
      abs_of_pos (one_div_pos.mpr hD)]
    simpa [div_eq_mul_inv, mul_comm] using (div_le_one hD).2 hxD
  let oracle1 := phaseOneOracle x0 M D inst.oracle
  let fstar1 := oracle1.value z
  let pdata := primalData p (etaF p) nf oracle1 fstar1
  have hzmin1 : ∀ y, oracle1.value z ≤ oracle1.value y := by
    intro y
    dsimp [oracle1, phaseOneOracle, normalizedPairOracle]
    rw [hzphys]
    exact div_le_div_of_nonneg_right (by linarith [hxstar (x0 + D • y)])
      (mul_nonneg hM.le (sq_nonneg D))
  have hpguards : ∀ k < nf,
      FunctionBregman oracle1.value oracle1.gradient
          (primalState p (etaF p) nf oracle1 k).x
          (primalState p (etaF p) nf oracle1 (k + 1)).x ≥
        (1 / 2) * (lpNorm (conjugateExponent p)
          (oracle1.gradient (primalState p (etaF p) nf oracle1 k).x -
            oracle1.gradient (primalState p (etaF p) nf oracle1 (k + 1)).x)) ^
              (2 : ℕ) := by
    intro k hk
    have hphys := hP k (by simpa [nf] using hk)
    have hguard : CocoercivityGuard p M inst.oracle
        (phaseOneObs p eps M D x0 inst.oracle k).point
        (phaseOneObs p eps M D x0 inst.oracle (k + 1)).point :=
      (cocoPairHolds_exact_iff p M inst.oracle _ _).1 hphys
    have hs := (belowGuardScaling p M D hp1 hM hD d inst.oracle x0
      (primalState p (etaF p) nf oracle1 k).x
      (primalState p (etaF p) nf oracle1 (k + 1)).x).2.2
    apply hs.2
    simpa [phaseOneObs, phaseOneState, oracle1, nf,
      O3.PairOracle.observe] using hguard
  have hpass : AbovePrimalPhaseAssumptions pdata := by
    have hdyn := primal_dynamics p (etaF p) nf hp (etaF_pos hp) hnf
      oracle1 fstar1
    rcases hdyn with ⟨hn, hcoeff, hs0, hv0, hx0, hstep⟩
    refine ⟨⟨hn, hcoeff, hs0, hv0, hx0, hstep⟩,
      normalized_convex inst x0 hM hD,
      normalized_coordinateGradient inst x0 hM hD, ?_,
      ⟨z, rfl, hzmin1⟩, hcoeff, hs0, hv0, hx0, ?_,
      primal_trace_exact p (etaF p) nf oracle1,
      primal_trace_length p (etaF p) nf oracle1, ?_⟩
    · exact (sInf_range_eq_of_min oracle1.value z hzmin1).symm
    · intro k hk
      exact ⟨(hstep k hk).1, (hstep k hk).2.1, (hstep k hk).2.2,
        hpguards k hk⟩
    · intro k hk
      exact primal_queried_at p (etaF p) nf oracle1 k hk
  have hgap1 : oracle1.value (primalState p (etaF p) nf oracle1 nf).x -
      fstar1 ≤ delta0 := by
    apply abovePhaseOneHorizonBound p hp delta0 hdelta nf
      (by rfl) pdata hpass z rfl hznorm
    · rfl
    · rfl
  let center := phaseTwoCenter p eps M D x0 inst.oracle
  let oracle2 := phaseTwoOracle p eps M D x0 inst.oracle
  let ddata := dualData p (etaD p eps M D) nd oracle2
  let z2 : Point d := (1 / D) • (xstar - center)
  have hz2phys : center + D • z2 = xstar := by
    dsimp [z2]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hD.ne']
    ring
  have hzmin2 : ∀ y, oracle2.value z2 ≤ oracle2.value y := by
    intro y
    dsimp [oracle2, phaseTwoOracle, normalizedPairOracle]
    rw [hz2phys]
    exact div_le_div_of_nonneg_right (by linarith [hxstar (center + D • y)])
      (mul_nonneg hM.le (sq_nonneg D))
  have hqguards : ∀ k < nd,
      FunctionBregman oracle2.value oracle2.gradient
          (dualQ p (etaD p eps M D) nd oracle2 k)
          (dualQ p (etaD p eps M D) nd oracle2 (k + 1)) ≥
        (1 / 2) * (lpNorm (conjugateExponent p)
          (oracle2.gradient (dualQ p (etaD p eps M D) nd oracle2 k) -
            oracle2.gradient
              (dualQ p (etaD p eps M D) nd oracle2 (k + 1)))) ^ (2 : ℕ) := by
    intro k hk
    have hphys := hQ k (by simpa [nd] using hk)
    have hguard : CocoercivityGuard p M inst.oracle
        (phaseTwoObs p eps M D x0 inst.oracle k).point
        (phaseTwoObs p eps M D x0 inst.oracle (k + 1)).point :=
      (cocoPairHolds_exact_iff p M inst.oracle _ _).1 hphys
    have hs := (belowGuardScaling p M D hp1 hM hD d inst.oracle center
      (dualQ p (etaD p eps M D) nd oracle2 k)
      (dualQ p (etaD p eps M D) nd oracle2 (k + 1))).2.2
    apply hs.2
    simpa [phaseTwoObs, center, oracle2, nd,
      O3.PairOracle.observe] using hguard
  have hdass : AboveDualPhaseAssumptions ddata := by
    have hdyn := dual_dynamics p (etaD p eps M D) nd hp
      (etaD_pos hp heps hM hD) hnd oracle2
    refine ⟨hdyn, normalized_convex inst center hM hD,
      normalized_coordinateGradient inst center hM hD,
      normalized_bddBelow inst center hM,
      dual_trace_exact p (etaD p eps M D) nd oracle2,
      dual_trace_length p (etaD p eps M D) nd oracle2,
      (fun k hk => ⟨dual_queried_at p (etaD p eps M D) nd oracle2 k hk,
        rfl⟩), hdyn.2.2.1, ?_⟩
    intro k hk
    exact ⟨(hdyn.2.2.2 k hk).1, (hdyn.2.2.2 k hk).2, hqguards k hk⟩
  have hsinf2 : sInf (Set.range oracle2.value) = oracle2.value z2 :=
    sInf_range_eq_of_min oracle2.value z2 hzmin2
  have hlink : oracle2.value (dualQ p (etaD p eps M D) nd oracle2 0) -
      oracle2.value z2 =
      oracle1.value (primalState p (etaF p) nf oracle1 nf).x - fstar1 := by
    simp only [dualQ_zero]
    have hcenter : center =
        x0 + D • (primalState p (etaF p) nf oracle1 nf).x := by rfl
    change
      ((inst.oracle.value (center + D • (0 : Point d)) -
          inst.oracle.value center) / (M * D ^ 2) -
        (inst.oracle.value (center + D • z2) - inst.oracle.value center) /
          (M * D ^ 2)) =
      ((inst.oracle.value
          (x0 + D • (primalState p (etaF p) nf oracle1 nf).x) -
            inst.oracle.value x0) / (M * D ^ 2) -
        (inst.oracle.value (x0 + D • z) - inst.oracle.value x0) /
          (M * D ^ 2))
    simp only [smul_zero, add_zero]
    rw [hz2phys, hzphys, hcenter]
    ring
  have hgap0 : ddata.oracle.value (ddata.q 0) -
      sInf (Set.range ddata.oracle.value) ≤ delta0 := by
    change oracle2.value (dualQ p (etaD p eps M D) nd oracle2 0) -
      sInf (Set.range oracle2.value) ≤ delta0
    rw [hsinf2, hlink]
    exact hgap1
  have hdual := (abovePhaseTwoTerminalGradientBound p hp delta0 hdelta nd
    (by rfl) ddata hdass hgap0 (by rfl) (by rfl)).2
  have hscale : lpNorm (conjugateExponent p)
      (oracle2.gradient (dualQ p (etaD p eps M D) nd oracle2 nd)) =
      (1 / (M * D)) * lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 inst.oracle nd).gradient := by
    rw [← normalizedGradient_phaseTwo]
    change O3.lpNorm (O3.conjugateExponent p) ((1 / (M * D)) • _) = _
    rw [O3.Stage2RouteC.lpNorm_smul
      (O3.one_lt_conjugateExponent hp1).le,
      abs_of_pos (one_div_pos.mpr (mul_pos hM hD))]
  change lpNorm (conjugateExponent p)
    (oracle2.gradient (dualQ p (etaD p eps M D) nd oracle2 nd)) ≤ delta0 at hdual
  rw [hscale] at hdual
  have hMD : 0 < M * D := mul_pos hM hD
  have hscaled : (1 / (M * D)) *
      lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 inst.oracle nd).gradient ≤
      (1 / (M * D)) * eps := by
    simpa [delta0, delta, div_eq_mul_inv, mul_comm] using hdual
  exact (mul_le_mul_iff_left₀ (one_div_pos.mpr hMD)).mp
    (by simpa [nd, mul_comm] using hscaled)

end V7.Stage4AboveTwoFinalTrial
