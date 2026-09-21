/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Normalization
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
The completed below-two phases imply the requested physical terminal-gradient bound.
-/

namespace V7.Stage3BelowTwoS3F

private abbrev LpSpace (p : ℝ) (d : ℕ) :=
  PiLp (ENNReal.ofReal p) (fun _ : Fin d => ℝ)

theorem minimizerSet_isClosed (inst : PositiveInstance p d x0) :
    IsClosed (MinimizerSet inst.oracle) := by
  have hf : Continuous inst.oracle.value := continuous_iff_continuousAt.mpr fun x =>
    (inst.coordinateGradient x).1.continuousAt
  change IsClosed {x | ∀ y, inst.oracle.value x ≤ inst.oracle.value y}
  simpa only [Set.ofPred_forall] using
    (isClosed_iInter fun y => isClosed_le hf
      (continuous_const : Continuous (fun _ : Point d => inst.oracle.value y)))

theorem lpNorm_eq_transport_dist (p : ℝ) (hp : 1 ≤ p) (x y : Point d) :
    lpNorm p (x - y) =
      dist (WithLp.toLp (ENNReal.ofReal p) x : LpSpace p d)
        (WithLp.toLp (ENNReal.ofReal p) y : LpSpace p d) := by
  change O3.lpNorm p (x - y) = _
  rw [O3.Stage2RouteC.lpNorm_eq_piLpNorm hp]
  change ‖(WithLp.toLp (ENNReal.ofReal p) (x - y) : LpSpace p d)‖ =
    ‖(WithLp.toLp (ENNReal.ofReal p) x : LpSpace p d) -
      WithLp.toLp (ENNReal.ofReal p) y‖
  rfl

theorem exists_minimizer_at_radius (inst : PositiveInstance p d x0)
    (hp : 1 < p) :
    ∃ xstar : Point d, xstar ∈ MinimizerSet inst.oracle ∧
      lpNorm p (xstar - x0) = inst.R := by
  let e : Point d ≃ₜ LpSpace p d :=
    (PiLp.homeomorph (ENNReal.ofReal p) (fun _ : Fin d => ℝ)).symm
  let S : Set (LpSpace p d) := e '' MinimizerSet inst.oracle
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let _ : ProperSpace (LpSpace p d) := FiniteDimensional.proper ℝ (LpSpace p d)
  have hSclosed : IsClosed S := e.isClosedMap _ (minimizerSet_isClosed inst)
  have hSne : S.Nonempty := inst.minimizerNonempty.image e
  obtain ⟨z, hzS, hz⟩ := hSclosed.exists_infDist_eq_dist hSne (e x0)
  rcases hzS with ⟨xstar, hxstar, rfl⟩
  refine ⟨xstar, hxstar, ?_⟩
  let distances : Set ℝ :=
    (fun x : Point d => lpNorm p (x - x0)) '' MinimizerSet inst.oracle
  have hnonempty : distances.Nonempty := inst.minimizerNonempty.image _
  have hbelow : BddBelow distances := ⟨0, by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact O3.lpNorm_nonneg p (x - x0)⟩
  have hle : lpNorm p (xstar - x0) ≤ sInf distances := by
    apply le_csInf hnonempty
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hxS : e x ∈ S := ⟨x, hx, rfl⟩
    change lpNorm p (xstar - x0) ≤ lpNorm p (x - x0)
    rw [lpNorm_eq_transport_dist p hp.le, lpNorm_eq_transport_dist p hp.le]
    change dist (e xstar) (e x0) ≤ dist (e x) (e x0)
    rw [dist_comm (e xstar) (e x0), dist_comm (e x) (e x0)]
    calc
      dist (e x0) (e xstar) = Metric.infDist (e x0) S := hz.symm
      _ ≤ dist (e x0) (e x) := Metric.infDist_le_dist_of_mem hxS
  have hge : sInf distances ≤ lpNorm p (xstar - x0) :=
    csInf_le hbelow ⟨xstar, hxstar, rfl⟩
  change lpNorm p (xstar - x0) = sInf distances
  exact le_antisymm hle hge

theorem horizon_ge (p eps M D : ℝ) :
    2 * Real.sqrt (M * D / ((p - 1) * eps)) ≤
      (horizon p eps M D : ℝ) := Nat.le_ceil _

theorem one_le_horizon {p eps M D : ℝ} (hp : 1 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D) :
    1 ≤ horizon p eps M D := by
  have hsigma : 0 < p - 1 := sub_pos.mpr hp
  have hratio : 0 < M * D / ((p - 1) * eps) := by positivity
  have hceil := horizon_ge p eps M D
  have hsqrt : 0 < Real.sqrt (M * D / ((p - 1) * eps)) := Real.sqrt_pos.2 hratio
  exact Nat.ceil_pos.mpr (mul_pos (by norm_num) hsqrt)

theorem sInf_range_eq_of_min (f : Point d → ℝ) (z : Point d)
    (hz : ∀ y, f z ≤ f y) : sInf (Set.range f) = f z := by
  apply le_antisymm
  · exact csInf_le ⟨f z, by rintro y ⟨x, rfl⟩; exact hz x⟩ ⟨z, rfl⟩
  · apply le_csInf (Set.range_nonempty f)
    rintro y ⟨x, rfl⟩
    exact hz x

theorem cocoPairHolds_exact_iff (p M : ℝ) (oracle : PairOracle d)
    (x y : Point d) :
    cocoPairHolds p M (oracle.observe x) (oracle.observe y) ↔
      CocoercivityGuard p M oracle x y := by
  rfl

/-- The prescribed horizon makes the reciprocal terminal weight fit the gradient budget. -/
private lemma horizon_inverse_weight_le_budget (p eps M D : ℝ) (hp : 1 < p)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (n : ℕ) (hn : n = horizon p eps M D) : 1 / ((p - 1) * weight n n) ≤ eps / (M * D) := by
  subst n
  let n := horizon p eps M D
  have hsigma : 0 < p - 1 := sub_pos.mpr hp
  rw [weight_at]
  have hnreal := horizon_ge p eps M D
  have hratio : 0 ≤ M * D / ((p - 1) * eps) := by positivity
  have hsqrtSq := Real.sq_sqrt hratio
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hcore : 4 * M * D ≤ (p - 1) * eps * (n : ℝ) ^ 2 := by
    change 2 * Real.sqrt (M * D / ((p - 1) * eps)) ≤ (n : ℝ) at hnreal
    have hsqrt0 : 0 ≤ Real.sqrt (M * D / ((p - 1) * eps)) :=
      Real.sqrt_nonneg _
    have hsqbound :
        (2 * Real.sqrt (M * D / ((p - 1) * eps))) ^ (2 : ℕ) ≤
          (n : ℝ) ^ (2 : ℕ) :=
      (sq_le_sq₀ (by positivity) hn0).2 hnreal
    have hid : 4 * M * D = (p - 1) * eps *
        (2 * Real.sqrt (M * D / ((p - 1) * eps))) ^ (2 : ℕ) := by
      calc
        4 * M * D = 4 * ((p - 1) * eps) *
            (M * D / ((p - 1) * eps)) := by
          field_simp [hsigma.ne', heps.ne']
        _ = 4 * ((p - 1) * eps) *
            (Real.sqrt (M * D / ((p - 1) * eps))) ^ (2 : ℕ) := by
          rw [hsqrtSq]
        _ = _ := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hsqbound (by positivity)
  have hden : 0 < (p - 1) * ((n : ℝ) ^ 2 / 4) := by
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast one_le_horizon hp heps hM hD
    positivity
  have hMD : 0 < M * D := mul_pos hM hD
  rw [div_le_div_iff₀ hden hMD]
  nlinarith

theorem terminal_gradient_le (p eps M D : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (inst : PositiveInstance p d x0) (hDR : inst.R ≤ D)
    (hP : ∀ k < horizon p eps M D, cocoPairHolds p M
      (phaseOneObs p eps M D x0 inst.oracle k)
      (phaseOneObs p eps M D x0 inst.oracle (k + 1)))
    (hQ : ∀ k < horizon p eps M D, cocoPairHolds p M
      (phaseTwoObs p eps M D x0 inst.oracle k)
      (phaseTwoObs p eps M D x0 inst.oracle (k + 1))) :
    lpNorm (conjugateExponent p)
      (phaseTwoObs p eps M D x0 inst.oracle (horizon p eps M D)).gradient ≤ eps := by
  let n := horizon p eps M D
  have hsigma : 0 < p - 1 := sub_pos.mpr hp
  obtain ⟨xstar, hxstar, hradius⟩ := exists_minimizer_at_radius inst hp
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
    rw [O3.Stage2RouteC.lpNorm_smul hp.le, abs_of_pos (one_div_pos.mpr hD)]
    simpa [div_eq_mul_inv, mul_comm] using (div_le_one hD).2 hxD
  let oracle₁ := phaseOneOracle x0 M D inst.oracle
  let fstar₁ := oracle₁.value z
  let pdata := primalData p n oracle₁ z fstar₁
  have hzmin₁ : ∀ y, oracle₁.value z ≤ oracle₁.value y := by
    intro y
    dsimp [oracle₁, phaseOneOracle, normalizedPairOracle]
    rw [hzphys]
    exact div_le_div_of_nonneg_right (by linarith [hxstar (x0 + D • y)])
      (mul_nonneg hM.le (sq_nonneg D))
  have hpguards : ∀ k < n,
      FunctionBregman oracle₁.value oracle₁.gradient
          (primalState p n oracle₁ k).x (primalState p n oracle₁ (k + 1)).x ≥
        (1 / 2) * (lpNorm (conjugateExponent p)
          (oracle₁.gradient (primalState p n oracle₁ k).x -
            oracle₁.gradient (primalState p n oracle₁ (k + 1)).x)) ^ (2 : ℕ) := by
    intro k hk
    have hphys := hP k (by simpa [n] using hk)
    have hguard : CocoercivityGuard p M inst.oracle
        (phaseOneObs p eps M D x0 inst.oracle k).point
        (phaseOneObs p eps M D x0 inst.oracle (k + 1)).point := by
      exact (cocoPairHolds_exact_iff p M inst.oracle _ _).1 hphys
    have hs := (belowGuardScaling p M D hp hM hD d inst.oracle x0
      (primalState p n oracle₁ k).x (primalState p n oracle₁ (k + 1)).x).2.2
    apply hs.2
    simpa [phaseOneObs, phaseOneState, oracle₁, n,
      O3.PairOracle.observe] using hguard
  have hpass : BelowPrimalAssumptions pdata := by
    have hdyn := primal_dynamics p n (one_le_horizon hp heps hM hD)
      oracle₁ z fstar₁
    rcases hdyn with ⟨hn, hu0, hun, hdwn, hw, hs0, hv0, hx0, hstep⟩
    refine ⟨⟨hn, hu0, hun, hdwn, hw, hs0, hv0, hx0, hstep⟩,
      normalized_convex inst x0 hM hD,
      normalized_coordinateGradient inst x0 hM hD, rfl, hzmin₁,
      hu0, hun, hdwn, hw, hs0, hv0, hx0, ?_,
      primal_trace_exact p n oracle₁, primal_trace_length p n oracle₁, ?_⟩
    · intro k hk
      exact ⟨(hstep k hk).1, (hstep k hk).2.1, (hstep k hk).2.2,
        hpguards k hk⟩
    · intro k hk
      exact primal_queried_at p n oracle₁ k hk
  have hprimal := belowPrimal p hp hp2 d n pdata hpass
  have hh : belowH p z ≤ 1 / (2 * (p - 1)) := by
    unfold belowH
    have hz0 := O3.lpNorm_nonneg p z
    have hsquare : (lpNorm p z) ^ (2 : ℕ) ≤ 1 := by nlinarith
    have hc : 0 ≤ 1 / (2 * (p - 1)) := by positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsquare hc
  have hgap₁ : oracle₁.value (primalState p n oracle₁ n).x - fstar₁ ≤
      1 / (2 * (p - 1) * weight n n) := by
    change oracle₁.value (primalState p n oracle₁ n).x - fstar₁ ≤
      belowH p z / weight n n at hprimal
    have hw := weight_pos (one_le_horizon hp heps hM hD) le_rfl
    calc
      _ ≤ belowH p z / weight n n := hprimal
      _ ≤ (1 / (2 * (p - 1))) / weight n n :=
        div_le_div_of_nonneg_right hh hw.le
      _ = _ := by field_simp [hsigma.ne', hw.ne']
  let center := phaseTwoCenter p eps M D x0 inst.oracle
  let oracle₂ := phaseTwoOracle p eps M D x0 inst.oracle
  let ddata := dualData p n oracle₂
  let z₂ : Point d := (1 / D) • (xstar - center)
  have hz₂phys : center + D • z₂ = xstar := by
    dsimp [z₂]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hD.ne']
    ring
  have hzmin₂ : ∀ y, oracle₂.value z₂ ≤ oracle₂.value y := by
    intro y
    dsimp [oracle₂, phaseTwoOracle, normalizedPairOracle]
    rw [hz₂phys]
    exact div_le_div_of_nonneg_right (by linarith [hxstar (center + D • y)])
      (mul_nonneg hM.le (sq_nonneg D))
  have hqguards : ∀ k < n,
      FunctionBregman oracle₂.value oracle₂.gradient
          (dualQ p n oracle₂ k) (dualQ p n oracle₂ (k + 1)) ≥
        (1 / 2) * (lpNorm (conjugateExponent p)
          (oracle₂.gradient (dualQ p n oracle₂ k) -
            oracle₂.gradient (dualQ p n oracle₂ (k + 1)))) ^ (2 : ℕ) := by
    intro k hk
    have hphys := hQ k (by simpa [n] using hk)
    have hguard : CocoercivityGuard p M inst.oracle
        (phaseTwoObs p eps M D x0 inst.oracle k).point
        (phaseTwoObs p eps M D x0 inst.oracle (k + 1)).point :=
      (cocoPairHolds_exact_iff p M inst.oracle _ _).1 hphys
    have hs := (belowGuardScaling p M D hp hM hD d inst.oracle center
      (dualQ p n oracle₂ k) (dualQ p n oracle₂ (k + 1))).2.2
    apply hs.2
    simpa [phaseTwoObs, center, oracle₂, n, O3.PairOracle.observe] using hguard
  have hdass : BelowDualAssumptions ddata := by
    have hdyn := dual_dynamics p n (one_le_horizon hp heps hM hD) oracle₂
    refine ⟨hdyn, normalized_convex inst center hM hD,
      normalized_coordinateGradient inst center hM hD,
      normalized_bddBelow inst center hM,
      coefficient_assumptions n (one_le_horizon hp heps hM hD),
      dual_trace_exact p n oracle₂, dual_trace_length p n oracle₂,
      (fun k hk => dual_queried_at p n oracle₂ k hk), (fun k hk => rfl),
      hdyn.2.2.1, hdyn.2.2.2, hqguards⟩
  have hdual := (belowTerminalGradient p hp hp2 d n ddata hdass).2
  have hsinf₂ : sInf (Set.range oracle₂.value) = oracle₂.value z₂ :=
    sInf_range_eq_of_min oracle₂.value z₂ hzmin₂
  change belowHstar p (oracle₂.gradient (dualQ p n oracle₂ n)) ≤
    (oracle₂.value (dualQ p n oracle₂ 0) - sInf (Set.range oracle₂.value)) /
      weight n n at hdual
  rw [hsinf₂] at hdual
  have hlink : oracle₂.value (dualQ p n oracle₂ 0) - oracle₂.value z₂ =
      oracle₁.value (primalState p n oracle₁ n).x - fstar₁ := by
    simp only [dualQ_zero]
    have hcenter : center = x0 + D • (primalState p n oracle₁ n).x := by
      rfl
    change
      ((inst.oracle.value (center + D • (0 : Point d)) -
          inst.oracle.value center) / (M * D ^ 2) -
        (inst.oracle.value (center + D • z₂) - inst.oracle.value center) /
          (M * D ^ 2)) =
      ((inst.oracle.value
          (x0 + D • (primalState p n oracle₁ n).x) -
            inst.oracle.value x0) / (M * D ^ 2) -
        (inst.oracle.value (x0 + D • z) - inst.oracle.value x0) /
          (M * D ^ 2))
    simp only [smul_zero, add_zero]
    rw [hz₂phys, hzphys]
    rw [hcenter]
    ring
  rw [hlink] at hdual
  have hstar : ((p - 1) / 2) *
      (lpNorm (conjugateExponent p) (oracle₂.gradient (dualQ p n oracle₂ n))) ^
        (2 : ℕ) ≤ 1 / (2 * (p - 1) * (weight n n) ^ (2 : ℕ)) := by
    change belowHstar p (oracle₂.gradient (dualQ p n oracle₂ n)) ≤ _
    have hw := weight_pos (one_le_horizon hp heps hM hD) le_rfl
    have hdiv := div_le_div_of_nonneg_right hgap₁ hw.le
    have heq : (1 / (2 * (p - 1) * weight n n)) / weight n n =
        1 / (2 * (p - 1) * (weight n n) ^ (2 : ℕ)) := by
      field_simp [hsigma.ne', hw.ne']
    exact hdual.trans (hdiv.trans_eq heq)
  have hnormF : lpNorm (conjugateExponent p)
      (oracle₂.gradient (dualQ p n oracle₂ n)) ≤ 1 / ((p - 1) * weight n n) := by
    have hg0 := O3.lpNorm_nonneg (conjugateExponent p)
      (oracle₂.gradient (dualQ p n oracle₂ n))
    have hw := weight_pos (one_le_horizon hp heps hM hD) le_rfl
    have hrhs : 0 ≤ 1 / ((p - 1) * weight n n) := by positivity
    have heq : ((p - 1) / 2) *
          (1 / ((p - 1) * weight n n)) ^ (2 : ℕ) =
        1 / (2 * (p - 1) * (weight n n) ^ (2 : ℕ)) := by
      field_simp [hsigma.ne', hw.ne']
    have hsq : ((p - 1) / 2) *
          (lpNorm (conjugateExponent p)
            (oracle₂.gradient (dualQ p n oracle₂ n))) ^ (2 : ℕ) ≤
        ((p - 1) / 2) *
          (1 / ((p - 1) * weight n n)) ^ (2 : ℕ) := by
      rw [heq]
      exact hstar
    have hc : 0 < (p - 1) / 2 := by positivity
    have hsqraw :
        (lpNorm (conjugateExponent p)
          (oracle₂.gradient (dualQ p n oracle₂ n))) ^ (2 : ℕ) ≤
          (1 / ((p - 1) * weight n n)) ^ (2 : ℕ) := by
      exact (mul_le_mul_iff_left₀ hc).mp (by simpa [mul_comm] using hsq)
    exact (sq_le_sq₀ hg0 hrhs).mp hsqraw
  have hbudget := horizon_inverse_weight_le_budget p eps M D hp heps hM hD n rfl
  have hnormNorm := hnormF.trans hbudget
  have hscale : lpNorm (conjugateExponent p)
      (oracle₂.gradient (dualQ p n oracle₂ n)) =
      (1 / (M * D)) * lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 inst.oracle n).gradient := by
    rw [← normalizedGradient_phaseTwo]
    change O3.lpNorm (O3.conjugateExponent p)
      ((1 / (M * D)) • _) = _
    rw [O3.Stage2RouteC.lpNorm_smul
      (O3.one_lt_conjugateExponent hp).le,
      abs_of_pos (one_div_pos.mpr (mul_pos hM hD))]
  rw [hscale] at hnormNorm
  have hMD := mul_pos hM hD
  have hnormNorm' : (1 / (M * D)) *
      lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 inst.oracle n).gradient ≤
      (1 / (M * D)) * eps := by
    simpa [div_eq_mul_inv, mul_comm] using hnormNorm
  exact (mul_le_mul_iff_left₀ (one_div_pos.mpr hMD)).mp
    (by simpa [mul_comm] using hnormNorm')

end V7.Stage3BelowTwoS3F
