/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Anchor
import LeanPool.ParameterFreeGradient.O3.Stage8EuclideanGap
import LeanPool.ParameterFreeGradient.O3.Stage9FiniteDataOGMG

open scoped BigOperators

namespace V7

private theorem positive_quadratic_root_unique {A a b : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hb : 0 < b)
    (haq : a ^ 2 = A + a) (hbq : b ^ 2 = A + b) : a = b := by
  have hfactor : (a - b) * (a + b - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hab | hsum
  · linarith
  · have ha1 : a < 1 := by nlinarith
    have hprod : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha1)
    nlinarith

private theorem euclidean_weights_eq_source (data : EuclideanGapData d m)
    (hdyn : EuclideanGapDynamics data) :
    (∀ k ≤ m, data.A k = O3.euclideanA k) ∧
    (∀ k < m, data.a (k + 1) = O3.euclideanWeight (O3.euclideanA k)) := by
  rcases hdyn with ⟨hM, hA0, hx0, hw0, hrec⟩
  have hA : ∀ k ≤ m, data.A k = O3.euclideanA k := by
    intro k hk
    induction k with
    | zero => simpa using hA0
    | succ k ih =>
        have hkm : k < m := by omega
        rcases hrec k hkm with ⟨ha, hasq, hAnext, hy, hw, hx⟩
        have hAk := ih (by omega)
        have hweightPos := O3.euclideanA_increment_pos k
        have hweightEq := O3.euclideanWeight_equation (O3.euclideanA_nonneg k)
        have hAnonneg := O3.euclideanA_nonneg k
        have haeq : data.a (k + 1) = O3.euclideanWeight (O3.euclideanA k) := by
          rw [hAk] at hasq
          exact positive_quadratic_root_unique hAnonneg ha hweightPos hasq hweightEq
        rw [hAnext, O3.euclideanA_succ, hAk, haeq]
  refine ⟨hA, ?_⟩
  intro k hk
  rcases hrec k hk with ⟨ha, hasq, hAnext, hy, hw, hx⟩
  have hAk := hA k (by omega)
  have hweightPos := O3.euclideanA_increment_pos k
  have hweightEq := O3.euclideanWeight_equation (O3.euclideanA_nonneg k)
  have hAnonneg := O3.euclideanA_nonneg k
  rw [hAk] at hasq
  exact positive_quadratic_root_unique hAnonneg ha hweightPos hasq hweightEq

private theorem euclidean_data_eq_source (data : EuclideanGapData d m)
    (P : O3.AdmissibleInstance d 2)
    (horacle : P.oracle = data.inst.oracle) (hx0P : P.x0 = data.x0)
    (hMP : P.L = data.inst.L) (heps : P.eps = 1)
    (hdyn : EuclideanGapDynamics data) :
    (∀ k ≤ m,
      data.x k = (O3.euclideanEstimateState P data.M k).accelerated ∧
      data.w k = O3.euclideanEstimateMinimizer P data.M k) ∧
    (∀ k < m, data.y k = O3.euclideanEstimateQuery P data.M k) := by
  rcases hdyn with ⟨hM, hA0, hxzero, hwzero, hrec⟩
  have hweights := euclidean_weights_eq_source data
    ⟨hM, hA0, hxzero, hwzero, hrec⟩
  have hA := hweights.1
  have ha := hweights.2
  have hgradP : P.grad = data.inst.oracle.gradient := by
    have h := congrArg O3.PairOracle.gradient horacle
    simpa [O3.AdmissibleInstance.oracle] using h
  have hcum : ∀ k,
      (O3.euclideanEstimateState P data.M k).cumulativeGradient =
        fun j => ∑ i ∈ Finset.range k,
          O3.euclideanWeight (O3.euclideanA i) *
            P.grad (O3.euclideanEstimateQuery P data.M i) j := by
    intro k
    induction k with
    | zero =>
        funext j
        simp [O3.euclideanEstimateState]
    | succ k ih =>
        rw [O3.euclideanEstimateState_succ_cumulative, ih]
        funext j
        simp [Finset.sum_range_succ, O3.euclideanEstimateObservation,
          O3.AdmissibleInstance.oracle, O3.PairOracle.observe]
  have hstateAll : ∀ k ≤ m,
      (data.x k = (O3.euclideanEstimateState P data.M k).accelerated ∧
       data.w k = O3.euclideanEstimateMinimizer P data.M k) ∧
      (∀ i < k, data.y i = O3.euclideanEstimateQuery P data.M i) := by
    intro k hk
    induction k with
    | zero =>
        refine ⟨?_, by intro i hi; omega⟩
        constructor
        · simpa [O3.euclideanEstimateState, hx0P] using hxzero
        · simpa [O3.euclideanEstimateMinimizer,
            O3.euclideanEstimateState,
            O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer,
            hx0P] using hwzero
    | succ k ih =>
        have hkm : k < m := by omega
        have hprevAll := ih (by omega)
        have hprev := hprevAll.1
        rcases hrec k hkm with ⟨hapos, hasq, hAnext, hy, hw, hx⟩
        have hAk := hA k (by omega)
        have hAn := hA (k + 1) (by omega)
        have hak := ha k hkm
        have hApos : 0 < data.A (k + 1) := by
          rw [hAn]
          exact O3.euclideanA_pos_of_one_le (by omega)
        have hyEq : data.y k = O3.euclideanEstimateQuery P data.M k := by
          rw [hy]
          simp only [O3.euclideanEstimateQuery, O3.euclideanBarycenter]
          rw [hAk, hAn, hak, hprev.1, hprev.2]
          rw [O3.euclideanA_succ]
          funext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp [hApos.ne']
        have hwEq : data.w (k + 1) =
            O3.euclideanEstimateMinimizer P data.M (k + 1) := by
          rw [hw]
          simp only [O3.euclideanEstimateMinimizer,
            O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer, hcum]
          rw [hx0P]
          rw [one_div]
          congr 1
          funext j
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp [hM.ne']
          apply Finset.sum_congr rfl
          intro i hi
          have him : i < k + 1 := Finset.mem_range.mp hi
          rw [ha i (by omega)]
          have hyi := if hik : i = k then by simpa [hik] using hyEq
            else hprevAll.2 i (by omega)
          rw [hyi, ← hgradP]
        refine ⟨?_, ?_⟩
        · constructor
          · rw [hx]
            rw [O3.euclideanEstimateState_succ_accelerated]
            simp only [O3.euclideanBarycenter]
            rw [hAk, hAn, hak, hprev.1, hwEq]
            rw [O3.euclideanA_succ]
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            field_simp [hApos.ne']
          · exact hwEq
        · intro i hi
          by_cases hik : i = k
          · simpa [hik] using hyEq
          · exact hprevAll.2 i (by omega)
  have hstate : ∀ k ≤ m,
      data.x k = (O3.euclideanEstimateState P data.M k).accelerated ∧
      data.w k = O3.euclideanEstimateMinimizer P data.M k :=
    fun k hk => (hstateAll k hk).1
  refine ⟨hstate, ?_⟩
  intro k hk
  rcases hrec k hk with ⟨_, _, _, hy, _, _⟩
  rw [hy]
  simp only [O3.euclideanEstimateQuery, O3.euclideanBarycenter]
  rw [hA k (by omega), hA (k + 1) (by omega), ha k hk,
    (hstate k (by omega)).1, (hstate k (by omega)).2]
  rw [O3.euclideanA_succ]
  have hApos : 0 < data.A (k + 1) := by
    rw [hA (k + 1) (by omega)]
    exact O3.euclideanA_pos_of_one_le (by omega)
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hApos.ne']

private theorem theta_eq_stage9 (data : OGMGData d n)
    (hdyn : OGMGDynamics data) :
    ∀ i ≤ n, data.theta i = O3.stage9Theta n i := by
  rcases hdyn with ⟨hn, hM, hthetaN, hu0, hvm1, hthetaOrd,
    htheta0, hrec, hvn⟩
  have hend : data.theta n = O3.stage9Theta n n := by
    rw [hthetaN, O3.stage9Theta_endpoint hn]
  have hpos : ∀ i, 1 ≤ i → i ≤ n →
      data.theta i = O3.stage9Theta n i := by
    intro i hi hin
    refine Nat.decreasingInduction' (P := fun j =>
      data.theta j = O3.stage9Theta n j) (m := i) (n := n) ?_ hin hend
    intro k hkn hik ih
    have hk1 : 1 ≤ k := le_trans hi hik
    have hdata := hthetaOrd k hk1 hkn
    rw [hdata, ih]
    rw [O3.stage9Theta_of_pos (by omega : 0 < k),
      O3.stage9Theta_of_pos (by omega : 0 < k + 1)]
    have hsub : n - k = (n - (k + 1)) + 1 := by omega
    rw [hsub, O3.ogmgThetaTail]
    rfl
  intro i hin
  by_cases hi0 : i = 0
  · subst i
    rw [htheta0, hpos 1 (by omega) hn]
    rw [O3.stage9Theta_zero, O3.ogmgThetaZero,
      O3.stage9Theta_of_pos (by omega : 0 < (1 : ℕ))]
    rfl
  · exact hpos i (Nat.one_le_iff_ne_zero.mpr hi0) hin

private theorem ogmg_data_eq_source (data : OGMGData d n)
    (hdyn : OGMGDynamics data) :
    let cfg := O3.stage9ExecutionConfig n data.oracle data.M data.U
    (∀ i ≤ n, data.u i = (O3.ogmgState cfg i).current) ∧
    (∀ i ≤ n, data.v i = O3.ogmgV cfg i) := by
  let cfg := O3.stage9ExecutionConfig n data.oracle data.M data.U
  have htheta := theta_eq_stage9 data hdyn
  rcases hdyn with ⟨hn, hMpos, hthetaN, hu0, hvm1, hthetaOrd,
    htheta0, hrec, hvn⟩
  have hM : data.M ≠ 0 := hMpos.ne'
  have hstate : ∀ i ≤ n,
      data.u i = (O3.ogmgState cfg i).current ∧
      (if i = 0 then data.vMinusOne else data.v (i - 1)) =
        (O3.ogmgState cfg i).previousV := by
    intro i hin
    induction i with
    | zero =>
        constructor
        · simpa [cfg, O3.stage9ExecutionConfig] using hu0
        · simpa [cfg, O3.stage9ExecutionConfig] using hvm1
    | succ k ih =>
        have hkn : k < n := by omega
        have hprev := ih (by omega)
        have hstep := hrec k hkn
        have hv : data.v k = O3.ogmgV cfg k := by
          rw [hstep.1, O3.ogmgV_eq, hprev.1]
          simp only [cfg, O3.stage9ExecutionConfig, O3.ogmgGradient_eq]
          rw [inv_eq_one_div]
        constructor
        · rw [hstep.2]
          rw [O3.ogmgState_succ_current]
          simp only [cfg, O3.stage9ExecutionConfig]
          rw [hv, hprev.1, hprev.2, htheta k (by omega),
            htheta (k + 1) (by omega)]
          rfl
        · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          simpa [hv] using (O3.ogmgState_succ_previousV cfg k).symm
  dsimp only
  constructor
  · intro i hi
    exact (hstate i hi).1
  · intro i hi
    by_cases hin : i < n
    · have hstep := hrec i hin
      rw [hstep.1, O3.ogmgV_eq, (hstate i hi).1]
      simp only [cfg, O3.stage9ExecutionConfig, O3.ogmgGradient_eq]
      rw [inv_eq_one_div]
    · have hieq : i = n := by omega
      subst i
      rw [hvn, O3.ogmgV_eq, (hstate n hi).1]
      simp only [cfg, O3.stage9ExecutionConfig, O3.ogmgGradient_eq]
      rw [inv_eq_one_div]

private theorem positive_fstar_eq_minimizer (inst : PositiveInstance p d x0)
    {xstar : Point d} (hxstar : xstar ∈ MinimizerSet inst.oracle) :
    inst.fstar = inst.oracle.value xstar := by
  have himage : inst.oracle.value '' MinimizerSet inst.oracle =
      {inst.oracle.value xstar} := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hxy := hxstar y
      have hyx := hy xstar
      simp only [Set.mem_singleton_iff]
      exact le_antisymm hyx hxy
    · intro hr
      simp only [Set.mem_singleton_iff] at hr
      subst r
      exact ⟨xstar, hxstar, rfl⟩
  rw [PositiveInstance.fstar, himage]
  simp

private theorem positive_radius_nonneg (inst : PositiveInstance p d x0) :
    0 ≤ inst.R := by
  rw [PositiveInstance.R, minimizerDistance, O3.minimizerDistance]
  apply le_csInf (inst.minimizerNonempty.image _)
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  exact O3.lpNorm_nonneg p (x - x0)

theorem euclideanGap : EuclideanGapStatement := by
  intro d m data hass
  rcases hass with ⟨hdyn, hDR, hxzero, hwzero, hrec, htrace, htraceEq,
    hguards, hAm⟩
  have hweights := euclidean_weights_eq_source data hdyn
  have hA := hweights.1
  have hm : 1 ≤ m := by
    by_contra hnot
    have hm0 : m = 0 := by omega
    subst m
    have hA0 := hdyn.2.1
    linarith
  have hR0 : 0 ≤ data.inst.R := by
    exact positive_radius_nonneg data.inst
  have hD0 : 0 ≤ data.D := hR0.trans hDR
  have hmiddle : data.M * data.D ^ (2 : ℕ) / (2 * data.A m) ≤
      2 * data.M * data.D ^ (2 : ℕ) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
    apply O3.euclideanGap_scalar data.M data.D
      (data.M * data.D ^ (2 : ℕ) / (2 * data.A m)) (data.A m) m
      hdyn.1 hD0 hm
    · simpa [hA m (le_refl m)] using O3.euclideanA_quadratic_lower hm
    · exact le_rfl
  obtain ⟨xstar, hxstar⟩ := data.inst.minimizerNonempty
  have hfstar := positive_fstar_eq_minimizer data.inst hxstar
  by_cases hz : ∃ z, data.inst.oracle.gradient z ≠
      data.inst.oracle.gradient data.x0
  · obtain ⟨z, hz⟩ := hz
    have hzx : z ≠ data.x0 := by
      intro h
      exact hz (congrArg data.inst.oracle.gradient h)
    let M0 := O3.secantScale 2 2 data.inst.oracle.gradient data.x0 z
    let P : O3.AdmissibleInstance d 2 :=
      { f := data.inst.oracle.value
        grad := data.inst.oracle.gradient
        L := data.inst.L
        eps := 1
        x0 := data.x0
        z0 := z
        M0 := M0
        p_gt_one := by norm_num
        L_pos := data.inst.L_pos
        eps_pos := by norm_num
        gradient_spec := data.inst.coordinateGradient
        convex := data.inst.convex
        minimizer_nonempty := data.inst.minimizerNonempty
        smooth := by
          simpa [IsLpSmooth, conjugateExponent, O3.conjugateExponent] using
            data.inst.smooth
        secant := ⟨hzx, hz, by
          norm_num [M0, O3.secantScale, O3.conjugateExponent,
            Real.conjExponent],
          O3.secantScale_pos hzx hz⟩ }
    have horacle : P.oracle = data.inst.oracle := rfl
    have hmap := euclidean_data_eq_source data P horacle rfl rfl rfl hdyn
    have haccept : O3.EuclideanEstimateAccepted P data.M m := by
      intro k hk
      have hg := hguards k hk
      have hold := (upperModelGuard_iff_historical 2 data.M data.inst.oracle
        (data.y k) (data.x (k + 1))).mp hg
      simpa [O3.euclideanEstimateGuard, O3.euclideanEstimateObservation,
        O3.AdmissibleInstance.oracle, O3.PairOracle.observe, horacle,
        hmap.2 k hk, (hmap.1 (k + 1) (by omega)).1] using hold
    have hgap := (O3.euclideanGap d P data.M data.D m hdyn.1 hm haccept
      (by simpa [P, O3.AdmissibleInstance.radius,
        PositiveInstance.R, minimizerDistance] using hDR)).2 xstar hxstar
    refine ⟨?_, hmiddle⟩
    rw [hfstar]
    simpa [P, hA m (le_refl m), (hmap.1 m (le_refl m)).1] using hgap.1
  · have hgradMin : data.inst.oracle.gradient xstar = 0 := by
      have hlocal : IsLocalMin data.inst.oracle.value xstar :=
        Filter.Eventually.of_forall hxstar
      have hfd := hlocal.fderiv_eq_zero
      have hp := (data.inst.coordinateGradient xstar).2
        (data.inst.oracle.gradient xstar)
      rw [hfd] at hp
      simp only [ContinuousLinearMap.zero_apply] at hp
      have hpair : pairing (data.inst.oracle.gradient xstar)
          (data.inst.oracle.gradient xstar) = 0 := hp.symm
      have hsq : (lpNorm 2 (data.inst.oracle.gradient xstar)) ^ (2 : ℕ) = 0 := by
        rw [← O3.pairing_self_eq_lpNorm_two_sq]
        exact hpair
      have hn := O3.lpNorm_nonneg 2 (data.inst.oracle.gradient xstar)
      have hnorm : lpNorm 2 (data.inst.oracle.gradient xstar) = 0 := by nlinarith
      exact (O3.lpNorm_eq_zero_iff (by norm_num)).mp hnorm
    have hgrad0 : ∀ x, data.inst.oracle.gradient x = 0 := by
      intro x
      have hxbase : data.inst.oracle.gradient x =
          data.inst.oracle.gradient data.x0 := by
        by_contra hne
        exact hz ⟨x, hne⟩
      have hminbase : data.inst.oracle.gradient xstar =
          data.inst.oracle.gradient data.x0 := by
        by_contra hne
        exact hz ⟨xstar, hne⟩
      rw [hxbase, ← hminbase, hgradMin]
    have hfirstOrder := O3.Stage3Anchor.firstOrderConvex_of_coordinateGradient
      data.inst.convex data.inst.coordinateGradient
    have hvalue : data.inst.oracle.value (data.x m) =
        data.inst.oracle.value xstar := by
      apply le_antisymm
      · have h := hfirstOrder (data.x m) xstar
        rw [hgrad0] at h
        simpa [pairing, O3.pairing] using h
      · exact hxstar (data.x m)
    have hfirst : data.inst.oracle.value (data.x m) - data.inst.fstar ≤
        data.M * data.D ^ (2 : ℕ) / (2 * data.A m) := by
      rw [hfstar, hvalue]
      have hnon : 0 ≤ data.M * data.D ^ (2 : ℕ) / (2 * data.A m) := by
        exact div_nonneg (mul_nonneg hdyn.1.le (sq_nonneg data.D))
          (mul_nonneg (by norm_num) hAm.le)
      linarith
    exact ⟨hfirst, hmiddle⟩

theorem finiteDataOGMG : FiniteDataOGMGStatement := by
  intro d n data hass
  rcases hass with ⟨hdyn, hconv, hgrad, hfstar, hmin, hthetaN, hu0,
    hvm1, hthetaOrd, htheta0, hrec, hvn, htrace, htraceEq, hguards,
    hqueried, hterminalV7⟩
  let cfg := O3.stage9ExecutionConfig n data.oracle data.M data.U
  have hsource := ogmg_data_eq_source data hdyn
  have hu := hsource.1
  have hv := hsource.2
  have htheta := theta_eq_stage9 data hdyn
  have hn : 1 ≤ n := hdyn.1
  have hM : 0 < data.M := hdyn.2.1
  have hall : O3.OGMGAllInterpolationGuardsHold cfg := by
    rw [O3.ogmgAllInterpolationGuardsHold_iff]
    intro i j
    have hi : i.val ≤ n := by
      simpa [cfg, O3.stage9ExecutionConfig] using Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ n := by
      simpa [cfg, O3.stage9ExecutionConfig] using Nat.le_of_lt_succ j.isLt
    have hguard := hguards i hi j hj
    simpa [O3.ogmgInterpolationCheck, O3.interpolationGuard_holds_iff,
      O3.ogmgDataObservation, EuclideanInterpolationGuard, cfg,
      O3.stage9ExecutionConfig, hu i hi, hu j hj,
      O3.ogmgObservation, O3.ogmgGradient,
      O3.PairOracle.observe] using hguard
  have hterminal : (O3.ogmgTerminalDescentCheck cfg).Holds := by
    rw [O3.ogmgTerminalDescentCheck_source_iff cfg (by
      simpa [cfg, O3.stage9ExecutionConfig] using hM)]
    simpa [TerminalDescentGuard, cfg, O3.stage9ExecutionConfig,
      hu n (le_refl n), hv n (le_refl n),
      O3.ogmgTerminalObservation, O3.ogmgObservation, O3.ogmgGradient,
      O3.PairOracle.observe] using hterminalV7
  obtain ⟨xstar, hxvalue, hxmin⟩ := hmin
  have hlower : data.fstar ≤ (O3.ogmgTerminalObservation cfg).value := by
    rw [← hxvalue]
    simpa [cfg, O3.stage9ExecutionConfig, hv n (le_refl n),
      O3.ogmgTerminalObservation,
      O3.PairOracle.observe] using hxmin (data.v n)
  have hold := O3.finiteDataOGMG d data.oracle data.U data.M data.fstar n
    hM hn hall hterminal hlower
  constructor
  · simpa [cfg, O3.stage9ExecutionConfig, hu n (le_refl n),
      htheta 0 (by omega),
      O3.ogmgGradient, O3.ogmgObservation, O3.PairOracle.observe] using hold.1
  · simpa [htheta 0 (by omega)] using hold.2

end V7
