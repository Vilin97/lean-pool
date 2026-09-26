/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.QueryGap

/-!
The completed resisting objective's gradient remains large outside the central region.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AFinalRepair
open Stage5AboveTwoLowerResume

/-- Every supporting vector of the nonzero `ell_p` norm has exact dual norm
one.  The upper estimate uses the repository's kernel-closed norming vector. -/
lemma lpNorm_supporting_vector_dual_norm_eq_one {p : ℝ} (hp : 1 < p)
    {y g : Point d} (hy : y ≠ 0)
    (hsupport : ∀ z : Point d,
      lpNorm p y + O3.pairing g (z - y) ≤ lpNorm p z) :
    lpNorm (conjugateExponent p) g = 1 := by
  have hynorm : 0 < lpNorm p y := O3.lpNorm_pos_of_ne_zero hy
  have hpairLower : lpNorm p y ≤ O3.pairing g y := by
    have h := hsupport 0
    have hzero : lpNorm p (0 : Point d) = 0 :=
      O3.lpNorm_zero (by linarith : 0 < p)
    have hneg : O3.pairing g ((0 : Point d) - y) = -O3.pairing g y := by
      simp [O3.pairing]
    rw [hzero, hneg] at h
    linarith
  have hholder := O3.pairing_le_lpNorm_mul
    (O3.holderConjugate_conjugateExponent hp).symm g y
  have hlower : 1 ≤ lpNorm (conjugateExponent p) g := by
    nlinarith [O3.lpNorm_nonneg (conjugateExponent p) g]
  have hgNorm : 0 < lpNorm (conjugateExponent p) g := lt_of_lt_of_le zero_lt_one hlower
  obtain ⟨hwNorm, hwPair⟩ := V7.normingDirection_correct p hp d g hgNorm
  let w := normingDirection (conjugateExponent p) g
  have hsupportW := hsupport (y + w)
  have htriangle := lpNorm_add_le hp.le y w
  have hsub : y + w - y = w := by module
  rw [hsub] at hsupportW
  change lpNorm p y + pairing g w ≤ lpNorm p (y + w) at hsupportW
  change lpNorm p (y + w) ≤ lpNorm p y + lpNorm p w at htriangle
  change lpNorm p w = 1 at hwNorm
  change pairing g w = lpNorm (conjugateExponent p) g at hwPair
  rw [hwPair] at hsupportW
  rw [hwNorm] at htriangle
  have hupper : lpNorm (conjugateExponent p) g ≤ 1 := by linarith
  exact le_antisymm hupper hlower

/-- Convexity and the frozen strict unit-sphere boundary condition propagate
to the all-radii barrier required by compact-ball attainment. -/
lemma kernel_radial_barrier_of_unit_boundary
    (kernel : SmoothingKernelData p d) (hp : 1 ≤ p)
    (hconv : O3.IsConvexObjective kernel.phi)
    (hphi0 : kernel.phi 0 = 0)
    (hboundary : ∀ u, lpNorm p u = 1 → kernel.phi u > lpNorm p u) :
    ∀ u : Point d, 1 ≤ lpNorm p u → lpNorm p u < kernel.phi u := by
  intro u hu
  let r := lpNorm p u
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hu
  let w : Point d := (1 / r) • u
  have hw : lpNorm p w = 1 := by
    change O3.lpNorm p ((1 / r) • u) = 1
    rw [O3.Stage2RouteC.lpNorm_smul hp, abs_of_pos (one_div_pos.mpr hr)]
    change (1 / r) * r = 1
    field_simp [hr.ne']
  have hstrict := hboundary w hw
  rw [hw] at hstrict
  have ha : 0 ≤ (1 / r : ℝ) := (one_div_pos.mpr hr).le
  have hb : 0 ≤ (1 - 1 / r : ℝ) := by
    rw [sub_nonneg, div_le_one hr]
    exact hu
  have hab : (1 / r : ℝ) + (1 - 1 / r) = 1 := by ring
  have hc := hconv.2 (Set.mem_univ u) (Set.mem_univ (0 : Point d)) ha hb hab
  have hpoint : (1 / r : ℝ) • u + (1 - 1 / r : ℝ) • (0 : Point d) = w := by
    simp [w]
  rw [hpoint, hphi0] at hc
  simp only [smul_eq_mul, mul_zero, add_zero] at hc
  have honeDiv : 1 < kernel.phi u / r := by
    rw [div_eq_mul_inv, mul_comm]
    exact lt_of_lt_of_le hstrict (by simpa [one_div] using hc)
  change r < kernel.phi u
  simpa using (lt_div_iff₀ hr).mp honeDiv

/-- A global supporting vector of a genuinely differentiable value is its
actual coordinate gradient.  This is Fermat's theorem applied after removing
the supporting affine functional. -/
lemma supporting_vector_eq_coordinate_gradient
    (f : Point d → ℝ) (gradient : Point d → Point d) (x g : Point d)
    (hgradient : O3.IsCoordinateGradient f gradient)
    (hsupport : ∀ z, f x + O3.pairing g (z - x) ≤ f z) :
    g = gradient x := by
  let F : Point d → ℝ := fun z => f z - pairingCLM g z
  have hmin : ∀ z, F x ≤ F z := by
    intro z
    have hs := hsupport z
    dsimp [F]
    rw [pairingCLM_apply, pairingCLM_apply]
    simp only [O3.pairing, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib] at hs ⊢
    linarith
  have hlocal : IsLocalMin F x := Filter.Eventually.of_forall hmin
  have hder : HasFDerivAt F
      (pairingCLM (gradient x) - pairingCLM g) x := by
    have hfder : HasFDerivAt f (pairingCLM (gradient x)) x := by
      convert (hgradient x).1.hasFDerivAt using 1
      ext h
      simpa [pairingCLM_apply] using ((hgradient x).2 h).symm
    exact hfder.sub (pairingCLM g).hasFDerivAt
  have hzero := hlocal.hasFDerivAt_eq_zero hder
  funext i
  have happ := congrArg (fun L : Point d →L[ℝ] ℝ => L (coordinateUnit i)) hzero
  simp only [sub_apply, pairingCLM_apply, zero_apply] at happ
  simp [O3.pairing, coordinateUnit] at happ
  linarith

lemma shiftedLpNorm_convex_oneLipschitz {p c : ℝ} (hp : 1 ≤ p) :
    O3.IsConvexObjective (fun x : Point d => lpNorm p x - c) ∧
      IsOneLipschitz p (fun x : Point d => lpNorm p x - c) := by
  constructor
  · unfold O3.IsConvexObjective
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hn := (convexOn_lpNorm (d := d) hp).2
      (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have hc := congrArg (fun z : ℝ => z * c) hab
    simp only [smul_eq_mul] at hn ⊢
    nlinarith
  · intro x y
    have hxy := lpNorm_add_le hp (x - y) y
    have hyx := lpNorm_add_le hp (y - x) x
    have hneg : lpNorm p (y - x) = lpNorm p (x - y) := by
      rw [show y - x = -(x - y) by module]
      change O3.lpNorm p (-(x - y)) = O3.lpNorm p (x - y)
      simpa using O3.Stage2RouteC.lpNorm_smul hp (-1 : ℝ) (x - y)
    rw [show x - y + y = x by module] at hxy
    rw [show y - x + x = y by module, hneg] at hyx
    rw [show lpNorm p x - c - (lpNorm p y - c) =
      lpNorm p x - lpNorm p y by ring]
    exact abs_le.2 ⟨by linarith, by linarith⟩

lemma partialG_le_lpNorm (data : LowerCompletionData p d T)
    {t : ℕ} (hp : 1 ≤ p) (hdelta : 0 ≤ data.delta)
    (hxi : ∀ i ≤ t, data.xi i = 1 ∨ data.xi i = -1)
    (hres : ResistingMaximumAt data t) (x : Point d) :
    data.partialG t x ≤ lpNorm p x := by
  obtain ⟨i, hit, hiEq⟩ := (hres x).2
  rw [hiEq]
  have hcoord := norm_apply_le_lpNorm hp x (data.sigma i)
  rcases hxi i hit with hxiI | hxiI <;> rw [hxiI] <;> norm_num
  · nlinarith [le_abs_self (x (data.sigma i)),
      mul_nonneg (Nat.cast_nonneg i) hdelta]
  · nlinarith [neg_le_abs (x (data.sigma i)),
      mul_nonneg (Nat.cast_nonneg i) hdelta]

lemma partialH_eq_shiftedLpNorm_of_three_le
    (data : LowerCompletionData p d T) {t : ℕ}
    (hp : 1 ≤ p) (hdelta : 0 ≤ data.delta)
    (hxi : ∀ i ≤ t, data.xi i = 1 ∨ data.xi i = -1)
    (hres : ResistingMaximumAt data t)
    (hH : ∀ x, data.partialH t x =
      max (data.partialG t x / 2) (lpNorm p x - 3 / 2))
    {x : Point d} (hx : 3 ≤ lpNorm p x) :
    data.partialH t x = lpNorm p x - 3 / 2 := by
  rw [hH]
  apply max_eq_right
  have hG := partialG_le_lpNorm data hp hdelta hxi hres x
  linarith

lemma smooth_shiftedLpNorm_gradient_dual_norm_eq_one
    (kernel : SmoothingKernelData p d) (hp : 1 < p)
    {chi : ℝ} (hchi : 0 < chi)
    (hkernel : SmoothingKernelAssumptions kernel)
    {x : Point d} (hx : chi < lpNorm p x) :
    lpNorm (conjugateExponent p)
      ((kernel.smooth chi (fun z => lpNorm p z - 3 / 2)).gradient x) = 1 := by
  obtain ⟨hM, hconvPhi, hC2, hgradPhi, hHessian, hphiNonneg, hphi0,
    hgrad0, hboundary, hquad, hsymm, hvalue, hsmooth, hlocal, hequiv⟩ := hkernel
  let ell : Point d → ℝ := fun z => lpNorm p z - 3 / 2
  have hell := shiftedLpNorm_convex_oneLipschitz (d := d) hp.le (c := (3 / 2 : ℝ))
  have hphiContinuous : Continuous kernel.phi := hC2.continuous
  have hradial := kernel_radial_barrier_of_unit_boundary kernel hp.le
    hconvPhi hphi0 hboundary
  have hex : ∀ z : Point d, ∃ v : Point d,
      IsInfimalMinimizer kernel chi ell z v ∧ lpNorm p v < chi := by
    intro z
    exact exists_infimal_minimizer_of_radial_kernel kernel hchi ell z hp.le
      hell.2 hphiContinuous hphi0 hradial
  obtain ⟨v, hv, hvNorm⟩ := hex x
  let y := x + v
  have hy : y ≠ 0 := by
    intro hy0
    have hvx : v = -x := by
      dsimp [y] at hy0
      funext i
      have hi := congrFun hy0 i
      simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hi ⊢
      linarith
    have hnormvx : lpNorm p v = lpNorm p x := by
      rw [hvx]
      exact O3.lpNorm_neg p x
    linarith
  let g : Point d := -kernel.gradPhi ((1 / chi) • v)
  have hellSupport : ∀ z : Point d,
      lpNorm p y + O3.pairing g (z - y) ≤ lpNorm p z := by
    intro z
    have hs := minimizer_supporting_inequality kernel hchi ell hell.1 hgradPhi hv z
    change ell y + O3.pairing g (z - y) ≤ ell z at hs
    dsimp [ell] at hs
    linarith
  have hgNorm := lpNorm_supporting_vector_dual_norm_eq_one hp hy hellSupport
  have hlocalSupport : ∀ z : Point d,
      localSmoothingValue kernel chi ell x + O3.pairing g (z - x) ≤
        localSmoothingValue kernel chi ell z := by
    intro z
    exact localSmoothingValue_supporting_of_minimizers kernel hchi ell hell.1
      hconvPhi hgradPhi hv (hex z).choose_spec.1
  have hsmoothSupport : ∀ z : Point d,
      (kernel.smooth chi ell).value x + O3.pairing g (z - x) ≤
        (kernel.smooth chi ell).value z := by
    intro z
    simpa [hvalue chi hchi ell hell.1 hell.2 x,
      hvalue chi hchi ell hell.1 hell.2 z] using hlocalSupport z
  have hgeq : g = (kernel.smooth chi ell).gradient x :=
    supporting_vector_eq_coordinate_gradient (kernel.smooth chi ell).value
      (kernel.smooth chi ell).gradient x g
      (hsmooth chi hchi ell hell.1 hell.2).1 hsmoothSupport
  change lpNorm (conjugateExponent p) ((kernel.smooth chi ell).gradient x) = 1
  rw [← hgeq]
  exact hgNorm

lemma coordinateGradient_eq_zero_of_global_minimizer
    (f : Point d → ℝ) (gradient : Point d → Point d) (x : Point d)
    (hgradient : O3.IsCoordinateGradient f gradient)
    (hmin : ∀ y, f x ≤ f y) : gradient x = 0 := by
  have hlocal : IsLocalMin f x := Filter.Eventually.of_forall hmin
  have hfder : HasFDerivAt f (pairingCLM (gradient x)) x := by
    convert (hgradient x).1.hasFDerivAt using 1
    ext h
    simpa [pairingCLM_apply] using ((hgradient x).2 h).symm
  have hzero := hlocal.hasFDerivAt_eq_zero hfder
  funext i
  have happ := congrArg (fun L : Point d →L[ℝ] ℝ => L (coordinateUnit i)) hzero
  simp only [pairingCLM_apply, zero_apply] at happ
  simpa [O3.pairing, coordinateUnit] using happ

/-- Frozen S5-D outside-gradient and optimizer-interiority package. -/
theorem _root_.V7.aboveLowerOutsideGradient : AboveLowerOutsideGradientStatement := by
  intro p hp d T data hassum
  rcases hassum with ⟨hcompletion, hobjectiveConvex, hobjectiveGradient⟩
  let base := data.toLowerCompletionData
  rcases hcompletion with
    ⟨hp', hd, hT, hTd, hx0, hkernel, hDelta, hdelta, hchi, hbeta,
      hqueries, hsteps, hcompletedValue, hcompletedGradient⟩
  have hpOne : 1 ≤ p := by linarith
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hDeltaPos : 0 < base.Delta := by rw [hDelta]; positivity
  have hDeltaLe : base.Delta ≤ 1 := by
    rw [hDelta]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith : 0 ≤ p))
  have hdeltaPos : 0 < base.delta := by rw [hdelta]; positivity
  have hchiPos : 0 < base.chi := by rw [hchi]; positivity
  have hchiLe : base.chi ≤ 1 := by
    rw [hchi, hdelta]
    have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hden : 1 ≤ (2 : ℝ) * T := by nlinarith
    have hfrac : base.Delta / ((2 : ℝ) * T) ≤ base.Delta :=
      div_le_self hDeltaPos.le hden
    nlinarith
  have hbetaPos : 0 < base.beta := by
    rw [hbeta]
    exact div_pos hchiPos hkernel.1
  have hlast : T - 1 < T := by omega
  let shortSteps : ∀ s < T,
      (base.xi s = 1 ∨ base.xi s = -1) ∧ ResistingMaximumAt base s :=
    fun s hs => ⟨(hsteps s hs).2.2.2.1, (hsteps s hs).2.2.2.2.2.1⟩
  have hpartialLast := partialH_convex_oneLipschitz base hpOne hlast shortSteps
    (hsteps (T - 1) hlast).2.2.2.2.2.2.1
  have hkernelFull := hkernel
  have houtside : ∀ x, 4 ≤ lpNorm p x →
      lpNorm (conjugateExponent p)
        ((base.kernel.smooth base.chi (base.partialH (T - 1))).gradient x) = 1 ∧
      lpNorm (conjugateExponent p) (data.completedOracle.gradient x) = base.beta := by
    intro x hx
    let ell : Point d → ℝ := fun z => lpNorm p z - 3 / 2
    have hell := shiftedLpNorm_convex_oneLipschitz (d := d) hpOne (c := (3 / 2 : ℝ))
    have hnear : ∀ v, lpNorm p v ≤ base.chi →
        base.partialH (T - 1) (x + v) = ell (x + v) := by
      intro v hv
      have htri := lpNorm_add_le hpOne (x + v) (-v)
      have hsum : x + v + -v = x := by module
      rw [hsum] at htri
      change O3.lpNorm p x ≤ O3.lpNorm p (x + v) + O3.lpNorm p (-v) at htri
      rw [O3.lpNorm_neg] at htri
      have hnorm : 3 ≤ lpNorm p (x + v) := by linarith
      exact partialH_eq_shiftedLpNorm_of_three_le base hpOne hdeltaPos.le
        (fun i hi => (hsteps i (lt_of_le_of_lt hi hlast)).2.2.2.1)
        (hsteps (T - 1) hlast).2.2.2.2.2.1
        (hsteps (T - 1) hlast).2.2.2.2.2.2.1 hnorm
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsmooth, hlocal, -⟩ := hkernel
    have hobs := hlocal base.chi hchiPos (base.partialH (T - 1)) ell
      hpartialLast.1 hpartialLast.2 hell.1 hell.2 x hnear
    have hgradEq := congrArg O3.Observation.gradient hobs
    change (base.kernel.smooth base.chi (base.partialH (T - 1))).gradient x =
      (base.kernel.smooth base.chi ell).gradient x at hgradEq
    have hshiftNorm := smooth_shiftedLpNorm_gradient_dual_norm_eq_one
      base.kernel (by linarith) hchiPos hkernelFull (by linarith : base.chi < lpNorm p x)
    have hsmoothNorm : lpNorm (conjugateExponent p)
        ((base.kernel.smooth base.chi (base.partialH (T - 1))).gradient x) = 1 := by
      rw [hgradEq]
      exact hshiftNorm
    refine ⟨hsmoothNorm, ?_⟩
    rw [hcompletedGradient]
    change O3.lpNorm (conjugateExponent p)
      (base.beta • (base.kernel.smooth base.chi (base.partialH (T - 1))).gradient x) =
      base.beta
    rw [O3.Stage2RouteC.lpNorm_smul
      (O3.one_lt_conjugateExponent (by linarith : 1 < p)).le,
      abs_of_pos hbetaPos]
    change O3.lpNorm (O3.conjugateExponent p)
      ((base.kernel.smooth base.chi (base.partialH (T - 1))).gradient x) = 1 at hsmoothNorm
    rw [hsmoothNorm, mul_one]
  refine ⟨houtside, ?_⟩
  intro x hmin
  have hgradZero := coordinateGradient_eq_zero_of_global_minimizer
    data.completedOracle.value data.completedOracle.gradient x hobjectiveGradient hmin
  by_contra hx
  have hxout : 4 ≤ lpNorm p x := le_of_not_gt hx
  have hnormBeta := (houtside x hxout).2
  rw [hgradZero] at hnormBeta
  change O3.lpNorm (O3.conjugateExponent p) 0 = base.beta at hnormBeta
  rw [O3.lpNorm_zero (by
    exact lt_trans zero_lt_one (O3.one_lt_conjugateExponent (by linarith : 1 < p)))] at hnormBeta
  linarith

end V7.Stage5AboveTwoLowerS5A2Envelope
