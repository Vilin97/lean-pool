/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.HamiltonIveyReaction.Reaction
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySupportLaplacian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyScalarBarrier
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarParabolicInvariant
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity

/-!
# Parabolic Hamilton--Ivey invariant region for geometric curvature

This file joins three previously separate ingredients:

* the actual ordered curvature spectrum of a three-dimensional Riemannian
  metric;
* the Hamilton--Ivey pointwise reaction coercivity calculation; and
* the intrinsic compact-manifold scalar parabolic maximum principle.

The resulting theorem is stated directly for the eigenvalues of the genuine
curvature endomorphism.  Its remaining analytic input is the parabolic
inequality for the Hamilton--Ivey defect; this is the precise output required
from curvature evolution and the tensor/eigenvalue support argument.
-/

@[expose] public noncomputable section
open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- The Hamilton--Ivey defect evaluated on the ordered eigenvalues of the
actual three-dimensional curvature endomorphism. -/
def hamiltonIveyDefect
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) : ℝ :=
  HamiltonIveyReaction.defect K t
    (g.curvatureLambda cov hcov hLevi hdim t x)
    (g.curvatureMu cov hcov hLevi hdim t x)
    (g.curvatureNu cov hcov hLevi hdim t x)

/-- A continuous-safe version of the Hamilton--Ivey defect.  The estimate is
only asserted on the negative-spectrum region, where the logarithmic profile
is defined geometrically.  Outside that region the value is capped at `1`;
on negative spectrum, capping the defect above at `1` leaves its negative set
unchanged.  This avoids the artificial global assumption that the least
curvature eigenvalue be strictly negative everywhere. -/
def hamiltonIveyTruncatedDefect
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) : ℝ :=
  if g.curvatureNu cov hcov hLevi hdim t x < 0 then
    min (g.hamiltonIveyDefect cov hcov hLevi hdim K t x) 1
  else 1

/-- Negative values of the truncated defect are exactly bad Hamilton--Ivey
contacts with negative least eigenvalue. -/
theorem hamiltonIveyTruncatedDefect_neg_iff
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) :
    g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K t x < 0 ↔
      g.curvatureNu cov hcov hLevi hdim t x < 0 ∧
        g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 := by
  by_cases hnu : g.curvatureNu cov hcov hLevi hdim t x < 0
  · simp [hamiltonIveyTruncatedDefect, hnu]
  · simp [hamiltonIveyTruncatedDefect, hnu]

/-- At a negative contact, the truncation agrees with the original defect. -/
theorem hamiltonIveyTruncatedDefect_eq_defect_of_neg
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M)
    (hnu : g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hdefect : g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0) :
    g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K t x =
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  unfold hamiltonIveyTruncatedDefect
  rw [if_pos hnu,
    min_eq_left (show g.hamiltonIveyDefect cov hcov hLevi hdim K t x ≤ 1 by
      linarith [hdefect])]

/-- The capped Hamilton--Ivey defect is continuous across the boundary
`nu = 0` if the scalar curvature and least curvature eigenvalue are
continuous.  The key boundary estimate is geometric: `lambda, mu ≥ nu`
implies `R ≥ 3 nu`, so the logarithmic defect tends to `+∞` as `nu → 0⁻`.
Consequently the cap is identically `1` in a neighborhood of every zero
eigenvalue point. -/
theorem hamiltonIveyTruncatedDefect_continuousOn_of_scalarCurvature_and_curvatureNu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hNuCont : ContinuousOn
      (fun p : ℝ × M => g.curvatureNu cov hcov hLevi hdim p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M))) :
    ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)) := by
  let D : Set (ℝ × M) := Icc 0 T ×ˢ (Set.univ : Set M)
  let nu : ℝ × M → ℝ := fun p =>
    g.curvatureNu cov hcov hLevi hdim p.1 p.2
  let R : ℝ × M → ℝ := fun p => g.scalarCurvature cov hcov p.1 p.2
  let defect : ℝ × M → ℝ := fun p =>
    g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2
  let truncated : ℝ × M → ℝ := fun p =>
    g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K p.1 p.2
  have hformula (p : ℝ × M) :
      defect p = R p / (-nu p) - Real.log (-nu p) + 3 +
        Real.log (K / (1 + K * p.1)) := by
    dsimp [defect, R, nu, hamiltonIveyDefect,
      HamiltonIveyReaction.defect, HamiltonIveyReaction.scalar]
    rw [g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim p.1 p.2]
    simpa only [g.scalarCurvature_apply]
  intro p hp
  have hNuAt := hNuCont p hp
  have hScalarAt := hScalarCont p hp
  by_cases hnu : nu p < 0
  · have hden : ContinuousWithinAt (fun q : ℝ × M => -nu q) D p :=
      hNuAt.neg
    have hdenNe : -nu p ≠ 0 := (neg_ne_zero.mpr hnu.ne)
    have hRdiv : ContinuousWithinAt (fun q => R q / -nu q) D p :=
      hScalarAt.div hden hdenNe
    have hlogNu : ContinuousWithinAt (fun q => Real.log (-nu q)) D p :=
      hden.log hdenNe
    have htDen : 0 < 1 + K * p.1 := by
      have hpD : p ∈ D := hp
      have ht : p.1 ∈ Icc (0 : ℝ) T := hpD.1
      nlinarith [hK, ht.1]
    have htDenNe : 1 + K * p.1 ≠ 0 := ne_of_gt htDen
    have htimeDen : ContinuousWithinAt
        (fun q : ℝ × M => 1 + K * q.1) D p := by
      exact continuousWithinAt_const.add
        (continuous_fst.continuousWithinAt.const_mul K)
    have htimeQuot : ContinuousWithinAt
        (fun q : ℝ × M => K / (1 + K * q.1)) D p :=
      continuousWithinAt_const.div htimeDen htDenNe
    have htimeLog : ContinuousWithinAt
        (fun q : ℝ × M => Real.log (K / (1 + K * q.1))) D p :=
      htimeQuot.log (ne_of_gt (div_pos hK htDen))
    have hdefectCont : ContinuousWithinAt
        (fun q => R q / -nu q - Real.log (-nu q) + 3 +
          Real.log (K / (1 + K * q.1))) D p := by
      exact (hRdiv.sub hlogNu).add continuousWithinAt_const |>.add htimeLog
    have hdefectCont' : ContinuousWithinAt defect D p := by
      apply hdefectCont.congr_of_eventuallyEq
        (Filter.Eventually.of_forall hformula)
      exact hformula p
    have hnuNegative : ∀ᶠ q in 𝓝[D] p, nu q < 0 :=
      hNuAt.eventually (isOpen_Iio.mem_nhds hnu)
    have hminCont : ContinuousWithinAt
        (fun q => min (defect q) 1) D p := by
      have hpair : ContinuousWithinAt
          (fun q : ℝ × M => (defect q, (1 : ℝ))) D p :=
        hdefectCont'.prodMk continuousWithinAt_const
      have hinfFunction : Continuous
          (fun z : ℝ × ℝ => z.1 ⊓ z.2) := continuous_inf
      have hinf := hinfFunction.continuousWithinAt.comp hpair
        (by intro q hq; exact Set.mem_univ _)
      change ContinuousWithinAt (fun q => defect q ⊓ (1 : ℝ)) D p
      exact hinf
    have heq : truncated =ᶠ[𝓝[D] p] fun q => min (defect q) 1 := by
      filter_upwards [hnuNegative] with q hq
      simp [truncated, defect, nu, hamiltonIveyTruncatedDefect, hq]
    have hvalue : truncated p = min (defect p) 1 := by
      simp [truncated, defect, nu, hamiltonIveyTruncatedDefect, hnu]
    exact hminCont.congr_of_eventuallyEq heq hvalue
  · by_cases hnuZero : nu p = 0
    · let c : ℝ := Real.log (K / (1 + K * T))
      let ε : ℝ := Real.exp (c - 1)
      have hε : 0 < ε := Real.exp_pos _
      have hsmall : ∀ᶠ q in 𝓝[D] p, nu q ∈ Ioo (-ε) ε := by
        have hAtZero : nu p ∈ Ioo (-ε) ε := by
          rw [hnuZero]
          exact ⟨by linarith, hε⟩
        exact hNuAt.eventually (isOpen_Ioo.mem_nhds hAtZero)
      have hconstant : truncated =ᶠ[𝓝[D] p] fun _ => 1 := by
        filter_upwards [self_mem_nhdsWithin, hsmall] with q hqD hqsmall
        by_cases hqneg : nu q < 0
        · have hqtime : q.1 ∈ Icc (0 : ℝ) T := hqD.1
          have hqnuPos : 0 < -nu q := neg_pos.mpr hqneg
          have hqnuSmall : -nu q < ε := by linarith [hqsmall.1]
          have hdenT : 0 < 1 + K * T := by nlinarith [hK, hT]
          have hdenq : 0 < 1 + K * q.1 := by nlinarith [hK, hqtime.1]
          have hKratio : K / (1 + K * T) ≤ K / (1 + K * q.1) := by
            apply (div_le_div_iff₀ hdenT hdenq).2
            nlinarith [mul_nonneg (sq_nonneg K)
              (sub_nonneg.mpr hqtime.2)]
          have hlogratio : c ≤ Real.log (K / (1 + K * q.1)) := by
            dsimp [c]
            exact Real.log_le_log (div_pos hK hdenT) hKratio
          have hthree : 3 * nu q ≤ R q := by
            have horder₁ := g.curvatureLambda_ge_mu
              cov hcov hLevi hdim q.1 q.2
            have horder₂ := g.curvatureMu_ge_nu
              cov hcov hLevi hdim q.1 q.2
            have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
              cov hcov hLevi hdim q.1 q.2
            change 3 * g.curvatureNu cov hcov hLevi hdim q.1 q.2 ≤
              g.scalarCurvature cov hcov q.1 q.2
            rw [← hsum]
            linarith
          have hquot : -3 ≤ R q / (-nu q) := by
            have hid : (3 * nu q) / (-nu q) = -3 := by
              apply (div_eq_iff (ne_of_gt hqnuPos)).2
              ring
            calc
              -3 = (3 * nu q) / (-nu q) := hid.symm
              _ ≤ R q / (-nu q) :=
                div_le_div_of_nonneg_right hthree hqnuPos.le
          have hlogNu : Real.log (-nu q) < c - 1 := by
            calc
              Real.log (-nu q) < Real.log (Real.exp (c - 1)) :=
                Real.log_lt_log hqnuPos (by simpa [ε] using hqnuSmall)
              _ = c - 1 := Real.log_exp _
          have hdefectLower : 1 ≤ defect q := by
            rw [hformula]
            dsimp [c] at hlogratio hlogNu ⊢
            linarith
          simp [truncated, defect, nu, hamiltonIveyTruncatedDefect,
            hqneg, min_eq_right hdefectLower]
        · simp [truncated, hamiltonIveyTruncatedDefect, nu, hqneg]
      have hvalue : truncated p = 1 := by
        simp [truncated, hamiltonIveyTruncatedDefect, nu, hnuZero]
      exact continuousWithinAt_const.congr_of_eventuallyEq hconstant hvalue
    · have hnuPos : 0 < nu p := by
        rcases lt_or_eq_of_le (le_of_not_gt hnu) with h | h
        · exact h
        · exact False.elim (hnuZero h.symm)
      have hpositive : ∀ᶠ q in 𝓝[D] p, 0 < nu q :=
        hNuAt.eventually (isOpen_Ioi.mem_nhds hnuPos)
      have hconstant : truncated =ᶠ[𝓝[D] p] fun _ => 1 := by
        filter_upwards [hpositive] with q hq
        simp [truncated, hamiltonIveyTruncatedDefect, nu, not_lt.mpr hq.le]
      have hvalue : truncated p = 1 := by
        simp [truncated, hamiltonIveyTruncatedDefect, nu, not_lt.mpr hnuPos.le]
      exact continuousWithinAt_const.congr_of_eventuallyEq hconstant hvalue

/-- The zeroth-order Hamilton--Ivey reaction evaluated on the genuine
curvature spectrum. -/
def hamiltonIveyReactionTerm
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) : ℝ :=
  HamiltonIveyReaction.reaction K t
    (g.curvatureLambda cov hcov hLevi hdim t x)
    (g.curvatureMu cov hcov hLevi hdim t x)
    (g.curvatureNu cov hcov hLevi hdim t x)

/-! The spatial scalar regularity used by the barrier and support arguments
is not an independent analytic input.  On each slice it follows from the
actual curvature tensor, metric raising, and the fibrewise trace. -/

theorem scalarCurvature_mdifferentiableAt_of_curvature
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hcov₂ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 2)
    (t : ℝ) (x : M) :
    MDiffAt (g.scalarCurvature cov hcov t) x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov t) 2 := hcov₂ t
  change MDiffAt (CovariantDerivative.scalarCurvature (cov := cov t)) x
  exact RicciFlow.scalarCurvature_mdifferentiableAt_of_curvature
    (I := I) (M := M) (cov t) x

theorem eventually_mdifferentiableAt_scalarCurvature_of_curvature
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hcov₂ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 2)
    (t : ℝ) (x : M) :
    ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y := by
  exact Filter.Eventually.of_forall
    (fun y => g.scalarCurvature_mdifferentiableAt_of_curvature cov hcov hcov₂ t y)

/-! The Hilbert--Schmidt Ricci square is likewise independent of the chosen
Levi--Civita representative.  This lets intrinsic time-variation results be
transported back to the connection family used by the curvature spectrum. -/

theorem ricciNormSq_eq_of_isLeviCivita
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    {cov cov' : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)}
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hcov' : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov' t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hLevi' : g.IsLeviCivita cov') (t : ℝ) (x : M) :
    g.ricciNormSq cov hcov t x = g.ricciNormSq cov' hcov' t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov' t) 1 := hcov' t
  let b := stdOrthonormalBasis ℝ (TM x)
  change (∑ i, ∑ j,
      (g.ricciCurvature cov hcov t x (b i) (b j)) ^ 2) =
    ∑ i, ∑ j,
      (g.ricciCurvature cov' hcov' t x (b i) (b j)) ^ 2
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [g.ricciCurvature_eq_of_isLeviCivita hcov hcov' hLevi hLevi'
    t x (b i) (b j)]

/-- The smooth test defect obtained by replacing the least eigenvalue with
its genuine spacetime Rayleigh support while retaining actual scalar
curvature. -/
def hamiltonIveySupportedDefect
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M) (p : ℝ × M) : ℝ :=
    HamiltonIveyReaction.nuProfile
      (g.scalarCurvature cov hcov p.1 p.2)
      (g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p) +
    3 + Real.log (K / (1 + K * p.1))

private theorem hasDerivAt_invNeg {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / (-y)) (1 / z ^ 2) z := by
  have h := (hasDerivAt_const z (1 : ℝ)).div
    (hasDerivAt_id z).neg (neg_ne_zero.mpr hz)
  change HasDerivAt ((fun _ : ℝ => 1) / -id) (1 / z ^ 2) z
  apply h.congr_deriv
  change ((0 * (-z) - 1 * (-1)) / (-z) ^ 2) = 1 / z ^ 2
  field_simp [hz]
  ring

private theorem hasDerivAt_logNeg {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log (-y)) (1 / z) z := by
  have h := (hasDerivAt_id z).neg.log (neg_ne_zero.mpr hz)
  change HasDerivAt (fun y : ℝ => Real.log ((-id) y)) (1 / z) z
  apply h.congr_deriv
  change (-1) / (-z) = 1 / z
  field_simp [hz]

private theorem hasDerivAt_deriv_invNeg {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (deriv (fun y : ℝ => 1 / (-y))) (-2 / z ^ 3) z := by
  let A : ℝ → ℝ := fun y => 1 / (-y)
  have hAeq : deriv A =ᶠ[𝓝 z] (fun y : ℝ => 1 / y ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    have h := hasDerivAt_invNeg hy
    change deriv A y = 1 / y ^ 2
    exact h.deriv
  have hden : HasDerivAt (id ^ 2) (2 * z) z := by
    simpa [pow_one, mul_one] using (hasDerivAt_id z).pow 2
  have hJ : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / z ^ 3) z := by
    have h := (hasDerivAt_const z (1 : ℝ)).div hden (pow_ne_zero 2 hz)
    change HasDerivAt ((fun _ : ℝ => 1) / (id ^ 2))
      (-2 / z ^ 3) z
    apply h.congr_deriv
    change (0 * z ^ 2 - 1 * (2 * z)) / (z ^ 2) ^ 2 = -2 / z ^ 3
    field_simp [hz]
    ring
  have hA' : HasDerivAt (deriv A) (-2 / z ^ 3) z :=
    (hAeq.hasDerivAt_iff).2 hJ
  simpa [A] using hA'

private theorem hasDerivAt_deriv_logNeg {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (deriv (fun y : ℝ => Real.log (-y))) (-1 / z ^ 2) z := by
  let B : ℝ → ℝ := fun y => Real.log (-y)
  have hBeq : deriv B =ᶠ[𝓝 z] (fun y : ℝ => 1 / y) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    have h := hasDerivAt_logNeg hy
    change deriv B y = 1 / y
    exact h.deriv
  have hInv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / z ^ 2) z := by
    have hInv0 := (hasDerivAt_id z).inv hz
    have heq : (fun y : ℝ => 1 / y) =ᶠ[𝓝 z] (id⁻¹) := by
      filter_upwards [] with y
      simp [one_div]
    exact hInv0.congr_of_eventuallyEq heq
  have hInv' : HasDerivAt (deriv B) (-1 / z ^ 2) z :=
    (hBeq.hasDerivAt_iff).2 hInv
  simpa [B] using hInv'

/-- Intrinsic differential of the Hamilton--Ivey scalar profile.  The first
term is the scalar-curvature gradient weighted by `1/(-q)`; the second is the
support gradient weighted by the derivative of `R/(-q) - log(-q)`. -/
theorem mdifferentiableAt_nuProfile
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    {R q : M → ℝ} {x : M}
    (hR : MDiffAt R x) (hq : MDiffAt q x) (hq0 : q x ≠ 0) :
    MDiffAt (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x := by
  let A : ℝ → ℝ := fun z => 1 / (-z)
  let B : ℝ → ℝ := fun z => Real.log (-z)
  have hA : HasDerivAt A (1 / (q x) ^ 2) (q x) := by
    have h := (hasDerivAt_const (q x) (1 : ℝ)).div
      (hasDerivAt_id (q x)).neg (neg_ne_zero.mpr hq0)
    change HasDerivAt ((fun _ : ℝ => 1) / -id)
      (1 / (q x) ^ 2) (q x)
    apply h.congr_deriv
    change ((0 * (-q x) - 1 * (-1)) / (-q x) ^ 2) =
      1 / (q x) ^ 2
    field_simp [hq0]
    ring
  have hB : HasDerivAt B (1 / q x) (q x) := by
    have h := (hasDerivAt_id (q x)).neg.log (neg_ne_zero.mpr hq0)
    change HasDerivAt (fun z : ℝ => Real.log ((-id) z))
      (1 / q x) (q x)
    apply h.congr_deriv
    change (-1) / (-q x) = 1 / q x
    field_simp [hq0]
  have hAq : MDiffAt (A ∘ q) x :=
    hA.differentiableAt.comp_mdifferentiableAt hq
  have hBq : MDiffAt (B ∘ q) x :=
    hB.differentiableAt.comp_mdifferentiableAt hq
  have hprofile :
      (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) =
        R * (A ∘ q) - (B ∘ q) := by
    funext y
    change R y / (-q y) - Real.log (-q y) =
      R y * (1 / (-q y)) - Real.log (-q y)
    rw [div_eq_mul_inv, one_div]
  rw [hprofile]
  exact (hR.mul hAq).sub hBq

theorem scalarDifferential_nuProfile
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    {R q : M → ℝ} {x : M}
    (hR : MDiffAt R x) (hq : MDiffAt q x) (hq0 : q x ≠ 0) :
    CovariantDerivative.scalarDifferential (I := I)
        (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x =
      (1 / (-q x)) •
          CovariantDerivative.scalarDifferential (I := I) R x +
        ((R x - q x) / q x ^ 2) •
          CovariantDerivative.scalarDifferential (I := I) q x := by
  let A : ℝ → ℝ := fun z => 1 / (-z)
  let B : ℝ → ℝ := fun z => Real.log (-z)
  have hA : HasDerivAt A (1 / (q x) ^ 2) (q x) := by
    have h := (hasDerivAt_const (q x) (1 : ℝ)).div
      (hasDerivAt_id (q x)).neg (neg_ne_zero.mpr hq0)
    change HasDerivAt ((fun _ : ℝ => 1) / -id)
      (1 / (q x) ^ 2) (q x)
    apply h.congr_deriv
    change ((0 * (-q x) - 1 * (-1)) / (-q x) ^ 2) =
      1 / (q x) ^ 2
    field_simp [hq0]
    ring
  have hB : HasDerivAt B (1 / q x) (q x) := by
    have h := (hasDerivAt_id (q x)).neg.log (neg_ne_zero.mpr hq0)
    change HasDerivAt (fun z : ℝ => Real.log ((-id) z))
      (1 / q x) (q x)
    apply h.congr_deriv
    change (-1) / (-q x) = 1 / q x
    field_simp [hq0]
  have hAq : MDiffAt (A ∘ q) x :=
    hA.differentiableAt.comp_mdifferentiableAt hq
  have hBq : MDiffAt (B ∘ q) x :=
    hB.differentiableAt.comp_mdifferentiableAt hq
  have hprofile :
      (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) =
        R * (A ∘ q) - (B ∘ q) := by
    funext y
    change R y / (-q y) - Real.log (-q y) =
      R y * (1 / (-q y)) - Real.log (-q y)
    rw [div_eq_mul_inv, one_div]
  have hprofileDiff :
      CovariantDerivative.scalarDifferential (I := I)
          (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x =
        CovariantDerivative.scalarDifferential (I := I)
            (R * (A ∘ q)) x -
          CovariantDerivative.scalarDifferential (I := I) (B ∘ q) x := by
    ext u
    change mvfderiv (I := I)
        (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x u =
      mvfderiv (I := I) (R * (A ∘ q)) x u -
        mvfderiv (I := I) (B ∘ q) x u
    rw [hprofile, mvfderiv_sub (hR.mul hAq) hBq]
    simp only [ContinuousLinearMap.sub_apply]
  have hAqDiff :
      CovariantDerivative.scalarDifferential (I := I) (A ∘ q) x =
        (1 / (q x) ^ 2) •
          CovariantDerivative.scalarDifferential (I := I) q x := by
    ext u
    simpa [smul_eq_mul] using
      CovariantDerivative.scalarDifferential_comp_of_hasDerivAt
        (I := I) hA hq u
  have hBqDiff :
      CovariantDerivative.scalarDifferential (I := I) (B ∘ q) x =
        (1 / q x) •
          CovariantDerivative.scalarDifferential (I := I) q x := by
    ext u
    simpa [smul_eq_mul] using
      CovariantDerivative.scalarDifferential_comp_of_hasDerivAt
        (I := I) hB hq u
  rw [hprofileDiff,
    CovariantDerivative.scalarDifferential_mul (I := I) hR hAq,
    hAqDiff, hBqDiff]
  ext u
  simp [A, Function.comp_apply, smul_eq_mul]
  field_simp [hq0]
  ring

/-- Intrinsic Laplacian formula for the Hamilton--Ivey logarithmic profile.
The mixed-gradient term and the gradient square are both explicit; this is
the second-order chain-rule identity needed at a spatial contact minimum. -/
theorem scalarLaplacian_nuProfile_formula
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM) {R q : M → ℝ} {x : M}
    (hRnear : ∀ᶠ y in 𝓝 x, MDiffAt R y)
    (hqnear : ∀ᶠ y in 𝓝 x, MDiffAt q y)
    (hdR : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) R y)) x)
    (hdq : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) q y)) x)
    (hq0 : q x ≠ 0)
    (hq0near : ∀ᶠ y in 𝓝 x, q y ≠ 0) :
    CovariantDerivative.scalarLaplacian cov
        (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x =
      (1 / (-q x)) * CovariantDerivative.scalarLaplacian cov R x +
        ((R x - q x) / q x ^ 2) *
          CovariantDerivative.scalarLaplacian cov q x +
        (2 / q x ^ 2) *
          (∑ i : Fin (Module.finrank ℝ (TM x)),
            CovariantDerivative.scalarDifferential (I := I) R x
                (stdOrthonormalBasis ℝ (TM x) i) *
              CovariantDerivative.scalarDifferential (I := I) q x
                (stdOrthonormalBasis ℝ (TM x) i)) +
        ((q x - 2 * R x) / q x ^ 3) *
          (∑ i : Fin (Module.finrank ℝ (TM x)),
            (CovariantDerivative.scalarDifferential (I := I) q x
              (stdOrthonormalBasis ℝ (TM x) i)) ^ 2) := by
  let A : ℝ → ℝ := fun z => 1 / (-z)
  let B : ℝ → ℝ := fun z => Real.log (-z)
  let a : M → ℝ := A ∘ q
  let b : M → ℝ := B ∘ q
  let P : M → ℝ := R * a
  let N : M → ℝ := (-1 : ℝ) • b
  have hAnear : ∀ᶠ y in 𝓝 x,
      HasDerivAt A (deriv A (q y)) (q y) := by
    filter_upwards [hq0near] with y hy
    have h : HasDerivAt A (1 / (q y) ^ 2) (q y) := by
      simpa [A] using hasDerivAt_invNeg hy
    exact h.congr_deriv h.deriv.symm
  have hBnear : ∀ᶠ y in 𝓝 x,
      HasDerivAt B (deriv B (q y)) (q y) := by
    filter_upwards [hq0near] with y hy
    have h : HasDerivAt B (1 / q y) (q y) := by
      simpa [B] using hasDerivAt_logNeg hy
    exact h.congr_deriv h.deriv.symm
  have hA₂ : HasDerivAt (deriv A) (-2 / q x ^ 3) (q x) := by
    simpa [A] using hasDerivAt_deriv_invNeg hq0
  have hB₂ : HasDerivAt (deriv B) (-1 / q x ^ 2) (q x) := by
    simpa [B] using hasDerivAt_deriv_logNeg hq0
  have haNear : ∀ᶠ y in 𝓝 x, MDiffAt a y := by
    filter_upwards [hAnear, hqnear] with y hAy hqy
    exact hAy.differentiableAt.comp_mdifferentiableAt hqy
  have hbNear : ∀ᶠ y in 𝓝 x, MDiffAt b y := by
    filter_upwards [hBnear, hqnear] with y hBy hqy
    exact hBy.differentiableAt.comp_mdifferentiableAt hqy
  have hda : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) a y)) x :=
    CovariantDerivative.mdifferentiableAt_scalarDifferential_comp_of_hasDerivAt_deriv
      hAnear hqnear hdq hA₂
  have hdb : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) b y)) x :=
    CovariantDerivative.mdifferentiableAt_scalarDifferential_comp_of_hasDerivAt_deriv
      hBnear hqnear hdq hB₂
  have hAvalue : deriv A (q x) = 1 / q x ^ 2 := by
    simpa [A] using (hasDerivAt_invNeg hq0).deriv
  have hBvalue : deriv B (q x) = 1 / q x := by
    simpa [B] using (hasDerivAt_logNeg hq0).deriv
  have hda_apply (u : TM x) :
      scalarDifferential (I := I) a x u =
        (1 / q x ^ 2) * scalarDifferential (I := I) q x u := by
    simpa [a, A, smul_eq_mul] using
      CovariantDerivative.scalarDifferential_comp_of_hasDerivAt
        (I := I) (hasDerivAt_invNeg hq0) (hqnear.self_of_nhds) u
  have hdb_apply (u : TM x) :
      scalarDifferential (I := I) b x u =
        (1 / q x) * scalarDifferential (I := I) q x u := by
    simpa [b, B, smul_eq_mul] using
      CovariantDerivative.scalarDifferential_comp_of_hasDerivAt
        (I := I) (hasDerivAt_logNeg hq0) (hqnear.self_of_nhds) u
  have hPnear : ∀ᶠ y in 𝓝 x, MDiffAt P y := by
    filter_upwards [hRnear, haNear] with y hRy hay
    exact hRy.mul hay
  have hNnear : ∀ᶠ y in 𝓝 x, MDiffAt N y := by
    filter_upwards [hbNear] with y hby
    exact (mdifferentiableAt_const : MDiffAt (fun _ : M => (-1 : ℝ)) y).smul hby
  have hPchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) P y =
        R y • scalarDifferential (I := I) a y +
          a y • scalarDifferential (I := I) R y := by
    filter_upwards [hRnear, haNear] with y hRy hay
    exact CovariantDerivative.scalarDifferential_mul (I := I) hRy hay
  have hPsections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) P y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (R y • scalarDifferential (I := I) a y +
          a y • scalarDifferential (I := I) R y)) := by
    filter_upwards [hPchain] with y hy
    rw [hy]
  have hPdiff : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) P y)) x := by
    have hsum := mdifferentiableAt_add_section
      ((hRnear.self_of_nhds).smul_section hda)
      ((haNear.self_of_nhds).smul_section hdR)
    exact hsum.congr_of_eventuallyEq hPsections
  have hNchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) N y =
        ((-1 : ℝ) • scalarDifferential (I := I) b) y := by
    filter_upwards [hbNear] with y hby
    ext u
    simp only [scalarDifferential_apply, smul_apply]
    change mvfderiv (I := I) ((fun _ : M => (-1 : ℝ)) * b) y u =
      (-1 : ℝ) * mvfderiv (I := I) b y u
    rw [mvfderiv_mul (I := I) mdifferentiableAt_const hby]
    rw [mvfderiv_const]
    simp
  have hNsections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) N y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (((-1 : ℝ) • scalarDifferential (I := I) b) y)) := by
    filter_upwards [hNchain] with y hy
    rw [hy]
  have hNdiff : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) N y)) x := by
    have hscaled := ((mdifferentiableAt_const :
      MDiffAt (fun _ : M => (-1 : ℝ)) x).smul_section hdb)
    exact hscaled.congr_of_eventuallyEq hNsections
  have hLapA :=
    CovariantDerivative.scalarLaplacian_comp_eq_of_hasDerivAt_deriv
      cov hAnear hqnear hdq hA₂
  have hLapB :=
    CovariantDerivative.scalarLaplacian_comp_eq_of_hasDerivAt_deriv
      cov hBnear hqnear hdq hB₂
  have hLapProd :=
    CovariantDerivative.scalarLaplacian_mul_of_eventually_mdifferentiableAt
      cov hRnear haNear hdR hda
  have hLapNeg :=
    CovariantDerivative.scalarLaplacian_smul_const_of_eventually_mdifferentiableAt
      cov (-1) hbNear hdb
  have hLapProfile :
      CovariantDerivative.scalarLaplacian cov
          (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x =
        CovariantDerivative.scalarLaplacian cov P x +
          CovariantDerivative.scalarLaplacian cov N x := by
    have hprofile :
        (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) = P + N := by
      funext y
      change R y / (-q y) - Real.log (-q y) =
        R y * (1 / (-q y)) + (-1 : ℝ) * Real.log (-q y)
      rw [div_eq_mul_inv]
      ring
    rw [hprofile]
    exact CovariantDerivative.scalarLaplacian_add_of_eventually_mdifferentiableAt
      cov hPnear hNnear hPdiff hNdiff
  let e := stdOrthonormalBasis ℝ (TM x)
  let cross : ℝ := ∑ i : Fin (Module.finrank ℝ (TM x)),
    scalarDifferential (I := I) R x (e i) *
      scalarDifferential (I := I) q x (e i)
  let square : ℝ := ∑ i : Fin (Module.finrank ℝ (TM x)),
    (scalarDifferential (I := I) q x (e i)) ^ 2
  have hcross₁ :
      (∑ i : Fin (Module.finrank ℝ (TM x)),
        scalarDifferential (I := I) R x (e i) *
          scalarDifferential (I := I) a x (e i)) =
        (1 / q x ^ 2) * cross := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ (TM x)),
          (1 / q x ^ 2) *
            (scalarDifferential (I := I) R x (e i) *
              scalarDifferential (I := I) q x (e i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hda_apply]
        ring
      _ = (1 / q x ^ 2) * cross := by
        dsimp [cross]
        rw [Finset.mul_sum]
  have hcross₂ :
      (∑ i : Fin (Module.finrank ℝ (TM x)),
        scalarDifferential (I := I) a x (e i) *
          scalarDifferential (I := I) R x (e i)) =
        (1 / q x ^ 2) * cross := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ (TM x)),
          (1 / q x ^ 2) *
            (scalarDifferential (I := I) R x (e i) *
              scalarDifferential (I := I) q x (e i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hda_apply]
        ring
      _ = (1 / q x ^ 2) * cross := by
        dsimp [cross]
        rw [Finset.mul_sum]
  have hLapP :
      CovariantDerivative.scalarLaplacian cov P x =
        R x * CovariantDerivative.scalarLaplacian cov a x +
          (1 / q x ^ 2) * cross +
          a x * CovariantDerivative.scalarLaplacian cov R x +
          (1 / q x ^ 2) * cross := by
    dsimp [P]
    rw [hLapProd, hcross₁, hcross₂]
  have hLapN :
      CovariantDerivative.scalarLaplacian cov N x =
        (-1 : ℝ) * CovariantDerivative.scalarLaplacian cov b x := by
    simpa [N] using hLapNeg
  have hLapIntermediate :
      CovariantDerivative.scalarLaplacian cov
          (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x =
        R x * CovariantDerivative.scalarLaplacian cov a x +
          (1 / q x ^ 2) * cross +
          a x * CovariantDerivative.scalarLaplacian cov R x +
          (1 / q x ^ 2) * cross +
          (-1 : ℝ) * CovariantDerivative.scalarLaplacian cov b x := by
    calc
      _ = CovariantDerivative.scalarLaplacian cov P x +
          CovariantDerivative.scalarLaplacian cov N x := hLapProfile
      _ = _ := by rw [hLapP, hLapN]
  calc
    _ = R x * CovariantDerivative.scalarLaplacian cov a x +
          (1 / q x ^ 2) * cross +
          a x * CovariantDerivative.scalarLaplacian cov R x +
          (1 / q x ^ 2) * cross +
          (-1 : ℝ) * CovariantDerivative.scalarLaplacian cov b x :=
        hLapIntermediate
    _ = (1 / (-q x)) * CovariantDerivative.scalarLaplacian cov R x +
          ((R x - q x) / q x ^ 2) *
            CovariantDerivative.scalarLaplacian cov q x +
          (2 / q x ^ 2) * cross +
          ((q x - 2 * R x) / q x ^ 3) * square := by
      rw [hLapA, hLapB, hAvalue, hBvalue]
      dsimp [a, A, b, B, cross, square, e]
      field_simp [hq0]
      ring

/-- At a local minimum of the Hamilton--Ivey profile, the mixed-gradient
term in the raw Laplacian chain rule combines with the gradient-square term
to give the familiar nonpositive correction `-|d q|^2/q^2`. -/
theorem scalarLaplacian_nuProfile_eq_of_isLocalMin
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM) {R q : M → ℝ} {x : M}
    (hRnear : ∀ᶠ y in 𝓝 x, MDiffAt R y)
    (hqnear : ∀ᶠ y in 𝓝 x, MDiffAt q y)
    (hdR : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) R y)) x)
    (hdq : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) q y)) x)
    (hR : MDiffAt R x) (hq : MDiffAt q x) (hq0 : q x ≠ 0)
    (hq0near : ∀ᶠ y in 𝓝 x, q y ≠ 0)
    (hmin : IsLocalMin
      (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x) :
    CovariantDerivative.scalarLaplacian cov
        (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x =
      (1 / (-q x)) * CovariantDerivative.scalarLaplacian cov R x +
        ((R x - q x) / q x ^ 2) *
          CovariantDerivative.scalarLaplacian cov q x -
        (1 / q x ^ 2) *
          (∑ i : Fin (Module.finrank ℝ (TM x)),
            (scalarDifferential (I := I) q x
              (stdOrthonormalBasis ℝ (TM x) i)) ^ 2) := by
  have hraw := scalarLaplacian_nuProfile_formula
    (I := I) (M := M) cov hRnear hqnear hdR hdq hq0 hq0near
  have hcritical :=
    CovariantDerivative.scalarDifferential_eq_zero_of_isLocalMin
      hmin (mdifferentiableAt_nuProfile hR hq hq0)
  have hprofileDiff := scalarDifferential_nuProfile hR hq hq0
  have hzero :
      (1 / (-q x)) •
          scalarDifferential (I := I) R x +
        ((R x - q x) / q x ^ 2) •
          scalarDifferential (I := I) q x = 0 := by
    calc
      _ = scalarDifferential (I := I)
            (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x :=
          hprofileDiff.symm
      _ = 0 := hcritical
  have hgradient : scalarDifferential (I := I) R x =
      ((R x - q x) / q x) • scalarDifferential (I := I) q x := by
    ext u
    have hu := congrArg
      (fun d : (TM x →L[ℝ] ℝ) => d u) hzero
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at hu
    simp only [CovariantDerivative.scalarDifferential_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hu' : q x *
          scalarDifferential (I := I) R x u =
        (R x - q x) * scalarDifferential (I := I) q x u := by
      simp only [ContinuousLinearMap.zero_apply] at hu
      field_simp [hq0] at hu
      nlinarith [hu]
    field_simp [hq0]
    simpa only [CovariantDerivative.scalarDifferential_apply] using
      (by simpa [mul_comm] using hu')
  let e := stdOrthonormalBasis ℝ (TM x)
  let cross : ℝ := ∑ i : Fin (Module.finrank ℝ (TM x)),
    scalarDifferential (I := I) R x (e i) *
      scalarDifferential (I := I) q x (e i)
  let square : ℝ := ∑ i : Fin (Module.finrank ℝ (TM x)),
    (scalarDifferential (I := I) q x (e i)) ^ 2
  have hcross : cross = ((R x - q x) / q x) * square := by
    calc
      cross = ∑ i : Fin (Module.finrank ℝ (TM x)),
          ((R x - q x) / q x) *
            (scalarDifferential (I := I) q x (e i)) ^ 2 := by
        dsimp [cross]
        apply Finset.sum_congr rfl
        intro i hi
        have hgradient_i :
            scalarDifferential (I := I) R x (e i) =
              ((R x - q x) / q x) *
                scalarDifferential (I := I) q x (e i) := by
          have h := congrArg (fun d : TM x →L[ℝ] ℝ => d (e i)) hgradient
          simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
        change scalarDifferential (I := I) R x (e i) *
            scalarDifferential (I := I) q x (e i) =
          ((R x - q x) / q x) *
            (scalarDifferential (I := I) q x (e i)) ^ 2
        rw [hgradient_i]
        ring
      _ = ((R x - q x) / q x) * square := by
        dsimp [square]
        rw [Finset.mul_sum]
  have hcross' :
      (∑ i : Fin (Module.finrank ℝ (TM x)),
        scalarDifferential (I := I) R x
            (stdOrthonormalBasis ℝ (TM x) i) *
          scalarDifferential (I := I) q x
            (stdOrthonormalBasis ℝ (TM x) i)) =
        ((R x - q x) / q x) *
          (∑ i : Fin (Module.finrank ℝ (TM x)),
            (scalarDifferential (I := I) q x
              (stdOrthonormalBasis ℝ (TM x) i)) ^ 2) := by
    simpa [cross, square, e, CovariantDerivative.scalarDifferential_apply] using hcross
  rw [hraw, hcross']
  field_simp [hq0]
  ring

/-- At a local minimum of the Hamilton--Ivey profile, its vanishing
differential forces the scalar-curvature gradient to be a precise multiple
of the negative-eigenvalue support gradient.  This is the intrinsic
critical-point cancellation used in the profile Laplacian calculation. -/
theorem scalarDifferential_scalar_eq_of_isLocalMin_nuProfile
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    {R q : M → ℝ} {x : M}
    (hR : MDiffAt R x) (hq : MDiffAt q x) (hq0 : q x ≠ 0)
    (hmin : IsLocalMin
      (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x) :
    CovariantDerivative.scalarDifferential (I := I) R x =
      ((R x - q x) / q x) •
        CovariantDerivative.scalarDifferential (I := I) q x := by
  have hcritical :=
    CovariantDerivative.scalarDifferential_eq_zero_of_isLocalMin
      hmin (mdifferentiableAt_nuProfile hR hq hq0)
  have hprofileDiff := scalarDifferential_nuProfile hR hq hq0
  have hzero :
      (1 / (-q x)) •
          CovariantDerivative.scalarDifferential (I := I) R x +
        ((R x - q x) / q x ^ 2) •
          CovariantDerivative.scalarDifferential (I := I) q x = 0 := by
    calc
      _ = CovariantDerivative.scalarDifferential (I := I)
            (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x :=
          hprofileDiff.symm
      _ = 0 := hcritical
  ext u
  have hu := congrArg (fun d : (TangentSpace I x →L[ℝ] ℝ) => d u) hzero
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul] at hu
  simp only [CovariantDerivative.scalarDifferential_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hu' : q x *
        (CovariantDerivative.scalarDifferential (I := I) R x) u =
      (R x - q x) *
        (CovariantDerivative.scalarDifferential (I := I) q x) u := by
    simp only [ContinuousLinearMap.zero_apply] at hu
    field_simp [hq0] at hu
    nlinarith [hu]
  field_simp [hq0]
  simpa only [CovariantDerivative.scalarDifferential_apply] using
    (by simpa [mul_comm] using hu')

/-- Adding a spatially constant normalization to the profile does not change
the critical-point gradient relation. -/
theorem scalarDifferential_scalar_eq_of_isLocalMin_nuProfile_add_const
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    {R q : M → ℝ} {x : M} {c : ℝ}
    (hR : MDiffAt R x) (hq : MDiffAt q x) (hq0 : q x ≠ 0)
    (hmin : IsLocalMin
      (fun y => HamiltonIveyReaction.nuProfile (R y) (q y) + c) x) :
    CovariantDerivative.scalarDifferential (I := I) R x =
      ((R x - q x) / q x) •
        CovariantDerivative.scalarDifferential (I := I) q x := by
  have hminProfile : IsLocalMin
      (fun y => HamiltonIveyReaction.nuProfile (R y) (q y)) x := by
    rw [IsLocalMin, IsMinFilter] at hmin ⊢
    filter_upwards [hmin] with y hy
    exact (add_le_add_iff_right c).mp hy
  exact scalarDifferential_scalar_eq_of_isLocalMin_nuProfile
    hR hq hq0 hminProfile

/-! At a contact point, the support's time derivative can be propagated all
the way to the logarithmic Hamilton--Ivey defect.  This is the exact chain
rule calculation that turns the metric Ricci-flow equation and the Ricci
time-variation input into the `sdot` required by the support maximum
principle. -/

theorem hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {K t₀ : ℝ} (hK : 0 < K) {x₀ : M} (ht₀ : t₀ ∈ s)
    (ht₀_nonneg : 0 ≤ t₀)
    (hnu : g.curvatureNu cov hcov hLevi hdim t₀ x₀ < 0)
    (scalarVelocity ricciVelocity : ℝ)
    (hscalar : HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x₀) scalarVelocity t₀)
    (hricci : HasDerivAt
      (fun τ => g.ricciCurvature cov hcov τ x₀
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀))
      ricciVelocity t₀) :
    HasDerivAt
      (fun τ => g.hamiltonIveySupportedDefect
        cov hcov hLevi hdim K t₀ x₀ (τ, x₀))
      (scalarVelocity /
          (-g.curvatureNu cov hcov hLevi hdim t₀ x₀) +
        (g.scalarCurvature cov hcov t₀ x₀ -
            g.curvatureNu cov hcov hLevi hdim t₀ x₀) /
          (g.curvatureNu cov hcov hLevi hdim t₀ x₀) ^ 2 *
          (scalarVelocity - 2 * ricciVelocity -
            (g.curvatureLambda cov hcov hLevi hdim t₀ x₀ +
              g.curvatureMu cov hcov hLevi hdim t₀ x₀) ^ 2) -
        K / (1 + K * t₀)) t₀ := by
  let R : ℝ → ℝ := fun τ => g.scalarCurvature cov hcov τ x₀
  let q : ℝ → ℝ := fun τ => g.curvatureNuSpacetimeSupport
    cov hcov hLevi hdim t₀ x₀ (τ, x₀)
  have hq := g.hasDerivAt_curvatureNuSpacetimeSupport_time_eigenvalue_form
    cov hcov hLevi hdim gdot s hflow ht₀ x₀ scalarVelocity ricciVelocity
    hscalar hricci
  have hq0 : q t₀ = g.curvatureNu cov hcov hLevi hdim t₀ x₀ := by
    exact g.curvatureNuSpacetimeSupport_eq_at_contact
      cov hcov hLevi hdim t₀ x₀
  have hqneg : q t₀ < 0 := by
    rw [hq0]
    exact hnu
  have hq0ne : q t₀ ≠ 0 := hqneg.ne
  have hR : HasDerivAt R scalarVelocity t₀ := by simpa [R] using hscalar
  have hq' : HasDerivAt q
      (scalarVelocity - 2 * ricciVelocity -
        (g.curvatureLambda cov hcov hLevi hdim t₀ x₀ +
          g.curvatureMu cov hcov hLevi hdim t₀ x₀) ^ 2) t₀ := by
    simpa [q] using hq
  have hquot := hR.div hq'.neg (neg_ne_zero.mpr hq0ne)
  have hlogq := hq'.neg.log (neg_ne_zero.mpr hq0ne)
  have hden : 1 + K * t₀ ≠ 0 := by
    have hdenpos : 0 < 1 + K * t₀ := by
      nlinarith [mul_nonneg hK.le ht₀_nonneg]
    exact hdenpos.ne'
  have hlinear : HasDerivAt (fun τ : ℝ => 1 + K * τ) K t₀ := by
    have h := (hasDerivAt_const t₀ (1 : ℝ)).add
      ((hasDerivAt_id t₀).const_mul K)
    have hfun : (fun τ : ℝ => 1 + K * τ) =
        (fun x : ℝ => 1) + (fun y : ℝ => K * id y) := by
      funext τ
      simp
    rw [hfun]
    simpa only [zero_add, mul_one] using h
  have hscale := (hasDerivAt_const t₀ K).div hlinear hden
  have hlogscale := hscale.log (div_ne_zero hK.ne' hden)
  have htotal := (hquot.sub hlogq).add_const 3 |>.add hlogscale
  change HasDerivAt
    (fun τ => ((R τ) / (-q τ) - Real.log (-q τ) + 3) +
      Real.log (K / (1 + K * τ))) _ t₀
  apply htotal.congr_deriv
  simp only [R, q, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply,
    id_eq, zero_add, mul_one]
  rw [g.curvatureNuSpacetimeSupport_eq_at_contact
    cov hcov hLevi hdim t₀ x₀]
  field_simp [hnu.ne, hden, hK.ne']
  ring

/-- The supported defect touches the actual Hamilton--Ivey defect at the
chosen spacetime contact point. -/
theorem hamiltonIveySupportedDefect_eq_at_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M) :
    g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀ (t₀, x₀) =
      g.hamiltonIveyDefect cov hcov hLevi hdim K t₀ x₀ := by
  rw [hamiltonIveySupportedDefect,
    g.curvatureNuSpacetimeSupport_eq_at_contact cov hcov hLevi hdim t₀ x₀,
    hamiltonIveyDefect, HamiltonIveyReaction.defect_eq_nuProfile]
  simp only [Prod.fst, Prod.snd]
  rw [HamiltonIveyReaction.scalar]
  rw [g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t₀ x₀]

/-- Wherever the Rayleigh support is negative and `R - support` is positive,
the actual defect lies below its smooth supported representative. -/
theorem hamiltonIveyDefect_le_supportedDefect
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M) (p : ℝ × M)
    (hnuSupport : g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p)
    (hSupportNeg :
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p < 0)
    (hScalarSubSupport : 0 < g.scalarCurvature cov hcov p.1 p.2 -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p) :
    g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2 ≤
      g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀ p := by
  have h := HamiltonIveyReaction.defect_le_nuProfile_of_upper_support
    (K := K) (t := p.1)
    (lambda := g.curvatureLambda cov hcov hLevi hdim p.1 p.2)
    (mu := g.curvatureMu cov hcov hLevi hdim p.1 p.2)
    (nu := g.curvatureNu cov hcov hLevi hdim p.1 p.2)
    (q := g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p)
    hnuSupport hSupportNeg
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim p.1 p.2
  have hcond : 0 <
      HamiltonIveyReaction.scalar
          (g.curvatureLambda cov hcov hLevi hdim p.1 p.2)
          (g.curvatureMu cov hcov hLevi hdim p.1 p.2)
          (g.curvatureNu cov hcov hLevi hdim p.1 p.2) -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p := by
    rw [HamiltonIveyReaction.scalar, hsum]
    exact hScalarSubSupport
  have hout := h hcond
  simpa [hamiltonIveyDefect, hamiltonIveySupportedDefect,
    HamiltonIveyReaction.scalar, hsum] using hout

/-- At a bad contact point, the scalar-minus-support sign required for the
preceding comparison follows from the scalar barrier and the negative defect;
it is not an additional geometric assumption. -/
theorem scalarCurvature_sub_spacetimeSupport_pos_at_bad_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K t₀ : ℝ} (hK : 0 < K) (ht₀ : 0 ≤ t₀) (x₀ : M)
    (hnu : g.curvatureNu cov hcov hLevi hdim t₀ x₀ < 0)
    (hscalar : -3 * (K / (1 + K * t₀)) ≤
      g.scalarCurvature cov hcov t₀ x₀)
    (hdefect : g.hamiltonIveyDefect cov hcov hLevi hdim K t₀ x₀ < 0) :
    0 < g.scalarCurvature cov hcov t₀ x₀ -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, x₀) := by
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t₀ x₀
  have hpos := HamiltonIveyReaction.lambda_add_mu_pos_of_defect_neg hK ht₀
    (g.curvatureLambda_ge_mu cov hcov hLevi hdim t₀ x₀)
    (g.curvatureMu_ge_nu cov hcov hLevi hdim t₀ x₀) hnu
    (by simpa [HamiltonIveyReaction.scalar, hsum] using hscalar)
    (by simpa [hamiltonIveyDefect] using hdefect)
  rw [g.curvatureNuSpacetimeSupport_eq_at_contact
    cov hcov hLevi hdim t₀ x₀]
  linarith

/-- Once the three open sign/support conditions hold near a bad contact, a
local minimum of the nonsmooth eigenvalue defect transfers to the smooth
Rayleigh-supported defect.  The contact equality and comparison are both
geometric theorems proved above. -/
theorem hamiltonIveySupportedDefect_isLocalMin
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M)
    (hmin : IsLocalMin
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2) (t₀, x₀))
    (hnuSupport : ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p)
    (hSupportNeg : ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p < 0)
    (hScalarSubSupport : ∀ᶠ p in nhds (t₀, x₀),
      0 < g.scalarCurvature cov hcov p.1 p.2 -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p) :
    IsLocalMin
      (g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀)
      (t₀, x₀) := by
  rw [IsLocalMin, IsMinFilter] at hmin ⊢
  filter_upwards [hmin, hnuSupport, hSupportNeg, hScalarSubSupport] with
      p hpmin hpnu hpneg hppos
  rw [g.hamiltonIveySupportedDefect_eq_at_contact
    cov hcov hLevi hdim K t₀ x₀]
  exact hpmin.trans (g.hamiltonIveyDefect_le_supportedDefect
    cov hcov hLevi hdim K t₀ x₀ p hpnu hpneg hppos)

/-- At a negative-defect contact, ordinary continuity supplies all open
sign neighborhoods, while metric-square continuity supplies the genuine
least-eigenvalue upper support.  Thus the local-minimum transfer requires no
independent sign or comparison assumptions. -/
theorem hamiltonIveySupportedDefect_isLocalMin_at_bad_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K t₀ : ℝ} (hK : 0 < K) (ht₀ : 0 ≤ t₀) (x₀ : M)
    (hnu : g.curvatureNu cov hcov hLevi hdim t₀ x₀ < 0)
    (hscalar : -3 * (K / (1 + K * t₀)) ≤
      g.scalarCurvature cov hcov t₀ x₀)
    (hdefect : g.hamiltonIveyDefect cov hcov hLevi hdim K t₀ x₀ < 0)
    (hmin : IsLocalMin
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2) (t₀, x₀))
    (hnormContinuous : ContinuousAt
      (fun p : ℝ × M => (g p.1).inner p.2
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2))
      (t₀, x₀))
    (hScalarContinuous : ContinuousAt
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2) (t₀, x₀))
    (hSupportContinuous : ContinuousAt
      (g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀) (t₀, x₀)) :
    IsLocalMin
      (g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀)
      (t₀, x₀) := by
  have hnuSupport := g.curvatureNu_le_spacetimeSupport_eventually
    cov hcov hLevi hdim t₀ x₀ hnormContinuous
  have hSupportNegAt :
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, x₀) < 0 := by
    rw [g.curvatureNuSpacetimeSupport_eq_at_contact
      cov hcov hLevi hdim t₀ x₀]
    exact hnu
  have hSupportNeg : ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p < 0 :=
    hSupportContinuous.eventually (isOpen_Iio.mem_nhds hSupportNegAt)
  have hScalarSubSupportAt :=
    g.scalarCurvature_sub_spacetimeSupport_pos_at_bad_contact
      cov hcov hLevi hdim hK ht₀ x₀ hnu hscalar hdefect
  have hScalarSubSupport : ∀ᶠ p in nhds (t₀, x₀),
      0 < g.scalarCurvature cov hcov p.1 p.2 -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p :=
    (hScalarContinuous.sub hSupportContinuous).eventually
      (isOpen_Ioi.mem_nhds hScalarSubSupportAt)
  exact g.hamiltonIveySupportedDefect_isLocalMin cov hcov hLevi hdim
    K t₀ x₀ hmin hnuSupport hSupportNeg hScalarSubSupport

/-! ### The support-form Hamilton--Ivey maximum principle

The ordered eigenvalue fields need not be differentiable when eigenvalues
cross.  The next theorem therefore uses the exact Rayleigh-supported defect
at each hypothetical bad contact.  Its contact certificate records the three
geometric ingredients that the support construction must provide (upper
support, negativity, and the scalar-minus-support sign), together with the
actual supported-defect time derivative, spatial regularity, and parabolic
inequality.  No derivative or Laplacian of the nonsmooth ordered defect is
assumed globally.
-/

/-- Hamilton--Ivey pinching from the exact spacetime Rayleigh support.  This is
the invariant-region theorem in the form needed for a tensor maximum principle;
the remaining evolution task is to derive the contact certificate from the
Ricci-flow curvature evolution equation. -/
theorem hamiltonIveyPinching_of_spacetime_support_certificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ sdot : ℝ,
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          0 < g.scalarCurvature cov hcov p.1 p.2 -
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        HasDerivAt
          (fun τ : ℝ =>
            g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (τ, x))
          sdot t ∧
        (∀ᶠ y in 𝓝 x,
          MDiffAt
            (fun z : M =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M =>
                g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x ∧
        g.scalarLaplacian cov
            (fun _ y =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤ sdot)
    : ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let w : ℝ → M → ℝ :=
    g.hamiltonIveyDefect cov hcov hLevi hdim K
  let q : ℝ → M → ℝ :=
    g.hamiltonIveyReactionTerm cov hcov hLevi hdim K
  apply g.parabolicNonnegativeInvariant_of_upper_support cov w q hcont
  · intro t x ht hwneg
    obtain ⟨sdot, hupper, hneg, hscalarSupport, htime, hnear, hdiff, hpde⟩ :=
      hcontact ht hwneg
    refine ⟨fun p =>
        g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x p, sdot, ?_, ?_,
      htime, hnear, hdiff, hpde⟩
    · exact g.hamiltonIveySupportedDefect_eq_at_contact
        cov hcov hLevi hdim K t x
    · filter_upwards [hupper, hneg, hscalarSupport] with p hpupper hpneg hppos
      exact g.hamiltonIveyDefect_le_supportedDefect
        cov hcov hLevi hdim K t x p hpupper hpneg hppos
  · intro t ht x hwneg
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim t x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim t x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    have hscalar' :
        -3 * (K / (1 + K * t)) ≤
          HamiltonIveyReaction.scalar
            (g.curvatureLambda cov hcov hLevi hdim t x)
            (g.curvatureMu cov hcov hLevi hdim t x)
            (g.curvatureNu cov hcov hLevi hdim t x) := by
      simpa only [HamiltonIveyReaction.scalar, hsum] using hscalar t ht x
    exact (HamiltonIveyReaction.hamiltonIvey_reaction_coercive hK ht.1
      horder₁ horder₂ (hnuNeg t ht x) hscalar' hwneg).2.2
  · intro x
    have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    exact HamiltonIveyReaction.defect_zero_nonneg_of_least_eigenvalue_lower_bound
      hK
      (g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x)
      (g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x)
      (hnuNeg 0 hzero x) (hnuLower x)

/-! The standard tensor maximum-principle calculation only needs the support
PDE at the spatial minimum selected by the compactness argument.  This
variant exposes that scope instead of demanding the inequality at every
negative point. -/

theorem hamiltonIveyPinching_of_spacetime_support_certificate_at_spatial_minimum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ (s : ℝ × M → ℝ) (sdot : ℝ),
        s (t, x) = g.hamiltonIveyDefect cov hcov hLevi hdim K t x ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2 ≤ s p) ∧
        HasDerivAt (fun τ : ℝ => s (τ, x)) sdot t ∧
        (∀ᶠ y in 𝓝 x, MDiffAt (fun z : M => s (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M => s (t, z)) y)) x ∧
        (∀ hmin : IsLocalMin (fun y : M => s (t, y)) x,
          g.scalarLaplacian cov (fun _ y => s (t, y)) t x +
              g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤ sdot)) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let w : ℝ → M → ℝ :=
    g.hamiltonIveyDefect cov hcov hLevi hdim K
  let q : ℝ → M → ℝ :=
    g.hamiltonIveyReactionTerm cov hcov hLevi hdim K
  apply g.parabolicNonnegativeInvariant_of_upper_support_at_spatial_minimum
    cov w q hcont
  · intro t x ht hwneg
    obtain ⟨s, sdot, hs_touch, hs_upper, hs_time, hs_near, hs_diff, hs_pde⟩ :=
      hcontact ht hwneg
    exact ⟨s, sdot, hs_touch, hs_upper, hs_time, hs_near, hs_diff,
      hs_pde⟩
  · intro t ht x hwneg
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim t x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim t x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    have hscalar' :
        -3 * (K / (1 + K * t)) ≤
          HamiltonIveyReaction.scalar
            (g.curvatureLambda cov hcov hLevi hdim t x)
            (g.curvatureMu cov hcov hLevi hdim t x)
            (g.curvatureNu cov hcov hLevi hdim t x) := by
      simpa only [HamiltonIveyReaction.scalar, hsum] using hscalar t ht x
    exact (HamiltonIveyReaction.hamiltonIvey_reaction_coercive hK ht.1
      horder₁ horder₂ (hnuNeg t ht x) hscalar' hwneg).2.2
  · intro x
    have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    exact HamiltonIveyReaction.defect_zero_nonneg_of_least_eigenvalue_lower_bound
      hK
      (g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x)
      (g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x)
      (hnuNeg 0 hzero x) (hnuLower x)

/-! The preceding support theorem is now paired with the genuine Ricci-flow
time-variation calculation.  The contact data below expose scalar and Ricci
derivatives, while the support derivative itself is constructed internally;
there is no free `defectTimeDerivative` or arbitrary contact speed left. -/

theorem hamiltonIveyPinching_of_ricciFlow_support_certificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ scalarVelocity ricciVelocity,
        HasDerivAt
          (fun τ => g.scalarCurvature cov hcov τ x) scalarVelocity t ∧
        HasDerivAt
          (fun τ => g.ricciCurvature cov hcov τ x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x))
          ricciVelocity t ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          0 < g.scalarCurvature cov hcov p.1 p.2 -
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ y in 𝓝 x,
          MDiffAt
            (fun z : M =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M =>
                g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x ∧
        g.scalarLaplacian cov
            (fun _ y =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        scalarVelocity /
            (-g.curvatureNu cov hcov hLevi hdim t x) +
          (g.scalarCurvature cov hcov t x -
              g.curvatureNu cov hcov hLevi hdim t x) /
            (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 *
            (scalarVelocity - 2 * ricciVelocity -
              (g.curvatureLambda cov hcov hLevi hdim t x +
                g.curvatureMu cov hcov hLevi hdim t x) ^ 2) -
          K / (1 + K * t)) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  apply g.hamiltonIveyPinching_of_spacetime_support_certificate
    cov hcov hLevi hdim hK hT hnuNeg hnuLower hscalar hcont
  intro t x ht hdefect
  obtain ⟨scalarVelocity, ricciVelocity, hscalarTime, hricciTime,
    hupper, hneg, hscalarSupport, hnear, hdiff, hpde⟩ := hcontact ht hdefect
  let sdot : ℝ :=
    scalarVelocity /
        (-g.curvatureNu cov hcov hLevi hdim t x) +
      (g.scalarCurvature cov hcov t x -
          g.curvatureNu cov hcov hLevi hdim t x) /
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 *
        (scalarVelocity - 2 * ricciVelocity -
          (g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x) ^ 2) -
      K / (1 + K * t)
  refine ⟨sdot, hupper, hneg, hscalarSupport, ?_, hnear, hdiff, ?_⟩
  · exact g.hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
      cov hcov hLevi hdim gdot (Icc 0 T) hflow hK ht ht.1
      (hnuNeg t ht x) scalarVelocity ricciVelocity hscalarTime hricciTime
  · simpa [sdot] using hpde

/-- Hamilton--Ivey pinching for the genuine geometric curvature spectrum,
from the scalar lower barrier and the parabolic defect inequality supplied by
curvature evolution and the least-eigenvalue support construction. -/
theorem hamiltonIveyPinching_of_defect_parabolic_inequality
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (defectTimeDerivative : ℝ → M → ℝ)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt
        (fun s => g.hamiltonIveyDefect cov hcov hLevi hdim K s x)
        (defectTimeDerivative t x) t)
    (hfNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x,
        MDiffAt (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)
    (hdf : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I)
            (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)) x)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.scalarLaplacian cov
          (g.hamiltonIveyDefect cov hcov hLevi hdim K) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        defectTimeDerivative t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let w : ℝ → M → ℝ :=
    g.hamiltonIveyDefect cov hcov hLevi hdim K
  let q : ℝ → M → ℝ :=
    g.hamiltonIveyReactionTerm cov hcov hLevi hdim K
  apply g.parabolicNonnegativeInvariant cov w defectTimeDerivative q hcont htime
      hfNear hdf hpde
  · intro t ht x hwneg
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim t x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim t x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    have hscalar' :
        -3 * (K / (1 + K * t)) ≤
          HamiltonIveyReaction.scalar
            (g.curvatureLambda cov hcov hLevi hdim t x)
            (g.curvatureMu cov hcov hLevi hdim t x)
            (g.curvatureNu cov hcov hLevi hdim t x) := by
      simpa only [HamiltonIveyReaction.scalar, hsum] using hscalar t ht x
    exact (HamiltonIveyReaction.hamiltonIvey_reaction_coercive hK ht.1
      horder₁ horder₂ (hnuNeg t ht x) hscalar' hwneg).2.2
  · intro x
    have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    exact HamiltonIveyReaction.defect_zero_nonneg_of_least_eigenvalue_lower_bound
      hK
      (g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x)
      (g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x)
      (hnuNeg 0 hzero x) (hnuLower x)

/-- Geometric Hamilton--Ivey pinching from the exact scalar-curvature
evolution equation and the parabolic defect inequality.  The scalar lower
barrier required by reaction coercivity is derived internally from the
initial least-eigenvalue bound. -/
theorem hamiltonIveyPinching_of_scalar_evolution_and_defect_parabolic_inequality
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t)
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (defectTimeDerivative : ℝ → M → ℝ)
    (hDefectCont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hDefectTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt
        (fun s => g.hamiltonIveyDefect cov hcov hLevi hdim K s x)
        (defectTimeDerivative t x) t)
    (hDefectNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x,
        MDiffAt (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)
    (hDefectDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I)
            (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)) x)
    (hDefectPDE : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.scalarLaplacian cov
          (g.hamiltonIveyDefect cov hcov hLevi hdim K) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        defectTimeDerivative t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hScalarInitial : ∀ x : M,
      -(3 : ℝ) * K ≤ g.scalarCurvature cov hcov 0 x := by
    intro x
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim 0 x
    have hthreeNu :
        3 * g.curvatureNu cov hcov hLevi hdim 0 x ≤
          g.curvatureLambda cov hcov hLevi hdim 0 x +
            g.curvatureMu cov hcov hLevi hdim 0 x +
            g.curvatureNu cov hcov hLevi hdim 0 x := by
      linarith
    rw [hsum] at hthreeNu
    linarith [hnuLower x]
  have hScalarStrong := g.scalarCurvature_lowerBarrier_of_evolution cov hcov hdim
    hK.le hScalarCont hScalarTime hScalarNear hScalarDifferential hScalarInitial
  have hScalarWeak : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x := by
    intro t ht x
    have hden₁ : 0 < 1 + K * t := by
      nlinarith [mul_nonneg hK.le ht.1]
    have hden₂ : 0 < 1 + 2 * K * t := by
      nlinarith [mul_nonneg hK.le ht.1]
    have hcompare :
        -3 * (K / (1 + K * t)) ≤
          -(3 : ℝ) * K / (1 + 2 * K * t) := by
      calc
        -3 * (K / (1 + K * t)) =
            (-(3 : ℝ) * K) / (1 + K * t) := by ring
        _ ≤ (-(3 : ℝ) * K) / (1 + 2 * K * t) := by
          rw [div_le_div_iff₀ hden₁ hden₂]
          nlinarith [mul_nonneg (sq_nonneg K) ht.1]
    exact hcompare.trans (hScalarStrong t ht x)
  exact g.hamiltonIveyPinching_of_defect_parabolic_inequality cov hcov hLevi hdim
    hK hT hnuNeg hnuLower hScalarWeak defectTimeDerivative hDefectCont
    hDefectTime hDefectNear hDefectDifferential hDefectPDE

/-! The logarithmic defect is only a meaningful pinching quantity when the
least eigenvalue is negative.  The clipped invariant below lets the compact
maximum principle operate on the whole spacetime slab without requiring that
sign everywhere.  A negative contact automatically lies in the region where
the original defect and its genuine Rayleigh support are defined. -/

/-- Hamilton--Ivey pinching on the negative-spectrum region, without assuming
that the least curvature eigenvalue is negative everywhere.  Continuity is
required only for the capped quantity actually used by the compact maximum
principle.  At a negative contact, the upper support is required to touch the
original logarithmic defect and to dominate it near the contact; these are
precisely the properties supplied by the geometric Rayleigh-support
construction. -/
theorem hamiltonIveyPinching_of_truncatedDefect_support_certificate_at_spatial_minimum
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ (s : ℝ × M → ℝ) (sdot : ℝ),
        s (t, x) = g.hamiltonIveyDefect cov hcov hLevi hdim K t x ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2 ≤ s p) ∧
        HasDerivAt (fun τ : ℝ => s (τ, x)) sdot t ∧
        (∀ᶠ y in 𝓝 x, MDiffAt (fun z : M => s (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M => s (t, z)) y)) x ∧
        (∀ hmin : IsLocalMin (fun y : M => s (t, y)) x,
          g.scalarLaplacian cov (fun _ y => s (t, y)) t x +
              g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤ sdot)) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
        0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let w : ℝ → M → ℝ := g.hamiltonIveyTruncatedDefect
    cov hcov hLevi hdim K
  let reaction : ℝ → M → ℝ := g.hamiltonIveyReactionTerm
    cov hcov hLevi hdim K
  have hinitial : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    by_cases hnu : g.curvatureNu cov hcov hLevi hdim 0 x < 0
    · have hdefect :=
        HamiltonIveyReaction.defect_zero_nonneg_of_least_eigenvalue_lower_bound
          hK
          (g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x)
          (g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x)
          hnu (hnuLower x)
      have hdefect' :
          0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K 0 x := by
        simpa [hamiltonIveyDefect] using hdefect
      change 0 ≤ g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K 0 x
      unfold hamiltonIveyTruncatedDefect
      rw [if_pos hnu]
      exact le_min hdefect' (by norm_num)
    · simp [w, hamiltonIveyTruncatedDefect, hnu]
  have hreaction : ∀ t ∈ Icc 0 T, ∀ x : M,
      w t x < 0 → 0 < reaction t x := by
    intro t ht x hw
    have hbad :=
      (g.hamiltonIveyTruncatedDefect_neg_iff cov hcov hLevi hdim K t x).mp hw
    obtain ⟨hnu, hdefect⟩ := hbad
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim t x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim t x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    have hscalar' :
        -3 * (K / (1 + K * t)) ≤
          HamiltonIveyReaction.scalar
            (g.curvatureLambda cov hcov hLevi hdim t x)
            (g.curvatureMu cov hcov hLevi hdim t x)
            (g.curvatureNu cov hcov hLevi hdim t x) := by
      simpa only [HamiltonIveyReaction.scalar, hsum] using hscalar t ht x
    exact (HamiltonIveyReaction.hamiltonIvey_reaction_coercive hK ht.1
      horder₁ horder₂ hnu hscalar' hdefect).2.2
  have hw := g.parabolicNonnegativeInvariant_of_upper_support_at_spatial_minimum
    cov w reaction hcont
    (by
      intro t x ht hwneg
      have hbad :=
        (g.hamiltonIveyTruncatedDefect_neg_iff cov hcov hLevi hdim K t x).mp
          hwneg
      obtain ⟨hnu, hdefect⟩ := hbad
      obtain ⟨s, sdot, hs_touch, hnu_near, hs_upper, hs_time,
        hs_near, hs_diff, hs_pde⟩ := hcontact ht hnu hdefect
      refine ⟨s, sdot, ?_, ?_, hs_time, hs_near, hs_diff, ?_⟩
      · change s (t, x) =
          g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K t x
        rw [g.hamiltonIveyTruncatedDefect_eq_defect_of_neg
          cov hcov hLevi hdim K t x hnu hdefect]
        exact hs_touch
      · filter_upwards [hnu_near, hs_upper] with p hpnu hpupper
        change g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K
            p.1 p.2 ≤ s p
        rw [hamiltonIveyTruncatedDefect, if_pos hpnu]
        exact (min_le_left _ _).trans hpupper
      · simpa [reaction] using hs_pde)
    hreaction hinitial
  intro t ht x hnu
  have htruncated :
      0 ≤ g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K t x := by
    simpa [w] using hw t ht x
  by_cases hdefect : g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 1
  · have heq :
        g.hamiltonIveyTruncatedDefect cov hcov hLevi hdim K t x =
          g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
      unfold hamiltonIveyTruncatedDefect
      rw [if_pos hnu, min_eq_left hdefect.le]
    rw [heq] at htruncated
    exact htruncated
  · linarith

end CovariantDerivative.TimeDependentRiemannianMetric
