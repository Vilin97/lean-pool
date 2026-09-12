/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.EvenSmoothDescent
import LeanPool.NavierStokesAndEuler.NavierStokes.HolomorphicFamily
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase
import LeanPool.NavierStokesAndEuler.NavierStokes.VolterraRegularity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Canonical axis jets without a negative squared-radius extension

The squared-radius jets are the iterates of the integral Hadamard operator
on the signed radial variable.  They are genuine right derivatives at the
axis and genuine ordinary derivatives at positive squared radius.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff

namespace NavierStokes.BoundaryAxisJets

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Radial jet, given by `EvenSmoothDescent.radialIterate (fun s => F (s, z)) k r`. -/
noncomputable def radialJet (F : ℝ × P → E) (k : ℕ) (r : ℝ) (z : P) : E :=
  EvenSmoothDescent.radialIterate (fun s => F (s, z)) k r

/-- Axis jet, given by `radialJet F k (Real.sqrt p.1) p.2`. -/
noncomputable def axisJet (F : ℝ × P → E) (k : ℕ) (p : ℝ × P) : E :=
  radialJet F k (Real.sqrt p.1) p.2

omit [CompleteSpace E] in
theorem radialJet_succ (F : ℝ × P → E) (k : ℕ) (r : ℝ) (z : P) :
    radialJet F (k + 1) r z =
      EvenSmoothDescent.radialDerivative (fun s => radialJet F k s z) r := by
  exact congrFun (EvenSmoothDescent.radialIterate_succ (fun s => F (s, z)) k) r

omit [CompleteSpace E] in
theorem radialJet_even {F : ℝ × P → E} {z : P}
    (he : Function.Even (fun r => F (r, z))) (k : ℕ) :
    Function.Even (fun r => radialJet F k r z) :=
  EvenSmoothDescent.even_radialIterate he k

omit [CompleteSpace E] in
theorem axisJet_square {F : ℝ × P → E} {z : P}
    (he : Function.Even (fun r => F (r, z))) (k : ℕ) (r : ℝ) :
    axisJet F k (r ^ 2, z) = radialJet F k r z :=
  EvenSmoothDescent.descent_square (radialJet_even he k) r

omit [CompleteSpace E] in
theorem radialJet_contDiff {F : ℝ × P → E} {z : P}
    (hf : ContDiff ℝ ∞ (fun r => F (r, z))) (k : ℕ) :
    ContDiff ℝ ∞ (fun r => radialJet F k r z) :=
  EvenSmoothDescent.contDiff_radialIterate hf k

theorem axisJet_eq_iteratedDerivWithin {F : ℝ × P → E} {z : P}
    (hf : ContDiff ℝ ∞ (fun r => F (r, z)))
    (he : Function.Even (fun r => F (r, z))) (k : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    axisJet F k (X, z) =
      iteratedDerivWithin k (fun Y => F (Real.sqrt Y, z)) (Ici 0) X :=
  (EvenSmoothDescent.iteratedDerivWithin_descent hf he k hX).symm

theorem axisJet_hasDerivWithinAt {F : ℝ × P → E} {z : P}
    (hf : ContDiff ℝ ∞ (fun r => F (r, z)))
    (he : Function.Even (fun r => F (r, z))) (k : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    HasDerivWithinAt (fun Y => axisJet F k (Y, z)) (axisJet F (k + 1) (X, z)) (Ici 0) X := by
  simp only [axisJet, radialJet_succ]
  exact
    (EvenSmoothDescent.hasDerivWithinAt_descent (radialJet_contDiff hf k)
      (radialJet_even he k) hX)

theorem axisJet_hasDerivAt_pos {F : ℝ × P → E} {z : P}
    (hf : ContDiff ℝ ∞ (fun r => F (r, z)))
    (he : Function.Even (fun r => F (r, z))) (k : ℕ) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (fun Y => axisJet F k (Y, z)) (axisJet F (k + 1) (X, z)) X := by
  simp only [axisJet, radialJet_succ]
  exact
    (EvenSmoothDescent.hasDerivAt_descent_pos (radialJet_contDiff hf k)
      (radialJet_even he k) hX)

theorem axisJet_eq_iteratedDeriv_pos {F : ℝ × P → E} {z : P}
    (hf : ContDiff ℝ ∞ (fun r => F (r, z)))
    (he : Function.Even (fun r => F (r, z))) (k : ℕ) {X : ℝ} (hX : 0 < X) :
    axisJet F k (X, z) = iteratedDeriv k (fun Y => F (Real.sqrt Y, z)) X := by
  induction k generalizing X with
  | zero => rfl
  | succ k ih =>
    have hEq : (fun Y => axisJet F k (Y, z)) =ᶠ[𝓝 X]
        iteratedDeriv k (fun Y => F (Real.sqrt Y, z)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hX] with Y hY
      exact ih hY
    rw [iteratedDeriv_succ, ← hEq.deriv_eq]
    exact (axisJet_hasDerivAt_pos hf he k hX).deriv.symm

theorem axisJet_zero {F : ℝ × P → E} {z : P}
    (hf : ContDiff ℝ ∞ (fun r => F (r, z))) (k : ℕ) :
    axisJet F k (0, z) = ((k.factorial : ℝ) / ((2 * k).factorial : ℝ)) •
      iteratedDeriv (2 * k) (fun r => F (r, z)) 0 := by
  simpa only [axisJet, radialJet, Real.sqrt_zero] using
    EvenSmoothDescent.radialIterate_at_zero k hf

/-! ## Locality of the genuine Hadamard iterates -/

theorem scaled_mem_Ioo {R r t : ℝ} (hr : r ∈ Ioo (-R) R) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * r ∈ Ioo (-R) R := by
  have habs : |r| < R := abs_lt.mpr hr
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (abs_nonneg r) ht.2).trans_lt habs

omit [CompleteSpace E] in
theorem radialDerivative_congr {R : ℝ} {f g : ℝ → E} (hfg : EqOn f g (Ioo (-R) R))
    {r : ℝ} (hr : r ∈ Ioo (-R) R) :
    EvenSmoothDescent.radialDerivative f r = EvenSmoothDescent.radialDerivative g r := by
  unfold EvenSmoothDescent.radialDerivative EvenSmoothDescent.average
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have htr := scaled_mem_Ioo hr ht'
  have heq : f =ᶠ[𝓝 (t * r)] g := by
    filter_upwards [isOpen_Ioo.mem_nhds htr] with x hx
    exact hfg hx
  exact heq.iteratedDeriv_eq 2

omit [CompleteSpace E] in
theorem radialJet_congr {R : ℝ} {F G : ℝ × P → E} {z : P}
    (hfg : ∀ r ∈ Ioo (-R) R, F (r, z) = G (r, z)) (k : ℕ) :
    ∀ r ∈ Ioo (-R) R, radialJet F k r z = radialJet G k r z := by
  induction k with
  | zero => exact hfg
  | succ k ih =>
    intro r hr
    rw [radialJet_succ, radialJet_succ]
    exact radialDerivative_congr (fun s hs => ih s hs) hr

/-- Localized, given by `EvenSmoothDescent.localized R (fun r => F (r, p.2)) p.1`. -/
noncomputable def localized (R : ℝ) (F : ℝ × P → E) (p : ℝ × P) : E :=
  EvenSmoothDescent.localized R (fun r => F (r, p.2)) p.1

theorem evenCutoff_one {R r : ℝ} (hR : 0 < R) (hr : |r| ≤ R / 4) :
    EvenSmoothDescent.evenCutoff R r = 1 := by
  have hb : |(2 / R) * r| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hR)]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hR).mpr
    nlinarith
  have hbn : |(2 / R) * (-r)| ≤ 1 / 2 := by simpa only [mul_neg, abs_neg] using hb
  simp only [EvenSmoothDescent.evenCutoff, SmoothCutoffs.scaledCutoff_one_of_abs_le hb,
    SmoothCutoffs.scaledCutoff_one_of_abs_le hbn, mul_one]

omit [CompleteSpace E] in
theorem localized_eq {R r : ℝ} (hR : 0 < R) (hr : |r| ≤ R / 4) (F : ℝ × P → E) (z : P) :
    localized R F (r, z) = F (r, z) := by
  simp only [localized, EvenSmoothDescent.localized, evenCutoff_one hR hr, one_smul]

omit [CompleteSpace E] in
theorem radialJet_localized_eq {R : ℝ} (hR : 0 < R) (F : ℝ × P → E) (z : P) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-(R / 4)) (R / 4)) :
    radialJet (localized R F) k r z = radialJet F k r z :=
  radialJet_congr (fun _ hs => localized_eq hR (abs_lt.mpr hs).le F z) k r hr

omit [CompleteSpace E] in
theorem localized_descent_eventuallyEq {R : ℝ} (hR : 0 < R) (F : ℝ × P → E) (z : P)
    {X : ℝ} (hX : X ∈ Ico (0 : ℝ) ((R / 4) ^ 2)) :
    (fun Y => localized R F (Real.sqrt Y, z)) =ᶠ[𝓝 X] (fun Y => F (Real.sqrt Y, z)) := by
  have hs : Real.sqrt X ∈ Ioo (-(R / 4)) (R / 4) := by
    constructor
    · nlinarith [Real.sqrt_nonneg X]
    · nlinarith [Real.sq_sqrt hX.1, Real.sqrt_nonneg X, hX.2]
  have heq : (fun r => localized R F (r, z)) =ᶠ[𝓝 (Real.sqrt X)] (fun r => F (r, z)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact localized_eq hR (abs_lt.mpr hr).le F z
  exact heq.comp_tendsto (Real.continuous_sqrt.tendsto X)

theorem axisJet_eq_iteratedDerivWithin_local {R : ℝ} (hR : 0 < R) {F : ℝ × P → E} {z : P}
    (hf : ContDiffOn ℝ ∞ (fun r => F (r, z)) (Ioo (-R) R))
    (he : ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {X : ℝ} (hX : X ∈ Ico (0 : ℝ) ((R / 4) ^ 2)) :
    axisJet F k (X, z) =
      iteratedDerivWithin k (fun Y => F (Real.sqrt Y, z)) (Ici 0) X := by
  have hs : Real.sqrt X ∈ Ioo (-(R / 4)) (R / 4) := by
    constructor
    · nlinarith [Real.sqrt_nonneg X]
    · nlinarith [Real.sq_sqrt hX.1, Real.sqrt_nonneg X, hX.2]
  have hloc := EvenSmoothDescent.contDiff_localized (f := fun r => F (r, z)) hR hf
  have heloc := EvenSmoothDescent.even_localized (f := fun r => F (r, z)) hR he
  have hEq := localized_descent_eventuallyEq hR F z hX
  calc
    _ = axisJet (localized R F) k (X, z) := (radialJet_localized_eq hR F z k hs).symm
    _ = iteratedDerivWithin k (fun Y => localized R F (Real.sqrt Y, z)) (Ici 0) X :=
      axisJet_eq_iteratedDerivWithin hloc heloc k hX.1
    _ = _ := by
      simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
      rw [(hEq.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hEq.eq_of_nhds k]

theorem axisJet_eq_iteratedDeriv_local_pos {R : ℝ} (hR : 0 < R) {F : ℝ × P → E} {z : P}
    (hf : ContDiffOn ℝ ∞ (fun r => F (r, z)) (Ioo (-R) R))
    (he : ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) ((R / 4) ^ 2)) :
    axisJet F k (X, z) = iteratedDeriv k (fun Y => F (Real.sqrt Y, z)) X := by
  have hs : Real.sqrt X ∈ Ioo (-(R / 4)) (R / 4) := by
    constructor
    · nlinarith [Real.sqrt_nonneg X]
    · nlinarith [Real.sq_sqrt hX.1.le, Real.sqrt_nonneg X, hX.2]
  have hloc := EvenSmoothDescent.contDiff_localized (f := fun r => F (r, z)) hR hf
  have heloc := EvenSmoothDescent.even_localized (f := fun r => F (r, z)) hR he
  have hEq := localized_descent_eventuallyEq hR F z ⟨hX.1.le, hX.2⟩
  calc
    _ = axisJet (localized R F) k (X, z) := (radialJet_localized_eq hR F z k hs).symm
    _ = iteratedDeriv k (fun Y => localized R F (Real.sqrt Y, z)) X :=
      axisJet_eq_iteratedDeriv_pos hloc heloc k hX.1
    _ = _ := hEq.iteratedDeriv_eq k

/-! ## Genuine joint smoothness of the signed radial pullbacks -/

section Joint

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

/-- Radial partial, given by `deriv (fun r => F (r, p.2)) p.1`. -/
noncomputable def radialPartial (F : ℝ × P → E) (p : ℝ × P) : E :=
  deriv (fun r => F (r, p.2)) p.1

/-- Reduce family, given by `EvenSmoothDescent.radialDerivative (fun r => F (r, p.2)) p.1`. -/
noncomputable def reduceFamily (F : ℝ × P → E) (p : ℝ × P) : E :=
  EvenSmoothDescent.radialDerivative (fun r => F (r, p.2)) p.1

omit [CompleteSpace E] [ProperSpace P] in
theorem radialPartial_contDiffOn {U : Set P} (hU : IsOpen U) {F : ℝ × P → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (radialPartial F) (univ ×ˢ U) := by
  intro p hp
  have hbase : ContDiffAt ℝ ∞ F p := hF.contDiffAt ((isOpen_univ.prod hU).mem_nhds hp)
  have hG : ContDiffAt ℝ ∞ (fun w : (ℝ × P) × ℝ => F (w.2, w.1.2)) (p, p.1) :=
    hbase.comp (p, p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  have hD : ContDiffAt ℝ ∞
      (fun q : ℝ × P => fderiv ℝ (fun r => F (r, q.2)) q.1) p :=
    hG.fderiv contDiffAt_fst (by simp)
  exact (hD.clm_apply contDiffAt_const).contDiffWithinAt

omit [CompleteSpace E] [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P] in
theorem reduceFamily_integral (F : ℝ × P → E) (p : ℝ × P) :
    reduceFamily F p = (1 / 2 : ℝ) •
      ∫ t in (0 : ℝ)..1, radialPartial (radialPartial F) (t * p.1, p.2) := by
  simp only [reduceFamily, EvenSmoothDescent.radialDerivative, EvenSmoothDescent.average,
    radialPartial, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
    iteratedDeriv_zero]

omit [CompleteSpace E] in
theorem reduceFamily_contDiffOn {U : Set P} (hU : IsOpen U) {F : ℝ × P → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (reduceFamily F) (univ ×ˢ U) := by
  let G : (ℝ × P) × ℝ → E := fun w => radialPartial (radialPartial F) (w.2 * w.1.1, w.1.2)
  have hG : ContDiffOn ℝ ∞ G ((univ ×ˢ U) ×ˢ univ) :=
    (radialPartial_contDiffOn hU (radialPartial_contDiffOn hU hF)).comp
      ((contDiffOn_snd.mul contDiffOn_fst.fst).prodMk contDiffOn_fst.snd)
      (fun w hw => ⟨mem_univ _, hw.1.2⟩)
  have hi := ParametricRephase.intervalIntegral_contDiffOn_of_joint G (univ ×ˢ U)
    (isOpen_univ.prod hU) hG 0 1 zero_le_one
  have hEq : reduceFamily F = fun p => (1 / 2 : ℝ) • ∫ t in (0 : ℝ)..1, G (p, t) :=
    funext (reduceFamily_integral F)
  rw [hEq]
  exact hi.const_smul (1 / 2 : ℝ)

omit [CompleteSpace E] in
theorem radialJet_joint_contDiffOn {U : Set P} (hU : IsOpen U) {F : ℝ × P → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ U)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × P => radialJet F k p.1 p.2) (univ ×ˢ U) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    have h := reduceFamily_contDiffOn hU ih
    simp only [radialJet_succ]
    exact h

omit [CompleteSpace E] [ProperSpace P] in
theorem localized_joint_contDiffOn {R : ℝ} (hR : 0 < R) {U : Set P} (hU : IsOpen U)
    {F : ℝ × P → E} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U)) :
    ContDiffOn ℝ ∞ (localized R F) (univ ×ˢ U) := by
  intro p hp
  by_cases hr : |p.1| < R
  · exact (((EvenSmoothDescent.contDiff_evenCutoff R).comp contDiff_fst).contDiffAt.smul
      (hF.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨abs_lt.mp hr, hp.2⟩))).contDiffWithinAt
  · have hz := (EvenSmoothDescent.localized_eventually_zero hR (le_of_not_gt hr)
        (fun _ => (1 : ℝ))).comp_tendsto (continuous_fst.tendsto p)
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × P => (0 : E)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    change EvenSmoothDescent.evenCutoff R q.1 * 1 = 0 at hq
    simp only [mul_one] at hq
    simp only [localized, EvenSmoothDescent.localized, hq, zero_smul]

omit [CompleteSpace E] in
theorem radialJet_joint_contDiffOn_local {R : ℝ} (hR : 0 < R) {U : Set P} (hU : IsOpen U)
    {F : ℝ × P → E} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × P => radialJet F k p.1 p.2)
      (Ioo (-(R / 4)) (R / 4) ×ˢ U) := by
  have h := (radialJet_joint_contDiffOn hU (localized_joint_contDiffOn hR hU hF) k).mono
    (Set.prod_mono (subset_univ (Ioo (-(R / 4)) (R / 4))) (Subset.refl _))
  exact h.congr fun p hp => (radialJet_localized_eq hR F p.2 k hp.1).symm

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P] in
omit [CompleteSpace E] in
theorem radialJet_even_local {R : ℝ} (hR : 0 < R) {F : ℝ × P → E} {z : P}
    (he : ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-(R / 4)) (R / 4)) :
    radialJet F k (-r) z = radialJet F k r z := by
  have hnr : -r ∈ Ioo (-(R / 4)) (R / 4) := by constructor <;> linarith [hr.1, hr.2]
  rw [← radialJet_localized_eq hR F z k hnr, ← radialJet_localized_eq hR F z k hr]
  exact radialJet_even (EvenSmoothDescent.even_localized (f := fun r => F (r, z)) hR he) k r

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P] in
omit [CompleteSpace E] in
theorem axisJet_square_local {R : ℝ} (hR : 0 < R) {F : ℝ × P → E} {z : P}
    (he : ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-(R / 4)) (R / 4)) :
    axisJet F k (r ^ 2, z) = radialJet F k r z := by
  change radialJet F k (Real.sqrt (r ^ 2)) z = _
  rw [Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 r with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg hs, radialJet_even_local hR he k hr]

omit [CompleteSpace E] in
/-- The input needed by positive-order lower sources: every canonical
squared-radius jet has a genuinely smooth, even signed radial pullback. -/
theorem axisJet_pullback_contDiffOn_local {R : ℝ} (hR : 0 < R) {U : Set P} (hU : IsOpen U)
    {F : ℝ × P → E} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × P => axisJet F k (p.1 ^ 2, p.2))
      (Ioo (-(R / 4)) (R / 4) ×ˢ U) :=
  (radialJet_joint_contDiffOn_local hR hU hF k).congr
    (fun p hp => axisJet_square_local hR (he p.2 hp.2) k hp.1)

end Joint

/-! ## Holomorphy is preserved by the actual radial derivative -/

section Holomorphic

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

/-- The radial difference quotients converge in the supremum norm on every
compact parameter disk.  The holomorphic limit theorem therefore applies to
the genuine radial derivative. -/
theorem radialPartial_holomorphic {U : Set ℂ} (hU : IsOpen U) {F : ℝ × ℂ → B}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ U))
    (hhol : ∀ r : ℝ, DifferentiableOn ℂ (fun z => F (r, z)) U) (r : ℝ) :
    DifferentiableOn ℂ (fun z => radialPartial F (r, z)) U := by
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let σ := ε / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hDisk : closedBall z σ ⊆ U :=
    (closedBall_subset_ball (by dsimp [σ]; linarith : σ < ε)).trans hεsub
  let V : ℝ → C(CauchyRestriction.Disk z σ, B) :=
    CompactSmoothFamily.family (closedBall z σ) F
  have hV : ContDiff ℝ ∞ V := contDiffOn_univ.mp
    (CompactSmoothFamily.contDiffOn_family_of_joint (closedBall z σ) univ U
      isOpen_univ hU hDisk F hF)
  have hval (s : ℝ) (w : CauchyRestriction.Disk z σ) : V s w = F (s, w) :=
    CompactSmoothFamily.family_apply_of_joint (closedBall z σ) hDisk F hF.continuousOn
      (mem_univ s) w
  have hd : HasDerivAt V (deriv V r) r :=
    ((contDiff_infty_iff_deriv.mp hV).1 r).hasDerivAt
  have hderiv (w : CauchyRestriction.Disk z σ) : deriv V r w = radialPartial F (r, w) := by
    have he := (ContinuousMap.evalCLM ℝ w).hasFDerivAt.comp_hasDerivAt r hd
    have heq : (fun s => V s w) = fun s => F (s, w) := funext fun s => hval s w
    change HasDerivAt (fun s => V s w) (deriv V r w) r at he
    rw [heq] at he
    exact he.deriv.symm
  let Q : ℝ → ℂ → B := fun t w => t⁻¹ • (F (r + t, w) - F (r, w))
  have hlim : TendstoUniformlyOn Q (fun w => radialPartial F (r, w)) (𝓝[≠] (0 : ℝ))
      (ball z σ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have ht := Metric.tendsto_nhds.mp hd.tendsto_slope_zero δ hδ
    filter_upwards [ht] with t ht
    intro w hw
    let w' : CauchyRestriction.Disk z σ := ⟨w, ball_subset_closedBall hw⟩
    have hb := (deriv V r - t⁻¹ • (V (r + t) - V r)).norm_coe_le_norm w'
    have hn : ‖radialPartial F (r, w) - Q t w‖ ≤
        ‖deriv V r - t⁻¹ • (V (r + t) - V r)‖ := by
      simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, hderiv,
        hval, Q, w'] using hb
    rw [dist_eq_norm]
    apply hn.trans_lt
    simpa only [dist_eq_norm, norm_sub_rev] using ht
  have hQ : ∀ᶠ t in 𝓝[≠] (0 : ℝ), DifferentiableOn ℂ (Q t) (ball z σ) := by
    apply Filter.Eventually.of_forall
    intro t
    exact (((hhol (r + t)).sub (hhol r)).const_smul t⁻¹).mono
      (ball_subset_closedBall.trans hDisk)
  have hdiff := hlim.tendstoLocallyUniformlyOn.differentiableOn hQ isOpen_ball
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds z hσ)).differentiableWithinAt

/-- Segment: an abbreviation for `↥(Icc (0 : ℝ) 1)`. -/
abbrev Segment := ↥(Icc (0 : ℝ) 1)

/-- Segment extend, given by `f (projIcc 0 1 zero_le_one t)`. -/
noncomputable def segmentExtend (f : C(Segment, B)) (t : ℝ) : B :=
  f (projIcc 0 1 zero_le_one t)

omit [NormedSpace ℂ B] [CompleteSpace B] in
theorem segmentExtend_continuous (f : C(Segment, B)) : Continuous (segmentExtend f) :=
  f.continuous.comp continuous_projIcc

omit [CompleteSpace B] in
theorem segmentIntegral_norm (f : C(Segment, B)) :
    ‖∫ t in (0 : ℝ)..1, segmentExtend f t‖ ≤ 1 * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := segmentExtend f)
    (fun t _ => f.norm_coe_le_norm (projIcc 0 1 zero_le_one t))
  simpa only [sub_zero, abs_one, mul_one, one_mul] using h

/-- Integration of a compact continuous family is complex linear. -/
noncomputable def segmentIntegral : C(Segment, B) →L[ℂ] B :=
  LinearMap.mkContinuous {
    toFun f := ∫ t in (0 : ℝ)..1, segmentExtend f t
    map_add' := by
      intro f g
      exact intervalIntegral.integral_add
        ((segmentExtend_continuous f).intervalIntegrable 0 1)
        ((segmentExtend_continuous g).intervalIntegrable 0 1)
    map_smul' := by
      intro c f
      exact intervalIntegral.integral_smul c (segmentExtend f)
  } 1 segmentIntegral_norm

omit [CompleteSpace B] in
theorem intervalIntegral_holomorphic {U : Set ℂ} (hU : IsOpen U) {G : ℂ × ℝ → B}
    (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ))
    (hhol : ∀ t : ℝ, DifferentiableOn ℂ (fun z => G (z, t)) U) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, G (z, t)) U := by
  have hf := HolomorphicFamily.differentiableOn_family_of_joint (Icc (0 : ℝ) 1)
    U univ hU isOpen_univ (subset_univ _) G hG (fun t _ => hhol t)
  have hi : DifferentiableOn ℂ
      (fun z => segmentIntegral (CompactSmoothFamily.family (Icc (0 : ℝ) 1) G z)) U :=
    (segmentIntegral : C(Segment, B) →L[ℂ] B).differentiable.comp_differentiableOn hf
  apply hi.congr
  intro z hz
  change (∫ t in (0 : ℝ)..1, G (z, t)) =
    ∫ t in (0 : ℝ)..1, segmentExtend (CompactSmoothFamily.family (Icc (0 : ℝ) 1) G z) t
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  rw [segmentExtend, projIcc_of_mem zero_le_one ht']
  exact (CompactSmoothFamily.family_apply_of_joint (Icc (0 : ℝ) 1)
    (subset_univ _) G hG.continuousOn hz ⟨t, ht'⟩).symm

theorem reduceFamily_holomorphic {U : Set ℂ} (hU : IsOpen U) {F : ℝ × ℂ → B}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ U))
    (hhol : ∀ r : ℝ, DifferentiableOn ℂ (fun z => F (r, z)) U) (r : ℝ) :
    DifferentiableOn ℂ (fun z => reduceFamily F (r, z)) U := by
  have hD := radialPartial_contDiffOn hU hF
  have hDhol := radialPartial_holomorphic hU hF hhol
  have hD2 := radialPartial_contDiffOn hU hD
  have hD2hol := radialPartial_holomorphic hU hD hDhol
  let G : ℂ × ℝ → B := fun p => radialPartial (radialPartial F) (p.2 * r, p.1)
  have hG : ContDiffOn ℝ ∞ G (U ×ˢ univ) :=
    hD2.comp ((contDiffOn_snd.mul contDiffOn_const).prodMk contDiffOn_fst)
      (fun p hp => ⟨mem_univ _, hp.1⟩)
  have hi := (intervalIntegral_holomorphic hU hG (fun t => hD2hol (t * r))).const_smul
    (1 / 2 : ℝ)
  have heq : (fun z => reduceFamily F (r, z)) =
      (fun z => (1 / 2 : ℝ) • ∫ t in (0 : ℝ)..1, G (z, t)) :=
    funext fun z => reduceFamily_integral F (r, z)
  rw [heq]
  exact hi

theorem radialJet_holomorphic {U : Set ℂ} (hU : IsOpen U) {F : ℝ × ℂ → B}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ U))
    (hhol : ∀ r : ℝ, DifferentiableOn ℂ (fun z => F (r, z)) U) (k : ℕ) (r : ℝ) :
    DifferentiableOn ℂ (fun z => radialJet F k r z) U := by
  induction k generalizing r with
  | zero => exact hhol r
  | succ k ih =>
    have h := reduceFamily_holomorphic hU (radialJet_joint_contDiffOn hU hF k) ih r
    simp only [radialJet_succ]
    exact h

omit [CompleteSpace B] in
theorem localized_holomorphic {R : ℝ} (hR : 0 < R) {U : Set ℂ} {F : ℝ × ℂ → B}
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U) (r : ℝ) :
    DifferentiableOn ℂ (fun z => localized R F (r, z)) U := by
  by_cases hr : |r| < R
  · exact (hhol r (abs_lt.mp hr)).const_smul (EvenSmoothDescent.evenCutoff R r)
  · have hz := (EvenSmoothDescent.localized_eventually_zero hR (le_of_not_gt hr)
      (fun _ => (1 : ℝ))).eq_of_nhds
    change EvenSmoothDescent.evenCutoff R r * 1 = 0 at hz
    simp only [mul_one] at hz
    have heq : (fun z => localized R F (r, z)) = (fun _ => 0) := by
      funext z
      simp only [localized, EvenSmoothDescent.localized, hz, zero_smul]
    rw [heq]
    exact differentiableOn_const _

theorem radialJet_holomorphic_local {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-(R / 4)) (R / 4)) :
    DifferentiableOn ℂ (fun z => radialJet F k r z) U := by
  have h := radialJet_holomorphic hU (localized_joint_contDiffOn hR hU hF)
    (localized_holomorphic hR hhol) k r
  exact h.congr fun z _ => (radialJet_localized_eq hR F z k hr).symm

/-- Every canonical right jet has holomorphic parameter slices, including
at the axis, under the actual joint-smooth and holomorphic input hypotheses. -/
theorem axisJet_pullback_holomorphic_local {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-(R / 4)) (R / 4)) :
    DifferentiableOn ℂ (fun z => axisJet F k (r ^ 2, z)) U :=
  (radialJet_holomorphic_local hR hU hF hhol k hr).congr
    (fun z hz => axisJet_square_local hR (he z hz) k hr)

/-! ## Actual mixed parameter jets -/

/-- Complex partial, given by `deriv (fun z => F (p.1, z)) p.2`. -/
noncomputable def complexPartial (F : ℝ × ℂ → B) (p : ℝ × ℂ) : B :=
  deriv (fun z => F (p.1, z)) p.2

/-- Complex jet, given by `iteratedDeriv m (fun z => F (p.1, z)) p.2`. -/
noncomputable def complexJet (F : ℝ × ℂ → B) (m : ℕ) (p : ℝ × ℂ) : B :=
  iteratedDeriv m (fun z => F (p.1, z)) p.2

omit [CompleteSpace B] in
theorem complexPartial_eq_real_fderiv {U : Set ℂ} (hU : IsOpen U) {F : ℝ × ℂ → B}
    {r : ℝ} (hhol : DifferentiableOn ℂ (fun z => F (r, z)) U) {z : ℂ} (hz : z ∈ U) :
    complexPartial F (r, z) = fderiv ℝ (fun z => F (r, z)) z 1 := by
  have hd := (hhol.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hr := hd.hasFDerivAt.restrictScalars ℝ
  have heq := congrArg (fun L : ℂ →L[ℝ] B => L 1) hr.fderiv
  change fderiv ℝ (fun z => F (r, z)) z 1 = (1 : ℂ) • deriv (fun z => F (r, z)) z at heq
  simpa only [complexPartial, one_smul] using heq.symm

omit [CompleteSpace B] in
theorem complexPartial_contDiffOn {S : Set ℝ} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (S ×ˢ U))
    (hhol : ∀ r ∈ S, DifferentiableOn ℂ (fun z => F (r, z)) U) :
    ContDiffOn ℝ ∞ (complexPartial F) (S ×ˢ U) := by
  intro p hp
  have hbase := hF.contDiffAt ((hS.prod hU).mem_nhds hp)
  have hG : ContDiffAt ℝ ∞ (fun w : (ℝ × ℂ) × ℂ => F (w.1.1, w.2)) (p, p.2) :=
    hbase.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hD : ContDiffAt ℝ ∞
      (fun q : ℝ × ℂ => fderiv ℝ (fun z => F (q.1, z)) q.2) p :=
    hG.fderiv contDiffAt_snd (by simp)
  apply ContDiffAt.contDiffWithinAt
  apply (hD.clm_apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℂ => (1 : ℂ))
      p)).congr_of_eventuallyEq
  filter_upwards [(hS.prod hU).mem_nhds hp] with q hq
  exact complexPartial_eq_real_fderiv hU (hhol q.1 hq.1) hq.2

theorem complexJet_contDiffOn {S : Set ℝ} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (S ×ˢ U))
    (hhol : ∀ r ∈ S, DifferentiableOn ℂ (fun z => F (r, z)) U) (m : ℕ) :
    ContDiffOn ℝ ∞ (complexJet F m) (S ×ˢ U) := by
  induction m with
  | zero => exact hF
  | succ m ih =>
    have hh : ∀ r ∈ S, DifferentiableOn ℂ (fun z => complexJet F m (r, z)) U :=
      fun r hr => VolterraRegularity.holomorphic_iteratedDeriv hU (hhol r hr) m
    have heq : complexJet F (m + 1) = complexPartial (complexJet F m) := by
      funext p
      simp only [complexJet, complexPartial, iteratedDeriv_succ]
    rw [heq]
    exact complexPartial_contDiffOn hS hU ih hh

/-- Mixed axis jet, given by `iteratedDeriv m (fun z => axisJet F k (p.1, z)) p.2`. -/
noncomputable def mixedAxisJet (F : ℝ × ℂ → B) (k m : ℕ) (p : ℝ × ℂ) : B :=
  iteratedDeriv m (fun z => axisJet F k (p.1, z)) p.2

omit [CompleteSpace B] in
theorem mixedAxisJet_square_local {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z))
    (k m : ℕ) {r : ℝ} (hr : r ∈ Ioo (-(R / 4)) (R / 4)) {z : ℂ} (hz : z ∈ U) :
    mixedAxisJet F k m (r ^ 2, z) =
      complexJet (fun p : ℝ × ℂ => radialJet F k p.1 p.2) m (r, z) := by
  have heq : (fun w => axisJet F k (r ^ 2, w)) =ᶠ[𝓝 z] (fun w => radialJet F k r w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact axisJet_square_local hR (he w hw) k hr
  exact heq.iteratedDeriv_eq m

/-- Every fixed mixed jet has the genuine joint regularity required of a
lower-order source, without any negative-`X` extension. -/
theorem mixedAxisJet_pullback_contDiffOn_local {R : ℝ} (hR : 0 < R) {U : Set ℂ}
    (hU : IsOpen U) {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => mixedAxisJet F k m (p.1 ^ 2, p.2))
      (Ioo (-(R / 4)) (R / 4) ×ˢ U) := by
  have h := complexJet_contDiffOn isOpen_Ioo hU (radialJet_joint_contDiffOn_local hR hU hF k)
    (fun r hr => radialJet_holomorphic_local hR hU hF hhol k hr) m
  exact h.congr fun p hp => mixedAxisJet_square_local hR hU he k m hp.1 hp.2

theorem mixedAxisJet_pullback_holomorphic_local {R : ℝ} (hR : 0 < R) {U : Set ℂ}
    (hU : IsOpen U) {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-(R / 4)) (R / 4)) :
    DifferentiableOn ℂ (fun z => mixedAxisJet F k m (r ^ 2, z)) U :=
  VolterraRegularity.holomorphic_iteratedDeriv hU
    (axisJet_pullback_holomorphic_local hR hU hF hhol he k hr) m

theorem mixedAxisJet_eq_within_local {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ)
    {X : ℝ} (hX : X ∈ Ico (0 : ℝ) ((R / 4) ^ 2)) {z : ℂ} (hz : z ∈ U) :
    mixedAxisJet F k m (X, z) =
      iteratedDeriv m (fun w => iteratedDerivWithin k (fun Y => F (Real.sqrt Y, w)) (Ici 0) X) z :=
          by
  have heq : (fun w => axisJet F k (X, w)) =ᶠ[𝓝 z]
      (fun w => iteratedDerivWithin k (fun Y => F (Real.sqrt Y, w)) (Ici 0) X) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    apply axisJet_eq_iteratedDerivWithin_local hR _ (he w hw) k hX
    exact hF.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => ⟨hr, hw⟩)
  exact heq.iteratedDeriv_eq m

theorem mixedAxisJet_eq_ordinary_local {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ)
    {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) ((R / 4) ^ 2)) {z : ℂ} (hz : z ∈ U) :
    mixedAxisJet F k m (X, z) =
      iteratedDeriv m (fun w => iteratedDeriv k (fun Y => F (Real.sqrt Y, w)) X) z := by
  have heq : (fun w => axisJet F k (X, w)) =ᶠ[𝓝 z]
      (fun w => iteratedDeriv k (fun Y => F (Real.sqrt Y, w)) X) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    apply axisJet_eq_iteratedDeriv_local_pos hR _ (he w hw) k hX
    exact hF.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => ⟨hr, hw⟩)
  exact heq.iteratedDeriv_eq m

/-! ## Interior localization retaining the full radial domain -/

/-- Interior bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
noncomputable def interiorBump {R S : ℝ} (hS : 0 < S) (hSR : S < R) : ContDiffBump (0 : ℝ) where
  rIn := S
  rOut := (S + R) / 2
  rIn_pos := hS
  rIn_lt_rOut := by linarith

/-- Interior cutoff, given by `interiorBump hS hSR r * interiorBump hS hSR (-r)`. -/
noncomputable def interiorCutoff {R S : ℝ} (hS : 0 < S) (hSR : S < R) (r : ℝ) : ℝ :=
  letI : HasContDiffBump ℝ := by infer_instance
  interiorBump hS hSR r * interiorBump hS hSR (-r)

theorem interiorCutoff_contDiff {R S : ℝ} (hS : 0 < S) (hSR : S < R) :
    ContDiff ℝ ∞ (interiorCutoff hS hSR) :=
  (interiorBump hS hSR).contDiff.mul ((interiorBump hS hSR).contDiff.comp contDiff_id.neg)

theorem interiorCutoff_even {R S : ℝ} (hS : 0 < S) (hSR : S < R) :
    Function.Even (interiorCutoff hS hSR) := by
  intro r
  simp only [interiorCutoff, neg_neg, mul_comm]

theorem interiorCutoff_one {R S r : ℝ} (hS : 0 < S) (hSR : S < R) (hr : |r| ≤ S) :
    interiorCutoff hS hSR r = 1 := by
  have hp : r ∈ closedBall (0 : ℝ) (interiorBump hS hSR).rIn := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, interiorBump] using hr
  have hn : -r ∈ closedBall (0 : ℝ) (interiorBump hS hSR).rIn := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_neg, interiorBump] using hr
  simp only [interiorCutoff, (interiorBump hS hSR).one_of_mem_closedBall hp,
    (interiorBump hS hSR).one_of_mem_closedBall hn, mul_one]

theorem interiorCutoff_eventually_zero {R S r : ℝ} (hS : 0 < S) (hSR : S < R) (hr : R ≤ |r|) :
    interiorCutoff hS hSR =ᶠ[𝓝 r] (fun _ => 0) := by
  have hn : r ∉ tsupport (interiorBump hS hSR : ℝ → ℝ) := by
    rw [(interiorBump hS hSR).tsupport_eq]
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, interiorBump]
    linarith
  have hz := notMem_tsupport_iff_eventuallyEq.mp hn
  filter_upwards [hz] with t ht
  change interiorBump hS hSR t = 0 at ht
  simp only [interiorCutoff, ht, zero_mul]

/-- Interior localized, given by `interiorCutoff hS hSR p.1 • F p`. -/
noncomputable def interiorLocalized {R S : ℝ} (hS : 0 < S) (hSR : S < R)
    (F : ℝ × ℂ → B) (p : ℝ × ℂ) : B := interiorCutoff hS hSR p.1 • F p

omit [CompleteSpace B] in
theorem interiorLocalized_eq {R S r : ℝ} (hS : 0 < S) (hSR : S < R) (hr : |r| ≤ S)
    (F : ℝ × ℂ → B) (z : ℂ) : interiorLocalized hS hSR F (r, z) = F (r, z) := by
  simp only [interiorLocalized, interiorCutoff_one hS hSR hr, one_smul]

omit [CompleteSpace B] in
theorem interiorLocalized_contDiffOn {R S : ℝ} (hS : 0 < S) (hSR : S < R)
    {U : Set ℂ} (hU : IsOpen U) {F : ℝ × ℂ → B}
    (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U)) :
    ContDiffOn ℝ ∞ (interiorLocalized hS hSR F) (univ ×ˢ U) := by
  intro p hp
  by_cases hr : |p.1| < R
  · exact (((interiorCutoff_contDiff hS hSR).comp contDiff_fst).contDiffAt.smul
      (hF.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨abs_lt.mp hr, hp.2⟩))).contDiffWithinAt
  · have hz := (interiorCutoff_eventually_zero hS hSR (le_of_not_gt hr)).comp_tendsto
      (continuous_fst.tendsto p)
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℂ => (0 : B)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    change interiorCutoff hS hSR q.1 = 0 at hq
    simp only [interiorLocalized, hq, zero_smul]

omit [CompleteSpace B] in
theorem interiorLocalized_even {R S : ℝ} (hS : 0 < S) (hSR : S < R) {F : ℝ × ℂ → B} {z : ℂ}
    (he : ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) :
    Function.Even (fun r => interiorLocalized hS hSR F (r, z)) := by
  intro r
  by_cases hr : |r| < R
  · simp only [interiorLocalized, interiorCutoff_even hS hSR r, he r (abs_lt.mp hr)]
  · have hz := (interiorCutoff_eventually_zero hS hSR (le_of_not_gt hr)).eq_of_nhds
    simp only [interiorLocalized, interiorCutoff_even hS hSR r, hz, zero_smul]

omit [CompleteSpace B] in
theorem interiorLocalized_holomorphic {R S : ℝ} (hS : 0 < S) (hSR : S < R)
    {U : Set ℂ} {F : ℝ × ℂ → B}
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U) (r : ℝ) :
    DifferentiableOn ℂ (fun z => interiorLocalized hS hSR F (r, z)) U := by
  by_cases hr : |r| < R
  · exact (hhol r (abs_lt.mp hr)).const_smul (interiorCutoff hS hSR r)
  · have hz := (interiorCutoff_eventually_zero hS hSR (le_of_not_gt hr)).eq_of_nhds
    simp only [interiorLocalized, hz, zero_smul]
    exact differentiableOn_const _

omit [CompleteSpace B] in
theorem radialJet_interiorLocalized_eq {R S : ℝ} (hS : 0 < S) (hSR : S < R)
    (F : ℝ × ℂ → B) (z : ℂ) (k : ℕ) {r : ℝ} (hr : r ∈ Ioo (-S) S) :
    radialJet (interiorLocalized hS hSR F) k r z = radialJet F k r z :=
  radialJet_congr (fun _ hs => interiorLocalized_eq hS hSR (abs_lt.mpr hs).le F z) k r hr

omit [CompleteSpace B] in
/-- No radial radius is lost: localization is chosen around each interior
point while the canonical jet itself remains unchanged. -/
theorem radialJet_joint_contDiffOn_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => radialJet F k p.1 p.2) (Ioo (-R) R ×ˢ U) := by
  intro p hp
  let S := (|p.1| + R) / 2
  have hS : 0 < S := by dsimp [S]; positivity
  have hSR : S < R := by dsimp [S]; linarith [abs_lt.mpr hp.1]
  have hpS : p.1 ∈ Ioo (-S) S := abs_lt.mp (by dsimp [S]; linarith [abs_lt.mpr hp.1])
  have hg := radialJet_joint_contDiffOn hU (interiorLocalized_contDiffOn hS hSR hU hF) k
  have hlocal : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ => radialJet F k q.1 q.2) (Ioo (-S) S ×ˢ U) :=
    (hg.mono (Set.prod_mono (subset_univ _) (Subset.refl _))).congr
      (fun q hq => (radialJet_interiorLocalized_eq hS hSR F q.2 k hq.1).symm)
  exact (hlocal.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hpS, hp.2⟩)).contDiffWithinAt

theorem radialJet_holomorphic_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) : DifferentiableOn ℂ (fun z => radialJet F k r z) U := by
  let S := (|r| + R) / 2
  have hS : 0 < S := by dsimp [S]; positivity
  have hSR : S < R := by dsimp [S]; linarith [abs_lt.mpr hr]
  have hrS : r ∈ Ioo (-S) S := abs_lt.mp (by dsimp [S]; linarith [abs_lt.mpr hr])
  have hg := radialJet_holomorphic hU (interiorLocalized_contDiffOn hS hSR hU hF)
    (interiorLocalized_holomorphic hS hSR hhol) k r
  exact hg.congr (fun z _ => (radialJet_interiorLocalized_eq hS hSR F z k hrS).symm)

omit [CompleteSpace B] in
theorem radialJet_even_full {R : ℝ} (hR : 0 < R) {F : ℝ × ℂ → B} {z : ℂ}
    (he : ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) : radialJet F k (-r) z = radialJet F k r z := by
  let S := (|r| + R) / 2
  have hS : 0 < S := by dsimp [S]; positivity
  have hSR : S < R := by dsimp [S]; linarith [abs_lt.mpr hr]
  have hrS : r ∈ Ioo (-S) S := abs_lt.mp (by dsimp [S]; linarith [abs_lt.mpr hr])
  have hnS : -r ∈ Ioo (-S) S := by constructor <;> linarith [hrS.1, hrS.2]
  rw [← radialJet_interiorLocalized_eq hS hSR F z k hnS,
    ← radialJet_interiorLocalized_eq hS hSR F z k hrS]
  exact radialJet_even (interiorLocalized_even hS hSR he) k r

omit [CompleteSpace B] in
theorem axisJet_square_full {R : ℝ} (hR : 0 < R) {F : ℝ × ℂ → B} {z : ℂ}
    (he : ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) : axisJet F k (r ^ 2, z) = radialJet F k r z := by
  change radialJet F k (Real.sqrt (r ^ 2)) z = _
  rw [Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 r with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg hs, radialJet_even_full hR he k hr]

omit [CompleteSpace B] in
theorem axisJet_pullback_contDiffOn_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => axisJet F k (p.1 ^ 2, p.2)) (Ioo (-R) R ×ˢ U) :=
  (radialJet_joint_contDiffOn_full hR hU hF k).congr
    (fun p hp => axisJet_square_full hR (he p.2 hp.2) k hp.1)

theorem axisJet_pullback_holomorphic_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) :
    DifferentiableOn ℂ (fun z => axisJet F k (r ^ 2, z)) U :=
  (radialJet_holomorphic_full hR hU hF hhol k hr).congr
    (fun z hz => axisJet_square_full hR (he z hz) k hr)

theorem axisJet_derivatives_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {X : ℝ} (hX : X ∈ Ico (0 : ℝ) (R ^ 2)) {z : ℂ} (hz : z ∈ U) :
    (axisJet F k (X, z) = iteratedDerivWithin k (fun Y => F (Real.sqrt Y, z)) (Ici 0) X) ∧
      (0 < X → axisJet F k (X, z) = iteratedDeriv k (fun Y => F (Real.sqrt Y, z)) X) := by
  have hsqrt : Real.sqrt X < R := by nlinarith [Real.sq_sqrt hX.1, Real.sqrt_nonneg X, hX.2]
  let S := (Real.sqrt X + R) / 2
  have hS : 0 < S := by dsimp [S]; positivity
  have hSR : S < R := by dsimp [S]; linarith
  have hroot : Real.sqrt X ∈ Ioo (-S) S := by
    dsimp [S]
    constructor <;> linarith [Real.sqrt_nonneg X]
  let G := interiorLocalized hS hSR F
  have hGjoint : ContDiffOn ℝ ∞ G (univ ×ˢ U) := interiorLocalized_contDiffOn hS hSR hU hF
  have hG : ContDiff ℝ ∞ (fun r => G (r, z)) := contDiffOn_univ.mp
    (hGjoint.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r _ => ⟨mem_univ r, hz⟩))
  have heG : Function.Even (fun r => G (r, z)) := interiorLocalized_even hS hSR (he z hz)
  have hEq : (fun Y => G (Real.sqrt Y, z)) =ᶠ[𝓝 X] (fun Y => F (Real.sqrt Y, z)) := by
    have hgerm : (fun r => G (r, z)) =ᶠ[𝓝 (Real.sqrt X)] (fun r => F (r, z)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hroot] with r hr
      exact interiorLocalized_eq hS hSR (abs_lt.mpr hr).le F z
    exact hgerm.comp_tendsto (Real.continuous_sqrt.tendsto X)
  have haxis : axisJet F k (X, z) = axisJet G k (X, z) :=
    (radialJet_interiorLocalized_eq hS hSR F z k hroot).symm
  constructor
  · rw [haxis, axisJet_eq_iteratedDerivWithin hG heG k hX.1]
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
    rw [(hEq.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hEq.eq_of_nhds k]
  · intro hpos
    rw [haxis, axisJet_eq_iteratedDeriv_pos hG heG k hpos]
    exact hEq.iteratedDeriv_eq k

theorem axisJet_eq_within_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {X : ℝ} (hX : X ∈ Ico (0 : ℝ) (R ^ 2)) {z : ℂ} (hz : z ∈ U) :
    axisJet F k (X, z) = iteratedDerivWithin k (fun Y => F (Real.sqrt Y, z)) (Ici 0) X :=
  (axisJet_derivatives_full hR hU hF he k hX hz).1

theorem axisJet_eq_ordinary_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) {z : ℂ} (hz : z ∈ U) :
    axisJet F k (X, z) = iteratedDeriv k (fun Y => F (Real.sqrt Y, z)) X :=
  (axisJet_derivatives_full hR hU hF he k ⟨hX.1.le, hX.2⟩ hz).2 hX.1

theorem axisJet_zero_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    axisJet F k (0, z) = ((k.factorial : ℝ) / ((2 * k).factorial : ℝ)) •
      iteratedDeriv (2 * k) (fun r => F (r, z)) 0 := by
  rw [axisJet_eq_within_full hR hU hF he k (by constructor <;> positivity) hz]
  apply EvenSmoothDescent.iteratedDerivWithin_descent_zero_local (f := fun r => F (r, z)) hR
  · exact hF.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => ⟨hr, hz⟩)
  · exact he z hz

omit [CompleteSpace B] in
theorem mixedAxisJet_square_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z))
    (k m : ℕ) {r : ℝ} (hr : r ∈ Ioo (-R) R) {z : ℂ} (hz : z ∈ U) :
    mixedAxisJet F k m (r ^ 2, z) =
      complexJet (fun p : ℝ × ℂ => radialJet F k p.1 p.2) m (r, z) := by
  have heq : (fun w => axisJet F k (r ^ 2, w)) =ᶠ[𝓝 z] (fun w => radialJet F k r w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact axisJet_square_full hR (he w hw) k hr
  exact heq.iteratedDeriv_eq m

theorem mixedAxisJet_pullback_contDiffOn_full {R : ℝ} (hR : 0 < R) {U : Set ℂ}
    (hU : IsOpen U) {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => mixedAxisJet F k m (p.1 ^ 2, p.2)) (Ioo (-R) R ×ˢ U) := by
  have h := complexJet_contDiffOn isOpen_Ioo hU (radialJet_joint_contDiffOn_full hR hU hF k)
    (fun r hr => radialJet_holomorphic_full hR hU hF hhol k hr) m
  exact h.congr fun p hp => mixedAxisJet_square_full hR hU he k m hp.1 hp.2

theorem mixedAxisJet_pullback_holomorphic_full {R : ℝ} (hR : 0 < R) {U : Set ℂ}
    (hU : IsOpen U) {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hhol : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) :
    DifferentiableOn ℂ (fun z => mixedAxisJet F k m (r ^ 2, z)) U :=
  VolterraRegularity.holomorphic_iteratedDeriv hU
    (axisJet_pullback_holomorphic_full hR hU hF hhol he k hr) m

theorem mixedAxisJet_eq_within_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ)
    {X : ℝ} (hX : X ∈ Ico (0 : ℝ) (R ^ 2)) {z : ℂ} (hz : z ∈ U) :
    mixedAxisJet F k m (X, z) =
      iteratedDeriv m (fun w => iteratedDerivWithin k (fun Y => F (Real.sqrt Y, w)) (Ici 0) X) z :=
          by
  have heq : (fun w => axisJet F k (X, w)) =ᶠ[𝓝 z]
      (fun w => iteratedDerivWithin k (fun Y => F (Real.sqrt Y, w)) (Ici 0) X) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact axisJet_eq_within_full hR hU hF he k hX hw
  exact heq.iteratedDeriv_eq m

theorem mixedAxisJet_eq_ordinary_full {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {F : ℝ × ℂ → B} (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) (k m : ℕ)
    {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) {z : ℂ} (hz : z ∈ U) :
    mixedAxisJet F k m (X, z) =
      iteratedDeriv m (fun w => iteratedDeriv k (fun Y => F (Real.sqrt Y, w)) X) z := by
  have heq : (fun w => axisJet F k (X, w)) =ᶠ[𝓝 z]
      (fun w => iteratedDeriv k (fun Y => F (Real.sqrt Y, w)) X) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact axisJet_eq_ordinary_full hR hU hF he k hX hw
  exact heq.iteratedDeriv_eq m

end Holomorphic

end NavierStokes.BoundaryAxisJets
