/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BoundaryAxisJets
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpacetimeGluing
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricEvenDescent
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Joint smooth extension of even radial profiles

The input is a genuinely smooth even function of the signed radius on an
open parameter strip. A fixed parameter window is chosen independently of
the profile.  Its squared-radius descent is smooth on the closed half-plane.
The proved joint Taylor--Borel extension is applied after reflecting this
half-plane and adding unused spatial coordinates.  Restriction gives a
global smooth function of `(X, eta)` with exactly the original physical
values.  No constant continuation at negative `X` is differentiated.
-/

@[expose] public section


noncomputable section

open Set Filter Function Metric
open scoped Topology ContDiff

namespace NavierStokes.ParametricRadialExtension

/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- The same window can be used for every order and every field component. -/
structure ParameterWindow (S : Set ℝ) where
  /-- Inner of `ParameterWindow`, of type `ℝ`. -/
  inner : ℝ
  /-- Outer of `ParameterWindow`, of type `ℝ`. -/
  outer : ℝ
  one_lt_inner : 1 < inner
  inner_lt_outer : inner < outer
  outer_subset : Ioo (-outer) outer ⊆ S

theorem exists_parameterWindow {S : Set ℝ} (hS : IsOpen S)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) : Nonempty (ParameterWindow S) := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hS hI
  refine ⟨⟨1 + δ / 4, 1 + δ / 2, by linarith, by linarith, ?_⟩⟩
  intro y hy
  apply hsub
  apply Metric.mem_thickening_iff.mpr
  by_cases hl : y < -1
  · refine ⟨-1, by norm_num, ?_⟩
    rw [Real.dist_eq, abs_of_neg (by linarith : y - -1 < 0)]
    linarith [hy.1]
  · by_cases hr : 1 < y
    · refine ⟨1, by norm_num, ?_⟩
      rw [Real.dist_eq, abs_of_pos (by linarith : 0 < y - 1)]
      linarith [hy.2]
    · exact ⟨y, ⟨le_of_not_gt hl, le_of_not_gt hr⟩, by simpa using hδ⟩

/-- Parameter window, given by `Classical.choice (exists_parameterWindow hS hI)`. -/
noncomputable def parameterWindow {S : Set ℝ} (hS : IsOpen S)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) : ParameterWindow S :=
  Classical.choice (exists_parameterWindow hS hI)

namespace ParameterWindow

variable {S : Set ℝ} (w : ParameterWindow S)

theorem inner_pos : 0 < w.inner := zero_lt_one.trans w.one_lt_inner
theorem outer_pos : 0 < w.outer := w.inner_pos.trans w.inner_lt_outer

/-- Bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
noncomputable def bump : ContDiffBump (0 : ℝ) where
  rIn := w.inner
  rOut := w.outer
  rIn_pos := w.inner_pos
  rIn_lt_rOut := w.inner_lt_outer

/-- Parameter map, given by `w.bump eta * eta`. -/
noncomputable def parameterMap (eta : ℝ) : ℝ := w.bump eta * eta

theorem parameterMap_contDiff : ContDiff ℝ ∞ w.parameterMap :=
  w.bump.contDiff.mul contDiff_id

theorem bump_one {eta : ℝ} (heta : |eta| ≤ w.inner) : w.bump eta = 1 := by
  apply w.bump.one_of_mem_closedBall
  simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, bump] using heta

theorem bump_zero {eta : ℝ} (heta : w.outer ≤ |eta|) : w.bump eta = 0 := by
  apply w.bump.zero_of_le_dist
  simpa only [dist_zero_right, Real.norm_eq_abs, bump] using heta

theorem parameterMap_eq {eta : ℝ} (heta : |eta| ≤ w.inner) :
    w.parameterMap eta = eta := by
  simp only [parameterMap, w.bump_one heta, one_mul]

theorem parameterMap_mem (eta : ℝ) : w.parameterMap eta ∈ S := by
  apply w.outer_subset
  apply abs_lt.mp
  by_cases heta : |eta| < w.outer
  · calc
      |w.parameterMap eta| = w.bump eta * |eta| := by
        rw [parameterMap, abs_mul, abs_of_nonneg w.bump.nonneg]
      _ ≤ |eta| := mul_le_of_le_one_left (abs_nonneg eta) w.bump.le_one
      _ < w.outer := heta
  · simp only [parameterMap, w.bump_zero (le_of_not_gt heta), zero_mul, abs_zero]
    exact w.outer_pos

theorem target_subset : Ioo (-w.inner) w.inner ⊆ S := by
  intro eta heta
  apply w.outer_subset
  constructor <;> linarith [heta.1, heta.2, w.inner_lt_outer]

theorem unit_subset : Icc (-1 : ℝ) 1 ⊆ Ioo (-w.inner) w.inner := by
  intro eta heta
  constructor <;> linarith [heta.1, heta.2, w.one_lt_inner]

end ParameterWindow

/-- A smooth global parameter substitution, equal to the original one on
the target window.  Its values remain inside the input parameter domain. -/
noncomputable def regularize {S : Set ℝ} (w : ParameterWindow S)
    (F : Plane → E) (p : Plane) : E := F (p.1, w.parameterMap p.2)

omit [CompleteSpace E] in
theorem regularize_contDiff {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S)) : ContDiff ℝ ∞ (regularize w F) :=
  hF.comp_contDiff (contDiff_fst.prodMk (w.parameterMap_contDiff.comp contDiff_snd))
    (fun p => ⟨mem_univ _, w.parameterMap_mem p.2⟩)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem regularize_even {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta)) (eta r : ℝ) :
    regularize w F (-r, eta) = regularize w F (r, eta) :=
  he _ (w.parameterMap_mem eta) r

/-- Descent, given by `F (Real.sqrt (2 * p.1), p.2)`. -/
noncomputable def descent (F : Plane → E) (p : Plane) : E :=
  F (Real.sqrt (2 * p.1), p.2)

/-- The factor `2` is the physical convention `X = R^2 / 2`. -/
theorem descent_contDiffOn {F : Plane → E} (hF : ContDiff ℝ ∞ F)
    (he : ∀ eta r, F (-r, eta) = F (r, eta)) :
    ContDiffOn ℝ ∞ (descent F) (Ici 0 ×ˢ (univ : Set ℝ)) := by
  have hs : ContDiff ℝ ∞ (fun p : Plane => F (p.2, p.1)) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hd := ParametricEvenDescent.contDiffOn_descend hs he
  have hm : ContDiff ℝ ∞ (fun p : Plane => (p.2, 2 * p.1)) :=
    contDiff_snd.prodMk (contDiff_const.mul contDiff_fst)
  exact hd.comp hm.contDiffOn
    (fun p hp => ⟨mem_univ _, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp.1⟩)

/-- Embed the two-variable half-plane into the already proved joint
half-space extension theorem.  The extra spatial coordinates are unused. -/
noncomputable def halfPlaneLift (g : Plane → E) (z : ProblemStatement.SpaceTime) : E :=
  g (-z.1, z.2 0)

omit [CompleteSpace E] in
theorem halfPlaneLift_contDiffOn {g : Plane → E}
    (hg : ContDiffOn ℝ ∞ g (Ici 0 ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (halfPlaneLift g) (SpacetimeGluing.past 0) := by
  have hm : ContDiff ℝ ∞ (fun z : ProblemStatement.SpaceTime => (-z.1, z.2 0)) :=
    contDiff_fst.neg.prodMk
      ((EuclideanSpace.proj (0 : Fin 3) : ProblemStatement.Space →L[ℝ] ℝ).contDiff.comp
        contDiff_snd)
  apply hg.comp hm.contDiffOn
  intro z hz
  constructor
  · change 0 ≤ -z.1
    have ht : z.1 ≤ 0 := hz.1
    linarith
  · exact mem_univ _

/-- Half plane extension, constructed using `SpacetimeGluing.smoothExtension`. -/
noncomputable def halfPlaneExtension (g : Plane → E)
    (hg : ContDiffOn ℝ ∞ g (Ici 0 ×ˢ (univ : Set ℝ))) (p : Plane) : E :=
  SpacetimeGluing.smoothExtension 0 (halfPlaneLift g) (halfPlaneLift_contDiffOn hg)
    (-p.1, p.2 • ProblemStatement.coordinateVector 0)

theorem halfPlaneExtension_contDiff {g : Plane → E}
    (hg : ContDiffOn ℝ ∞ g (Ici 0 ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (halfPlaneExtension g hg) :=
  (SpacetimeGluing.smoothExtension_contDiff (halfPlaneLift_contDiffOn hg)).comp
    (contDiff_fst.neg.prodMk (contDiff_snd.smul contDiff_const))

omit [CompleteSpace E] in
theorem halfPlaneExtension_eq {g : Plane → E}
    (hg : ContDiffOn ℝ ∞ g (Ici 0 ×ˢ (univ : Set ℝ))) {p : Plane} (hp : 0 ≤ p.1) :
    halfPlaneExtension g hg p = g p := by
  have hmem : (-p.1, p.2 • ProblemStatement.coordinateVector 0) ∈
      SpacetimeGluing.past 0 := ⟨neg_nonpos.mpr hp, mem_univ _⟩
  unfold halfPlaneExtension
  rw [SpacetimeGluing.smoothExtension_eqOn_past (halfPlaneLift_contDiffOn hg) hmem]
  simp [halfPlaneLift, ProblemStatement.coordinateVector]

omit [CompleteSpace E] in
theorem halfPlaneExtension_zero {g : Plane → E}
    (hg : ContDiffOn ℝ ∞ g (Ici 0 ×ˢ (univ : Set ℝ))) {p : Plane} (hp : p.1 ≤ -1) :
    halfPlaneExtension g hg p = 0 := by
  apply SpacetimeGluing.smoothExtension_zero_from
  linarith

/-- The global smooth extension.  The outer parameter cutoff and the
negative radial support bound are independent of the input profile. -/
noncomputable def extension {S : Set ℝ} (w : ParameterWindow S) (F : Plane → E)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta)) (p : Plane) : E :=
  w.bump p.2 • halfPlaneExtension (descent (regularize w F))
    (descent_contDiffOn (regularize_contDiff w hF) (regularize_even w he)) p

theorem extension_contDiff {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta)) :
    ContDiff ℝ ∞ (extension w F hF he) :=
  (w.bump.contDiff.comp contDiff_snd).smul (halfPlaneExtension_contDiff _)

theorem extension_eq {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    {p : Plane} (hX : 0 ≤ p.1) (heta : |p.2| ≤ w.inner) :
    extension w F hF he p = F (Real.sqrt (2 * p.1), p.2) := by
  rw [extension, halfPlaneExtension_eq _ hX, w.bump_one heta, one_smul]
  simp only [descent, regularize, w.parameterMap_eq heta]

theorem extension_zero_negative {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    {p : Plane} (hX : p.1 ≤ -1) : extension w F hF he p = 0 := by
  rw [extension, halfPlaneExtension_zero _ hX, smul_zero]

theorem extension_zero_parameter {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    {p : Plane} (heta : w.outer ≤ |p.2|) : extension w F hF he p = 0 := by
  rw [extension, w.bump_zero heta, zero_smul]

theorem extension_eqOn {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta)) :
    EqOn (extension w F hF he) (descent F) (Ici 0 ×ˢ Ioo (-w.inner) w.inner) := by
  intro p hp
  exact extension_eq w hF he hp.1 (abs_lt.mpr hp.2).le

/-- Every full mixed derivative of the extension, including at the axis,
is the genuine derivative within the physical closed half-plane. -/
theorem extension_mixed_jets {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    (n : ℕ) {p : Plane} (hp : p ∈ Ici 0 ×ˢ Ioo (-w.inner) w.inner) :
    iteratedFDeriv ℝ n (extension w F hF he) p =
      iteratedFDerivWithin ℝ n (descent F) (Ici 0 ×ˢ Ioo (-w.inner) w.inner) p := by
  have hu : UniqueDiffOn ℝ (Ici 0 ×ˢ Ioo (-w.inner) w.inner : Set Plane) :=
    (uniqueDiffOn_Ici 0).prod isOpen_Ioo.uniqueDiffOn
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hu
    ((extension_contDiff w hF he).of_le (nat_le_infty n)).contDiffAt hp]
  exact iteratedFDerivWithin_congr (extension_eqOn w hF he) hp n

/-- Exact recovery on the signed radius.  This also covers the axis. -/
theorem extension_pullback {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    (r : ℝ) {eta : ℝ} (heta : |eta| ≤ w.inner) :
    extension w F hF he (r ^ 2 / 2, eta) = F (r, eta) := by
  rw [extension_eq w hF he (by positivity) heta,
    show 2 * (r ^ 2 / 2) = r ^ 2 by ring, Real.sqrt_sq_eq_abs]
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
  · rw [abs_of_neg (lt_of_not_ge hr)]
    exact he eta (w.outer_subset (abs_lt.mp (heta.trans_lt w.inner_lt_outer))) r

/-- Exact right jets of the literal descended radial profile. -/
theorem extension_radial_jets {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    (n : ℕ) {X eta : ℝ} (hX : 0 ≤ X) (heta : |eta| ≤ w.inner) :
    iteratedDeriv n (fun Y => extension w F hF he (Y, eta)) X =
      iteratedDerivWithin n (fun Y => F (Real.sqrt (2 * Y), eta)) (Ici 0) X := by
  have hg : ContDiff ℝ ∞ (fun Y => extension w F hF he (Y, eta)) :=
    (extension_contDiff w hF he).comp (contDiff_id.prodMk contDiff_const)
  have hwithin : iteratedDerivWithin n (fun Y => extension w F hF he (Y, eta)) (Ici 0) X =
      iteratedDeriv n (fun Y => extension w F hF he (Y, eta)) X := by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv,
      iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici 0)
        (hg.of_le (nat_le_infty n)).contDiffAt hX]
  rw [← hwithin]
  exact iteratedDerivWithin_congr (fun Y hY => extension_eq w hF he hY heta) hX

/-- Identification with the actual Hadamard derivative chain from
`BoundaryAxisJets`; the factor `2^n` comes from `X = R^2/2`. -/
theorem extension_radialJet {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    (n : ℕ) {X eta : ℝ} (hX : 0 ≤ X) (heta : |eta| ≤ w.inner) :
    iteratedDeriv n (fun Y => extension w F hF he (Y, eta)) X =
      (2 : ℝ) ^ n • BoundaryAxisJets.axisJet F n (2 * X, eta) := by
  have hetaS : eta ∈ S :=
    w.outer_subset (abs_lt.mp (heta.trans_lt w.inner_lt_outer))
  have hs : ContDiff ℝ ∞ (fun r => F (r, eta)) :=
    hF.comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, hetaS⟩)
  have heven : Function.Even (fun r => F (r, eta)) := he eta hetaS
  have hd := EvenSmoothDescent.contDiffOn_descent hs heven
  rw [extension_radial_jets w hF he n hX heta]
  calc
    _ = (2 : ℝ) ^ n • iteratedDerivWithin n
        (fun Y => F (Real.sqrt Y, eta)) (Ici 0) (2 * X) :=
      iteratedDerivWithin_comp_const_smul hX (uniqueDiffOn_Ici 0)
        (hd.of_le (nat_le_infty n)) 2
        (fun Y hY => mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hY)
    _ = _ := congrArg ((2 : ℝ) ^ n • ·)
      (BoundaryAxisJets.axisJet_eq_iteratedDerivWithin hs heven n
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hX)).symm

/-- The axis constants and every higher radial jet are preserved exactly. -/
theorem extension_axis_jets {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    (n : ℕ) {eta : ℝ} (heta : |eta| ≤ w.inner) :
    iteratedDeriv n (fun Y => extension w F hF he (Y, eta)) 0 =
      ((2 : ℝ) ^ n * ((n.factorial : ℝ) / ((2 * n).factorial : ℝ))) •
        iteratedDeriv (2 * n) (fun r => F (r, eta)) 0 := by
  have hetaS : eta ∈ S :=
    w.outer_subset (abs_lt.mp (heta.trans_lt w.inner_lt_outer))
  have hs : ContDiff ℝ ∞ (fun r => F (r, eta)) :=
    hF.comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, hetaS⟩)
  rw [extension_radialJet w hF he n le_rfl heta, mul_zero,
    BoundaryAxisJets.axisJet_zero hs, smul_smul]

/-- Exterior support is inherited globally in the parameter, not only on
the interval where exact agreement with the input is required. -/
theorem extension_zero_exterior {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ eta ∈ S, ∀ r, B ≤ r → F (r, eta) = 0)
    {p : Plane} (hX : B ^ 2 / 2 ≤ p.1) : extension w F hF he p = 0 := by
  have hX0 : 0 ≤ p.1 := by nlinarith [sq_nonneg B]
  have hsqrt : B ≤ Real.sqrt (2 * p.1) := by
    apply (Real.le_sqrt hB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hX0)).mpr
    linarith
  rw [extension, halfPlaneExtension_eq _ hX0]
  change w.bump p.2 • F (Real.sqrt (2 * p.1), w.parameterMap p.2) = 0
  rw [hzero _ (w.parameterMap_mem p.2) _ hsqrt, smul_zero]

/-- A uniform support rectangle for all profiles with the same exterior
radius.  The negative extension occupies at most the fixed interval [-1,0]. -/
theorem extension_tsupport {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ eta ∈ S, ∀ r, B ≤ r → F (r, eta) = 0) :
    tsupport (extension w F hF he) ⊆
      Icc (-1 : ℝ) (B ^ 2 / 2) ×ˢ Icc (-w.outer) w.outer := by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  have hlo : -1 < p.1 := lt_of_not_ge fun h => hp (extension_zero_negative w hF he h)
  have hhi : p.1 < B ^ 2 / 2 :=
    lt_of_not_ge fun h => hp (extension_zero_exterior w hF he hB hzero h)
  have heta : |p.2| < w.outer :=
    lt_of_not_ge fun h => hp (extension_zero_parameter w hF he h)
  exact ⟨⟨hlo.le, hhi.le⟩, abs_le.mp heta.le⟩

theorem extension_hasCompactSupport {S : Set ℝ} (w : ParameterWindow S) {F : Plane → E}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S))
    (he : ∀ eta ∈ S, ∀ r, F (-r, eta) = F (r, eta))
    {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ eta ∈ S, ∀ r, B ≤ r → F (r, eta) = 0) :
    HasCompactSupport (extension w F hF he) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure
    (extension_tsupport w hF he hB hzero)

end NavierStokes.ParametricRadialExtension
