/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Sigma
import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.EllipticSet
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Ball averages of carrier fields and Lebesgue differentiation

This file is the analytic core of the honest slice-measurability route (Packet
P4b of the carrier redesign).  For a carrier field `a : RegCoeffField d` and a
measurable set `B` it introduces the matrix of scalar entry averages

`avgMat B a = fun i j => (volume B)⁻¹ • ∫_B a(·)_{ij}`,

records the **entry-test bridge**

`avgMat B a i j = (volume B)⁻¹ • entryTestR i j (indicator B 1) a`

(so that on rational balls `B ⊆ U` the average is an honest function of the
local entry-test generators — used for `LocalSigmaR U`-measurability in
`SliceMeasurability.lean`), and proves the two-directional characterization of
spatial a.e. ellipticity in terms of rational-ball averages:

* forward (Jensen): the average of an a.e.-elliptic field over a ball stays in
  the closed convex elliptic locus (`isEllipticMatrix_avgMat_of_aeRestrict`,
  built on `Convex.set_average_mem`);
* backward (Lebesgue differentiation): if all rational-ball averages of `a`
  inside an open set `U` are elliptic, then `a` is a.e.-elliptic on `U`
  (`aeRestrict_isEllipticMatrix_of_forall_ratBall`), built on the
  centre-free Lebesgue differentiation theorem
  `IsUnifLocDoublingMeasure.ae_tendsto_average` (whose Vitali family provides
  the differentiation basis of closed metric balls on `Vec d = Fin d → ℝ`,
  whose Lebesgue `volume` is a doubling additive Haar measure).

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory Metric Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## The matrix of entry averages -/

/-- The matrix of scalar entry averages of a carrier field over a set `B`.  Its
`(i, j)` entry is the average of `a(·)_{ij}` over `B` for the Lebesgue measure. -/
def avgMat (B : Set (Vec d)) (a : RegCoeffField d) : Mat d :=
  fun i j => (volume B).toReal⁻¹ • ∫ x in B, a x i j ∂volume

/-- The entry average is the corresponding scalar set-average. -/
theorem avgMat_entry_eq_setAverage (B : Set (Vec d)) (a : RegCoeffField d) (i j : Fin d) :
    avgMat B a i j = ⨍ x in B, a x i j ∂volume := by
  rw [avgMat, setAverage_eq, MeasureTheory.Measure.real]

/-! ## The entry-test bridge -/

/-- The constant-one indicator of a compact measurable set is an enriched
probe. -/
theorem isProbeR_indicator {B : Set (Vec d)} (hBcpt : IsCompact B) (hBmeas : MeasurableSet B) :
    IsProbeR (Set.indicator B (fun _ => (1 : ℝ))) := by
  refine ⟨(measurable_const).indicator hBmeas, ⟨1, fun x => ?_⟩, ?_⟩
  · by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
  · apply HasCompactSupport.intro hBcpt
    intro x hx; simp [Set.indicator_of_notMem hx]

/-- The support of the constant-one indicator of `B` is contained in `B`. -/
theorem support_indicator_one_subset (B : Set (Vec d)) :
    Function.support (Set.indicator B (fun _ => (1 : ℝ))) ⊆ B := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxB
  exact hx (by simp [Set.indicator_of_notMem hxB])

/-- **The entry-test bridge (integral form).**  The entry test of a carrier
field against the constant-one indicator of a measurable set is the set integral
of that entry. -/
theorem entryTestR_indicator_one (i j : Fin d) (B : Set (Vec d)) (hBmeas : MeasurableSet B)
    (a : RegCoeffField d) :
    entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) a = ∫ x in B, a x i j ∂volume := by
  unfold entryTestR
  rw [← integral_indicator hBmeas]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  by_cases hx : x ∈ B <;> simp [Set.indicator, hx]

/-- **The entry-test bridge.**  Each entry of the ball average is a scalar
multiple of the localized entry-test generator against the ball indicator. -/
theorem avgMat_entry_eq_smul_entryTestR (i j : Fin d) (B : Set (Vec d))
    (hBmeas : MeasurableSet B) (a : RegCoeffField d) :
    avgMat B a i j
      = (volume B).toReal⁻¹ • entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) a := by
  rw [avgMat, entryTestR_indicator_one i j B hBmeas]

/-! ## Integrability and the pi realization -/

/-- The pi realization `x ↦ (a(x)_{ij})_{ij}` of a carrier field, valued in the
genuine finite pi space `Fin d → Fin d → ℝ` (which — unlike `Mat d` — carries the
`NormedSpace`/`CompleteSpace` structure needed by the Bochner–Jensen average). -/
def matPi (a : RegCoeffField d) (x : Vec d) : Fin d → Fin d → ℝ := fun i j => a x i j

/-- The elliptic locus, realized natively on the pi space (defeq to the
`Mat d` locus of `EllipticSet.lean`, but stated so the Bochner average unifies
without triggering the blocked `Matrix` norm instances). -/
def elliptPi (lam Lam : ℝ) : Set (Fin d → Fin d → ℝ) :=
  {M | IsEllipticMatrix lam Lam M}

theorem convex_elliptPi (lam Lam : ℝ) : Convex ℝ (elliptPi (d := d) lam Lam) :=
  convex_isEllipticMatrix

theorem isClosed_elliptPi (lam Lam : ℝ) : IsClosed (elliptPi (d := d) lam Lam) :=
  isClosed_isEllipticMatrix

/-- The eval continuous-linear map picking out the `(i, j)` entry of a pi
matrix. -/
def entryCLM (i j : Fin d) : (Fin d → Fin d → ℝ) →L[ℝ] ℝ :=
  let row : (Fin d → Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.proj (R := ℝ) i
  let entry : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) j
  entry.comp row

/-- The pi realization is integrable on compact sets. -/
theorem integrableOn_matPi (a : RegCoeffField d) {B : Set (Vec d)} (hB : IsCompact B) :
    IntegrableOn (matPi a) B volume := by
  rw [IntegrableOn, integrable_pi_iff]; intro i
  rw [integrable_pi_iff]; intro j
  exact (a.entry_locInt i j).integrableOn_isCompact hB

/-- The `Mat d` entry average agrees with the Bochner set-average of the pi
realization. -/
theorem avgMat_eq_setAverage (a : RegCoeffField d) {B : Set (Vec d)} (hB : IsCompact B) :
    avgMat B a = ⨍ x in B, matPi a x ∂volume := by
  funext i j
  have hInt := integrableOn_matPi a hB
  have heval : (∫ x in B, matPi a x ∂volume) i j = ∫ x in B, a x i j ∂volume := by
    have h := (entryCLM (d := d) i j).integral_comp_comm hInt
    simpa [entryCLM, matPi] using h.symm
  rw [avgMat, setAverage_eq]
  simp only [Pi.smul_apply]
  rw [heval, MeasureTheory.Measure.real]

/-! ## Forward direction (Jensen) -/

/-- **Forward (Jensen).**  If a carrier field is a.e.-elliptic on the restricted
measure of `U`, then its average over any compact ball `B ⊆ U` of positive finite
volume is elliptic.  Immediate from `Convex.set_average_mem` on the closed convex
elliptic locus. -/
theorem isEllipticMatrix_avgMat_of_aeRestrict {U : Set (Vec d)} {lam Lam : ℝ}
    {a : RegCoeffField d}
    (hae : ∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix lam Lam (a x))
    {B : Set (Vec d)} (hBcpt : IsCompact B) (hBU : B ⊆ U)
    (hB0 : volume B ≠ 0) (hBfin : volume B ≠ ⊤) :
    IsEllipticMatrix lam Lam (avgMat B a) := by
  have hfs : ∀ᵐ x ∂(volume.restrict B), matPi a x ∈ elliptPi lam Lam :=
    hae.filter_mono (ae_mono (Measure.restrict_mono hBU le_rfl))
  have hmem :=
    (convex_elliptPi lam Lam).set_average_mem (isClosed_elliptPi lam Lam) hB0 hBfin hfs
      (integrableOn_matPi a hBcpt)
  rw [avgMat_eq_setAverage a hBcpt]
  exact hmem

/-! ## Rational balls -/

/-- The real point with rational coordinates `q`. -/
def ratPt (q : Fin d → ℚ) : Vec d := fun i => (q i : ℝ)

/-- **Rational balls are cofinal in an open set.**  For a point `x` of an open set
`U` and any positive tolerance `ε`, there is a rational-centre rational-radius
closed ball of radius below `ε` that contains `x` and lies in `U`. -/
theorem exists_ratBall {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} (hx : x ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : Fin d → ℚ) (r : ℚ), 0 < (r : ℝ) ∧ (r : ℝ) < ε ∧
      x ∈ closedBall (ratPt q) (r : ℝ) ∧ closedBall (ratPt q) (r : ℝ) ⊆ U := by
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hU x hx
  have hclosed_sub : closedBall x (ρ / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hρsub
  set t : ℝ := min (ρ / 3) (ε / 2) with ht
  have htpos : 0 < t := lt_min (by linarith) (by linarith)
  obtain ⟨r, hr0, hrt⟩ := exists_rat_btwn htpos
  have hrpos : 0 < (r : ℝ) := hr0
  have hcoord : ∀ i : Fin d, ∃ q : ℚ, |x i - (q : ℝ)| < (r : ℝ) / 2 := by
    intro i
    obtain ⟨q, hq1, hq2⟩ :=
      exists_rat_btwn (show x i - (r : ℝ) / 2 < x i + (r : ℝ) / 2 by linarith)
    exact ⟨q, by rw [abs_lt]; constructor <;> linarith⟩
  choose qf hqf using hcoord
  refine ⟨qf, r, hrpos, ?_, ?_, ?_⟩
  · exact hrt.trans (by rw [ht]; exact (min_le_right _ _).trans_lt (by linarith))
  · rw [mem_closedBall, dist_comm, dist_pi_le_iff hrpos.le]
    intro i
    rw [Real.dist_eq]
    have hi : |ratPt qf i - x i| < (r : ℝ) / 2 := by
      rw [abs_sub_comm]; simpa [ratPt] using hqf i
    linarith
  · intro y hy
    apply hclosed_sub
    rw [mem_closedBall] at hy ⊢
    have hcx : dist (ratPt qf) x ≤ (r : ℝ) / 2 := by
      rw [dist_pi_le_iff (by linarith)]
      intro i
      rw [Real.dist_eq, abs_sub_comm]; exact (hqf i).le
    have hstep : dist y x ≤ (r : ℝ) + (r : ℝ) / 2 :=
      le_trans (dist_triangle y (ratPt qf) x) (by linarith)
    have hrle : (r : ℝ) ≤ ρ / 3 :=
      le_of_lt (hrt.trans_le (by rw [ht]; exact min_le_left _ _))
    linarith

/-! ## Backward direction (Lebesgue differentiation) -/

/-- **Backward (Lebesgue differentiation).**  If every rational ball `B ⊆ U`
(with `U` open) has elliptic average, then the carrier field is a.e.-elliptic on
`U`.  For a.e. `x` the centre-free Lebesgue differentiation theorem provides a
sequence of rational balls containing `x` and shrinking to it whose averages
converge to `a x`; each average is elliptic and the locus is closed, so `a x` is
elliptic. -/
theorem aeRestrict_isEllipticMatrix_of_forall_ratBall {U : Set (Vec d)}
    (hUopen : IsOpen U) {lam Lam : ℝ} {a : RegCoeffField d}
    (H : ∀ (q : Fin d → ℚ) (r : ℚ), 0 < (r : ℝ) → closedBall (ratPt q) (r : ℝ) ⊆ U →
      IsEllipticMatrix lam Lam (avgMat (closedBall (ratPt q) (r : ℝ)) a)) :
    ∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix lam Lam (a x) := by
  have hdiff : ∀ᵐ x ∂volume, ∀ i j : Fin d,
      ∀ {ι : Type} {l : Filter ι} (w : ι → Vec d) (δ : ι → ℝ)
        (_ : Tendsto δ l (𝓝[>] 0)) (_ : ∀ᶠ n in l, x ∈ closedBall (w n) (1 * δ n)),
        Tendsto (fun n => ⨍ y in closedBall (w n) (δ n), a y i j ∂volume) l (𝓝 (a x i j)) := by
    rw [MeasureTheory.ae_all_iff]; intro i
    rw [MeasureTheory.ae_all_iff]; intro j
    exact IsUnifLocDoublingMeasure.ae_tendsto_average volume (a.entry_locInt i j) 1
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem hUopen.measurableSet]
    with x hx_diff hxU
  -- rational balls shrinking to `x`
  choose qf rf hpos hlt hxin hsub using
    (fun n : ℕ => exists_ratBall hUopen hxU (show (0 : ℝ) < 1 / (n + 1) by positivity))
  set w : ℕ → Vec d := fun n => ratPt (qf n) with hw
  set δ : ℕ → ℝ := fun n => (rf n : ℝ) with hδ
  set B : ℕ → Set (Vec d) := fun n => closedBall (w n) (δ n) with hB
  have hδtend : Tendsto δ atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall (fun n => hpos n)⟩
    exact squeeze_zero (fun n => (hpos n).le) (fun n => (hlt n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hxmem : ∀ᶠ n in atTop, x ∈ closedBall (w n) (1 * δ n) :=
    Filter.Eventually.of_forall (fun n => by simpa [hw, hδ, one_mul] using hxin n)
  have hentry : ∀ i j, Tendsto (fun n => avgMat (B n) a i j) atTop (𝓝 (a x i j)) := by
    intro i j
    have hb := hx_diff i j (l := atTop) w δ hδtend hxmem
    simpa [avgMat_entry_eq_setAverage, hB, hw, hδ] using hb
  have htend : Tendsto (fun n => avgMat (B n) a) atTop (𝓝 (a x)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hentry i j
  refine (isClosed_isEllipticMatrix (lam := lam) (Lam := Lam)).mem_of_tendsto htend
    (Filter.Eventually.of_forall (fun n => ?_))
  exact H (qf n) (rf n) (hpos n) (hsub n)

/-! ## The characterization -/

/-- **The rational-ball characterization of spatial a.e. ellipticity.**  For an
open set `U`, a carrier field is a.e.-elliptic on the restricted measure of `U`
iff all its rational-ball averages inside `U` are elliptic.  This is the exact
set equality behind the honest `LocalSigmaR U`-measurability of the slice
event. -/
theorem aeRestrict_isEllipticMatrix_iff_forall_ratBall {U : Set (Vec d)}
    (hUopen : IsOpen U) (lam Lam : ℝ) (a : RegCoeffField d) :
    (∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix lam Lam (a x)) ↔
      ∀ (q : Fin d → ℚ) (r : ℚ), 0 < (r : ℝ) → closedBall (ratPt q) (r : ℝ) ⊆ U →
        IsEllipticMatrix lam Lam (avgMat (closedBall (ratPt q) (r : ℝ)) a) := by
  refine ⟨fun hae q r hr hsub => ?_, aeRestrict_isEllipticMatrix_of_forall_ratBall hUopen⟩
  refine isEllipticMatrix_avgMat_of_aeRestrict hae (isCompact_closedBall _ _) hsub ?_ ?_
  · exact (measure_closedBall_pos volume (ratPt q) hr).ne'
  · exact measure_closedBall_lt_top.ne

end

end Homogenization
