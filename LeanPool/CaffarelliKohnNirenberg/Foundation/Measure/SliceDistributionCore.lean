/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionLocal
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionMollifyBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionSwap
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionTransport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientBumps

/-!
# From a countable family of mollifier bumps to every test function

A distributional identity that is only known against a *countable* family of
test functions can be upgraded to all test functions when the family is rich
enough.  The family used here is the family of mollifier bumps
`x ↦ mollifier (sliceRadius n) (x - y)` centred at the points `y` of a dense
set.  The upgrade has three steps.

* The pairing of a locally integrable field with a translated bump depends
  continuously on the centre, so vanishing on a dense set of centres gives
  vanishing at every admissible centre.
* Integrating the resulting identity against a test function `ψ` and exchanging
  the order of integration replaces the bump by the mollification of the
  transform of `ψ` that appears in the pairing.
* Letting the radius tend to zero recovers that transform itself.

The argument is carried out once, for an abstract kernel family `κ` and an
abstract transform `T` of the test function, and then specialised to the two
pairings used in `paper/ckn.tex`: the spatial divergence pairing
`∑ᵢ gᵢ ∂ᵢψ` and the plain multiplication pairing `F ψ`.  This is the mechanism
behind the almost-everywhere slice identities there: the null set produced by
testing one test function at a time is replaced by a single null set valid for
every test function.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set


noncomputable section

namespace CKN

/-- The `i`th coordinate derivative of the mollifier of radius `sliceRadius n`. -/
def sliceMollifierDeriv {d : ℕ} (n : ℕ) (i : Fin d) : Vec d → ℝ :=
  fun z => (fderiv ℝ (mollifier (d := d) (sliceRadius n) (sliceRadius_pos n)) z)
    (basisVec i)

private theorem sliceMollifierDeriv_continuous {d : ℕ} (n : ℕ) (i : Fin d) :
    Continuous (sliceMollifierDeriv (d := d) n i) :=
  continuous_fderiv_mollifier_apply (sliceRadius_pos n) i

private theorem sliceMollifierDeriv_eq_zero {d : ℕ} (n : ℕ) (i : Fin d)
    {z : Vec d} (hz : sliceRadius n < ‖z‖) :
    sliceMollifierDeriv (d := d) n i z = 0 :=
  fderiv_mollifier_apply_eq_zero (sliceRadius_pos n) hz i

/-- The general mollifier-bump family upgrade.  The pairing of a field `g` that
is locally integrable on an open set `Ω` against the kernels `κ n i` centred at
the points of a dense set `Q` determines the pairing against any transform `T`
of a compactly supported test function `ψ`, provided the two are linked by the
mollification identity `hid`. -/
theorem slice_pairing_zero_of_mollifier_family {d : ℕ} {ι : Type*} [Fintype ι]
    {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {Q : Set (Vec d)} (hQ : Dense Q)
    {g : Vec d → ι → ℝ}
    (hg : ∀ i : ι,
      MeasureTheory.LocallyIntegrableOn (fun x => g x i) Ω MeasureTheory.volume)
    {κ : ℕ → ι → Vec d → ℝ}
    (hκcont : ∀ (n : ℕ) (i : ι), Continuous (κ n i))
    (hκzero : ∀ (n : ℕ) (i : ι), ∀ z : Vec d, sliceRadius n < ‖z‖ → κ n i z = 0)
    {ψ : Vec d → ℝ} (hψcont : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω)
    {T : ι → Vec d → ℝ} (hTcont : ∀ i : ι, Continuous (T i))
    (hTsupp : ∀ (i : ι), ∀ x : Vec d, x ∉ tsupport ψ → T i x = 0)
    (hid : ∀ (n : ℕ) (i : ι) (x : Vec d),
      (∫ y, ψ y * κ n i (x - y) ∂MeasureTheory.volume)
        = mollify (T i) (sliceRadius n) (sliceRadius_pos n) x)
    (hzero : ∀ y ∈ Q, ∀ n : ℕ, closedBall y (sliceRadius n) ⊆ Ω →
      ∫ x in Ω, ∑ i : ι, g x i * κ n i (x - y) ∂MeasureTheory.volume = 0) :
    ∫ x in Ω, ∑ i : ι, g x i * T i x ∂MeasureTheory.volume = 0 := by
  classical
  have hκcompact : ∀ (n : ℕ) (i : ι), HasCompactSupport (κ n i) := by
    intro n i
    refine HasCompactSupport.intro
      (isCompact_closedBall (0 : Vec d) (sliceRadius n)) fun z hz => ?_
    refine hκzero n i z ?_
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
  have hTsuppc : ∀ i : ι, HasCompactSupport (T i) := fun i =>
    HasCompactSupport.intro hψc.isCompact (hTsupp i)
  have hMbound : ∀ i : ι, ∃ M : ℝ, ∀ x : Vec d, |T i x| ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := (hTsuppc i).exists_bound_of_continuous (hTcont i)
    exact ⟨M, fun x => by simpa only [Real.norm_eq_abs] using hM x⟩
  obtain ⟨δ, hδpos, hδΩ⟩ := hψc.isCompact.exists_cthickening_subset_open hΩ hψΩ
  set K : Set (Vec d) := cthickening δ (tsupport ψ) with hKdef
  have hKcompact : IsCompact K := hψc.isCompact.cthickening
  have hKmeas : MeasurableSet K := Metric.isClosed_cthickening.measurableSet
  have hψK : tsupport ψ ⊆ K := self_subset_cthickening _
  set G : ι → Vec d → ℝ := fun i => Set.indicator K (fun x => g x i) with hGdef
  have hGint : ∀ i : ι, MeasureTheory.Integrable (G i) MeasureTheory.volume :=
    fun i => ((hg i).integrableOn_compact_subset hδΩ hKcompact).integrable_indicator
      hKmeas
  have hGeq : ∀ (i : ι), ∀ x ∈ K, G i x = g x i := by
    intro i x hx
    simp only [hGdef, Set.indicator_of_mem hx]
  -- Step 1: the bump pairing vanishes at every admissible centre.
  have hDzero : ∀ n : ℕ, ∀ y : Vec d, closedBall y (sliceRadius n) ⊆ Ω →
      ∑ i : ι, ∫ x, g x i * κ n i (x - y) ∂MeasureTheory.volume = 0 := by
    intro n
    have hUopen : IsOpen {y : Vec d | closedBall y (sliceRadius n) ⊆ Ω} := by
      rw [Metric.isOpen_iff]
      intro y₀ hy₀
      obtain ⟨δ', hδ'pos, hδ'Ω, hδ'ball⟩ := exists_delta_cthickening_subset hΩ hy₀
      exact ⟨δ', hδ'pos, fun y hy =>
        (hδ'ball y (le_of_lt (Metric.mem_ball.mp hy))).trans hδ'Ω⟩
    have hcont : ∀ y ∈ {y : Vec d | closedBall y (sliceRadius n) ⊆ Ω},
        ContinuousAt (fun y : Vec d => ∑ i : ι,
          ∫ x, g x i * κ n i (x - y) ∂MeasureTheory.volume) y := by
      intro y₀ hy₀
      exact tendsto_finsetSum _ fun i _ =>
        continuousAt_integral_mul_translate hΩ (hg i) (hκcont n i)
          (fun z hz => hκzero n i z hz) hy₀
    have hqz : ∀ y ∈ {y : Vec d | closedBall y (sliceRadius n) ⊆ Ω} ∩ Q,
        ∑ i : ι, ∫ x, g x i * κ n i (x - y) ∂MeasureTheory.volume = 0 := by
      intro y hy
      have h1 := hzero y hy.2 n hy.1
      have h2 : ∫ x, ∑ i : ι, g x i * κ n i (x - y) ∂MeasureTheory.volume = 0 := by
        rw [← h1]
        symm
        refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        refine Finset.sum_eq_zero fun i _ => ?_
        have hxb : sliceRadius n < ‖x - y‖ := by
          by_contra hcon
          refine hx (hy.1 ?_)
          simpa only [Metric.mem_closedBall, dist_eq_norm] using not_lt.mp hcon
        rw [hκzero n i _ hxb, mul_zero]
      have hintbl : ∀ i : ι, MeasureTheory.Integrable
          (fun x => g x i * κ n i (x - y)) MeasureTheory.volume := fun i =>
        integrable_mul_translate (hg i) (hκcont n i)
          (fun z hz => hκzero n i z hz) hy.1
      rw [MeasureTheory.integral_finsetSum _ fun i _ => hintbl i] at h2
      exact h2
    exact eq_zero_of_dense_of_continuousAt hQ hUopen hcont hqz
  -- Step 2: for small radii every point of `tsupport ψ` is an admissible centre.
  have hadm : ∀ n : ℕ, sliceRadius n ≤ δ → ∀ y ∈ tsupport ψ,
      closedBall y (sliceRadius n) ⊆ Ω := by
    intro n hn y hy x hx
    exact hδΩ (Metric.mem_cthickening_of_dist_le x y δ (tsupport ψ) hy
      (le_trans (Metric.mem_closedBall.mp hx) hn))
  -- Step 3: pairing with `ψ` and exchanging the order of integration.
  have hpair : ∀ n : ℕ, sliceRadius n ≤ δ →
      ∑ i : ι, ∫ x, G i x * mollify (T i) (sliceRadius n) (sliceRadius_pos n) x
        ∂MeasureTheory.volume = 0 := by
    intro n hn
    have hswap : ∀ i : ι,
        (∫ y, ψ y * ∫ x, G i x * κ n i (x - y)
            ∂MeasureTheory.volume ∂MeasureTheory.volume)
          = ∫ x, G i x * mollify (T i) (sliceRadius n) (sliceRadius_pos n) x
            ∂MeasureTheory.volume := by
      intro i
      rw [integral_mul_integral_translate_swap hψcont hψc (hGint i)
        (hκcont n i) (hκcompact n i)]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => ?_)
      change G i x * (∫ y, ψ y * κ n i (x - y) ∂MeasureTheory.volume)
        = G i x * mollify (T i) (sliceRadius n) (sliceRadius_pos n) x
      rw [hid n i x]
    have hGkey : ∀ y ∈ tsupport ψ, ∀ i : ι,
        (∫ x, G i x * κ n i (x - y) ∂MeasureTheory.volume)
          = ∫ x, g x i * κ n i (x - y) ∂MeasureTheory.volume := by
      intro y hy i
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => ?_)
      change G i x * κ n i (x - y) = g x i * κ n i (x - y)
      by_cases hx : x ∈ K
      · rw [hGeq i x hx]
      · have hxb : sliceRadius n < ‖x - y‖ := by
          by_contra hcon
          refine hx (Metric.mem_cthickening_of_dist_le x y δ (tsupport ψ) hy ?_)
          have hxy : dist x y ≤ sliceRadius n := by
            simpa only [dist_eq_norm] using not_lt.mp hcon
          exact hxy.trans hn
        rw [hκzero n i _ hxb, mul_zero, mul_zero]
    have hpt : ∀ y : Vec d, ψ y * ∑ i : ι,
        (∫ x, G i x * κ n i (x - y) ∂MeasureTheory.volume) = 0 := by
      intro y
      by_cases hy : y ∈ tsupport ψ
      · have h1 : (∑ i : ι, ∫ x, G i x * κ n i (x - y) ∂MeasureTheory.volume)
            = ∑ i : ι, ∫ x, g x i * κ n i (x - y) ∂MeasureTheory.volume :=
          Finset.sum_congr rfl fun i _ => hGkey y hy i
        rw [h1, hDzero n y (hadm n hn y hy), mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    have hint : ∀ i : ι, MeasureTheory.Integrable
        (fun y => ψ y * ∫ x, G i x * κ n i (x - y) ∂MeasureTheory.volume)
        MeasureTheory.volume := fun i =>
      integrable_mul_integral_translate hψcont hψc (hGint i) (hκcont n i)
        (hκcompact n i)
    have hsum : ∑ i : ι, (∫ y, ψ y *
        ∫ x, G i x * κ n i (x - y) ∂MeasureTheory.volume
          ∂MeasureTheory.volume) = 0 := by
      rw [← MeasureTheory.integral_finsetSum _ fun i _ => hint i]
      have hpt' : ∀ y : Vec d, (∑ i : ι, ψ y *
          ∫ x, G i x * κ n i (x - y) ∂MeasureTheory.volume) = 0 := by
        intro y
        rw [← Finset.mul_sum]
        exact hpt y
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt')]
      simp
    calc ∑ i : ι, (∫ x, G i x *
        mollify (T i) (sliceRadius n) (sliceRadius_pos n) x
          ∂MeasureTheory.volume)
        = ∑ i : ι, (∫ y, ψ y *
          ∫ x, G i x * κ n i (x - y) ∂MeasureTheory.volume
            ∂MeasureTheory.volume) :=
          Finset.sum_congr rfl fun i _ => (hswap i).symm
      _ = 0 := hsum
  -- Step 4: let the radius tend to zero.
  have hlim : ∀ i : ι, Filter.Tendsto
      (fun n : ℕ => ∫ x, G i x *
        mollify (T i) (sliceRadius n) (sliceRadius_pos n) x
          ∂MeasureTheory.volume)
      Filter.atTop
      (nhds (∫ x, G i x * T i x ∂MeasureTheory.volume)) := by
    intro i
    obtain ⟨M, hM⟩ := hMbound i
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => M * ‖G i x‖) (fun n => ?_) ((hGint i).norm.const_mul M)
      (fun n => ?_) ?_
    · exact (hGint i).aestronglyMeasurable.mul
        (mollify_continuous (sliceRadius_pos n)
          (hTcont i).locallyIntegrable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hb := abs_mollify_le (hTcont i) hM (sliceRadius_pos n) x
      calc ‖G i x * mollify (T i) (sliceRadius n) (sliceRadius_pos n) x‖
          = ‖G i x‖ * |mollify (T i) (sliceRadius n) (sliceRadius_pos n) x| := by
            simp [Real.norm_eq_abs]
        _ ≤ ‖G i x‖ * M := by gcongr
        _ = M * ‖G i x‖ := mul_comm _ _
    · refine Filter.Eventually.of_forall fun x => ?_
      exact Filter.Tendsto.const_mul (G i x)
        (mollify_tendsto_of_continuous tendsto_sliceRadius_atTop
          sliceRadius_pos (hTcont i) x)
  have hlimsum : Filter.Tendsto
      (fun n : ℕ => ∑ i : ι, ∫ x, G i x *
        mollify (T i) (sliceRadius n) (sliceRadius_pos n) x
          ∂MeasureTheory.volume)
      Filter.atTop
      (nhds (∑ i : ι, ∫ x, G i x * T i x ∂MeasureTheory.volume)) :=
    tendsto_finsetSum _ fun i _ => hlim i
  have hsmall : ∀ᶠ n in Filter.atTop, sliceRadius n ≤ δ := by
    filter_upwards [tendsto_sliceRadius_atTop.eventually (gt_mem_nhds hδpos)]
      with n hn using le_of_lt hn
  have hfinal : ∑ i : ι, ∫ x, G i x * T i x ∂MeasureTheory.volume = 0 := by
    refine tendsto_nhds_unique hlimsum ?_
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [hsmall] with n hn using (hpair n hn).symm
  -- Step 5: identify the original integral.
  have hgψ : ∀ (i : ι) (x : Vec d), g x i * T i x = G i x * T i x := by
    intro i x
    by_cases hx : x ∈ K
    · rw [hGeq i x hx]
    · have hx' : x ∉ tsupport ψ := fun h => hx (hψK h)
      rw [hTsupp i x hx', mul_zero, mul_zero]
  calc ∫ x in Ω, ∑ i : ι, g x i * T i x ∂MeasureTheory.volume
      = ∫ x, ∑ i : ι, g x i * T i x ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        have hx' : x ∉ tsupport ψ := fun h => hx (hψΩ h)
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hTsupp i x hx', mul_zero]
    _ = ∫ x, ∑ i : ι, G i x * T i x ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun x => ?_)
        exact Finset.sum_congr rfl fun i _ => hgψ i x
    _ = ∑ i : ι, ∫ x, G i x * T i x ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_finsetSum _ fun i _ => ?_
        obtain ⟨M, hM⟩ := hMbound i
        exact (hGint i).mul_bdd (hTcont i).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => by
            simpa only [Real.norm_eq_abs] using hM x)
    _ = 0 := hfinal

/-- The divergence instance of the mollifier-bump family upgrade.  If the
distributional divergence pairing of a field `g` that is locally integrable on
an open set `Ω` vanishes against every mollifier bump centred at a point of a
dense set `Q` and small enough to fit inside `Ω`, then it vanishes against every
smooth compactly supported test function supported in `Ω`. -/
theorem slice_divergence_zero_of_mollifier_family {d : ℕ}
    {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {Q : Set (Vec d)} (hQ : Dense Q)
    {g : Vec d → Fin d → ℝ}
    (hg : ∀ i : Fin d,
      MeasureTheory.LocallyIntegrableOn (fun x => g x i) Ω MeasureTheory.volume)
    (hzero : ∀ y ∈ Q, ∀ n : ℕ, closedBall y (sliceRadius n) ⊆ Ω →
      ∫ x in Ω, ∑ i : Fin d, g x i *
        (fderiv ℝ (fun z : Vec d =>
          mollifier (d := d) (sliceRadius n) (sliceRadius_pos n) (z - y)) x)
          (basisVec i) ∂MeasureTheory.volume = 0)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) :
    ∫ x in Ω, ∑ i : Fin d, g x i * (fderiv ℝ ψ x) (basisVec i)
      ∂MeasureTheory.volume = 0 := by
  have hdcont : ∀ i : Fin d,
      Continuous fun x : Vec d => (fderiv ℝ ψ x) (basisVec i) := by
    intro i
    simpa using (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  refine slice_pairing_zero_of_mollifier_family (κ := sliceMollifierDeriv) hΩ hQ
    hg (fun n i => sliceMollifierDeriv_continuous n i)
    (fun n i z hz => sliceMollifierDeriv_eq_zero n i hz)
    hψ.continuous hψc hψΩ (T := fun i x => (fderiv ℝ ψ x) (basisVec i))
    hdcont (fun i x hx => ?_) (fun n i x => ?_) (fun y hy n hn => ?_)
  · rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
    simp
  · exact integral_mul_fderiv_mollifier_sub hψ i (sliceRadius_pos n) x
  · have h := hzero y hy n hn
    rw [← h]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sliceMollifierDeriv, fderiv_mollifier_sub_apply]

/-- The multiplication instance of the mollifier-bump family upgrade.  If the
integral of a function `F` that is locally integrable on an open set `Ω` against
every small mollifier bump centred at a point of a dense set `Q` vanishes, then
`∫ F ψ` vanishes for every continuous compactly supported `ψ` supported in
`Ω`. -/
theorem slice_integral_mul_zero_of_mollifier_family {d : ℕ}
    {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {Q : Set (Vec d)} (hQ : Dense Q)
    {F : Vec d → ℝ}
    (hF : MeasureTheory.LocallyIntegrableOn F Ω MeasureTheory.volume)
    (hzero : ∀ y ∈ Q, ∀ n : ℕ, closedBall y (sliceRadius n) ⊆ Ω →
      ∫ x in Ω, F x *
        mollifier (d := d) (sliceRadius n) (sliceRadius_pos n) (x - y)
        ∂MeasureTheory.volume = 0)
    {ψ : Vec d → ℝ} (hψcont : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) :
    ∫ x in Ω, F x * ψ x ∂MeasureTheory.volume = 0 := by
  have hmain : ∫ x in Ω, ∑ _i : Unit, F x * ψ x ∂MeasureTheory.volume = 0 := by
    refine slice_pairing_zero_of_mollifier_family
      (g := fun x _ => F x)
      (κ := fun n _ => mollifier (d := d) (sliceRadius n) (sliceRadius_pos n))
      hΩ hQ (fun _ => hF) (fun n _ => mollifier_contDiff (n := 0) _ |>.continuous)
      (fun n _ z hz => mollifier_eq_zero_of_lt_norm (sliceRadius_pos n) hz)
      hψcont hψc hψΩ (T := fun _ => ψ) (fun _ => hψcont)
      (fun _ x hx => image_eq_zero_of_notMem_tsupport hx)
      (fun n _ x => integral_mul_mollifier_sub ψ (sliceRadius_pos n) x)
      (fun y hy n hn => ?_)
    have h := hzero y hy n hn
    rw [← h]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    simp
  simpa using hmain

end CKN

end
