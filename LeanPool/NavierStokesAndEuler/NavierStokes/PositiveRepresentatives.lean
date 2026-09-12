/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryRepresentatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityHomogeneity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Positive-time representatives and the genuine stable inverse branch

The totalized `coordinateQ` is used only at positive time.  A different,
constructed inverse extends the stable branch across its regular zero-time
face.  The actual mask representatives stay at positive time.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PositiveRepresentatives

open Set Filter Function
open scoped Topology ContDiff InnerProductSpace
open SimilarityCoordinates

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Label: an abbreviation for `PartitionedCovariance.UnsignedLabel`. -/
abbrev Label := PartitionedCovariance.UnsignedLabel

/-- Positive time, given by `{p | 0 < p.2.2}`. -/
noncomputable def positiveTime : Set Slow := {p | 0 < p.2.2}
/-- Positive part, given by `K ∩ positiveTime`. -/
noncomputable def positivePart (K : Set Slow) : Set Slow := K ∩ positiveTime
/-- Active label, given by `PrimaryRepresentatives.ActiveLabel (positivePart K)`. -/
noncomputable def ActiveLabel (K : Set Slow) := PrimaryRepresentatives.ActiveLabel (positivePart K)
/-- Representative, given by `PrimaryRepresentatives.representative (positivePart K) L`. -/
noncomputable def representative (K : Set Slow) (L : ActiveLabel K) : Slow :=
  PrimaryRepresentatives.representative (positivePart K) L

theorem positiveTime_open : IsOpen positiveTime :=
  isOpen_lt continuous_const continuous_snd.snd

theorem positiveTime_convex : Convex ℝ positiveTime := by
  intro x hx y hy a b ha hb hab
  change 0 < a * x.2.2 + b * y.2.2
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb' : b = 1 := by linarith
    simpa only [zero_mul, zero_add, hb', one_mul, positiveTime, Set.mem_ofPred_eq] using hy
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)

theorem representative_mem (K : Set Slow) (L : ActiveLabel K) : representative K L ∈ K :=
  (PrimaryRepresentatives.representative_mem (positivePart K) L).1

theorem representative_time_pos (K : Set Slow) (L : ActiveLabel K) :
    0 < (representative K L).2.2 :=
  (PrimaryRepresentatives.representative_mem (positivePart K) L).2

theorem representative_mem_tsupport (K : Set Slow) (L : ActiveLabel K) :
    representative K L ∈ tsupport (PrimaryRepresentatives.nativeMask L.val.1 L.val.2) :=
  PrimaryRepresentatives.representative_mem_tsupport (positivePart K) L

theorem representative_enlarged_distance (K : Set Slow) (L : ActiveLabel K)
    {p : Slow} (hp : p ∈ PrimaryRepresentatives.gridBox L.val.1 L.val.2 2) :
    ‖p - representative K L‖ ≤ 3 / ChartScales.S L.val.1 ^ 3 :=
  PrimaryRepresentatives.representative_enlarged_distance (positivePart K) L hp

theorem representative_support_distance (K : Set Slow) (L : ActiveLabel K)
    {p : Slow} (hp : p ∈ tsupport (PrimaryRepresentatives.nativeMask L.val.1 L.val.2)) :
    ‖p - representative K L‖ ≤ 2 / ChartScales.S L.val.1 ^ 3 :=
  PrimaryRepresentatives.representative_support_distance (positivePart K) L hp

theorem physicalMask_has_positive_representative {h a b : ℝ} (L : Label) (hL : 1 ≤ L.1)
    {q : ℝ} {x : SlotColoring.Position} (hq : 0 < q) (hR : 0 ≤ x 0) (hT : 0 < x 2)
    (he : forwardScalar (2 * h) (x 1) q = x 2)
    (hX : x 0 ^ 2 / (2 * q) ∈ Icc a b)
    (hm : PartitionedCovariance.mask (CoordinateAlgebra.D h) L q x ≠ 0) :
    ∃ A : ActiveLabel (PrimaryRepresentatives.referenceCompact h a b), A.val = L := by
  apply PrimaryRepresentatives.physicalMask_active
  · exact hL
  · refine ⟨PrimaryRepresentatives.physicalMask_normalized_mem L hq hR hT.le he hX hm, ?_⟩
    rw [PrimaryRepresentatives.normalizedSlow_coordinates]
    exact div_pos hT (ChartScales.Q_pos _)
  · exact hm

/-! ## A smooth inverse on the stable branch, including its zero-time face -/

/-- Stable source, given by `{p | 0 < p.1 ∧ 0 < scalarSlope a p.2 p.1}`. -/
noncomputable def stableSource (a : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < scalarSlope a p.2 p.1}

/-- Stable target, given by `forwardMap a '' stableSource a`. -/
noncomputable def stableTarget (a : ℝ) : Set (ℝ × ℝ) := forwardMap a '' stableSource a

theorem scalarSlope_smoothAt {a : ℝ} {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => scalarSlope a x.2 x.1) p :=
  contDiffAt_const.sub (((contDiffAt_snd.pow 2).mul contDiffAt_const).mul
    (contDiffAt_fst.rpow_const_of_ne hp))

theorem stableSource_open (a : ℝ) : IsOpen (stableSource a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hq : ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < x.1 :=
    continuousAt_fst.eventually (Ioi_mem_nhds hp.1)
  have hm : ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < scalarSlope a x.2 x.1 :=
    (scalarSlope_smoothAt hp.1.ne').continuousAt.eventually (Ioi_mem_nhds hp.2)
  exact hq.and hm

theorem scalarSlope_lower_of_nonnegative {a q z : ℝ} (ha : 0 ≤ a) (hq : 0 < q)
    (hf : 0 ≤ forwardScalar a z q) : 1 - a ≤ scalarSlope a z q := by
  have hs : z ^ 2 * q ^ a / q ≤ 1 := (div_le_one hq).mpr (by
    dsimp only [forwardScalar] at hf
    linarith)
  have hm := mul_le_mul_of_nonneg_left hs ha
  rw [scalarSlope, Real.rpow_sub_one hq.ne']
  calc
    1 - a ≤ 1 - a * (z ^ 2 * q ^ a / q) := by linarith
    _ = _ := by ring

theorem scalarSlope_mono {a z q r : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 0 < q) (hqr : q ≤ r) : scalarSlope a z q ≤ scalarSlope a z r := by
  have hp := Real.rpow_le_rpow_of_nonpos hq hqr (sub_nonpos.mpr ha1)
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg z) ha)
  dsimp only [scalarSlope]
  linarith

theorem forwardScalar_hasDerivAt {a z q : ℝ} (hq : q ≠ 0) :
    HasDerivAt (forwardScalar a z) (scalarSlope a z q) q := by
  have hd := (hasDerivAt_id q).sub
    (((hasDerivAt_id q).rpow_const (p := a) (Or.inl hq)).const_mul (z ^ 2))
  convert! hd using 1
  simp [scalarSlope, mul_assoc]

theorem forwardScalar_lt_on_stable {a z q r : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : 0 < q) (hm : 0 < scalarSlope a z q) (hqr : q < r) :
    forwardScalar a z q < forwardScalar a z r := by
  have hd (s : ℝ) (hs : s ∈ Icc q r) := forwardScalar_hasDerivAt (a := a) (z := z)
    (hq.trans_le hs.1).ne'
  have hmono : StrictMonoOn (forwardScalar a z) (Icc q r) :=
    strictMonoOn_of_deriv_pos (convex_Icc q r)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt) (fun s hs => by
        rw [(hd s (interior_subset hs)).deriv]
        exact hm.trans_le (scalarSlope_mono ha ha1 hq (interior_subset hs).1))
  exact hmono ⟨le_rfl, hqr.le⟩ ⟨hqr.le, le_rfl⟩ hqr

theorem forwardMap_injOn_stable {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    InjOn (forwardMap a) (stableSource a) := by
  rintro ⟨q, z⟩ hq ⟨r, w⟩ hr he
  have hz : z = w := congrArg Prod.snd he
  subst w
  have hf : forwardScalar a z q = forwardScalar a z r := congrArg Prod.fst he
  have hqr : q = r := by
    rcases lt_trichotomy q r with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (forwardScalar_lt_on_stable ha ha1 hq.1 hq.2 hlt)) hf)
    · exact heq
    · exact False.elim ((ne_of_lt (forwardScalar_lt_on_stable ha ha1 hr.1 hr.2 hgt)) hf.symm)
  exact Prod.ext hqr rfl

/-- Stable inverse, choosing the witness provided by `hp`. -/
noncomputable def stableInverse (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := by
  classical
  exact if hp : p ∈ stableTarget a then Classical.choose hp else (1, p.2)

theorem stableInverse_spec {a : ℝ} {p : ℝ × ℝ} (hp : p ∈ stableTarget a) :
    stableInverse a p ∈ stableSource a ∧ forwardMap a (stableInverse a p) = p := by
  simp only [stableInverse, dite_eq_left hp]
  exact Classical.choose_spec hp

theorem stableInverse_forwardMap {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {p : ℝ × ℝ} (hp : p ∈ stableSource a) : stableInverse a (forwardMap a p) = p := by
  have hs := stableInverse_spec (show forwardMap a p ∈ stableTarget a from ⟨p, hp, rfl⟩)
  exact forwardMap_injOn_stable ha ha1 hs.1 hp hs.2

theorem stableTarget_open (a : ℝ) : IsOpen (stableTarget a) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨p, hp, rfl⟩
  have hsm := forwardMap_smooth (a := a) hp.1.ne'
  have hder := forwardMap_hasFDerivAt (a := a) hp.1.ne' hp.2.ne'
  have hs := hsm.hasStrictFDerivAt' hder (by simp)
  rw [← hs.map_nhds_eq_of_equiv]
  change forwardMap a ⁻¹' stableTarget a ∈ 𝓝 p
  filter_upwards [(stableSource_open a).mem_nhds hp] with x hx
  exact ⟨x, hx, rfl⟩

theorem stableInverse_smoothAt {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {p : ℝ × ℝ} (hp : p ∈ stableTarget a) : ContDiffAt ℝ ∞ (stableInverse a) p := by
  rcases hp with ⟨q, hq, rfl⟩
  have hsm := forwardMap_smooth (a := a) hq.1.ne'
  have hder := forwardMap_hasFDerivAt (a := a) hq.1.ne' hq.2.ne'
  have hs := hsm.hasStrictFDerivAt' hder (by simp)
  have hinv : ∀ᶠ x in 𝓝 q, stableInverse a (forwardMap a x) = x := by
    filter_upwards [(stableSource_open a).mem_nhds hq] with x hx
    exact stableInverse_forwardMap ha ha1 hx
  have heq := hs.localInverse_unique hinv
  exact (hsm.to_localInverse hder (by simp)).congr_of_eventuallyEq heq

theorem positiveTime_mem_stableTarget {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : p ∈ stableTarget a := by
  have hq := coordinateQ_spec ha ha1 hp
  refine ⟨(coordinateQ a p, p.2), ⟨hq.1, ?_⟩, Prod.ext hq.2 rfl⟩
  exact scalarSlope_pos ha ha1 hq.1 (by rwa [hq.2])

theorem stableInverse_eq_inverseMap {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : 0 < p.1) : stableInverse a p = inverseMap a p := by
  have hs := stableInverse_spec (positiveTime_mem_stableTarget ha ha1 hp)
  have hz : (stableInverse a p).2 = p.2 := by
    simpa only [forwardMap] using congrArg (fun x : ℝ × ℝ => x.2) hs.2
  apply Prod.ext
  · change _ = coordinateQ a p
    apply eq_coordinateQ ha ha1 hp hs.1.1
    have hq := congrArg Prod.fst hs.2
    simpa only [forwardMap, hz] using hq
  · exact hz

/-! ## The old closed reference set lies inside the regular stable target -/

/-- Source coordinates are `(R,(Z,rho))`, with `rho` independent of the
totalized inverse. -/
noncomputable def forwardSlow (h : ℝ) (p : Slow) : Slow :=
  (p.1, (p.2.1, forwardScalar (2 * h) p.2.1 p.2.2))

/-- Lifted box, given by `Icc (Real.sqrt a) (2 * Real.sqrt b) ×ˢ (Icc (-2 : ℝ) 2 ×ˢ Icc (1 / 2 :
ℝ) 2)`. -/
noncomputable def liftedBox (a b : ℝ) : Set Slow :=
  Icc (Real.sqrt a) (2 * Real.sqrt b) ×ˢ
    (Icc (-2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2)

/-- Lifted reference, given by `liftedBox a b ∩ {p | 0 ≤ (forwardSlow h p).2.2 ∧ a * (2 * p.2.2)
≤ p.1 ^ 2 ∧ p.1 ^ 2 ≤ b * (2 * p.2.2)}`. -/
noncomputable def liftedReference (h a b : ℝ) : Set Slow :=
  liftedBox a b ∩ {p | 0 ≤ (forwardSlow h p).2.2 ∧
    a * (2 * p.2.2) ≤ p.1 ^ 2 ∧ p.1 ^ 2 ≤ b * (2 * p.2.2)}

theorem forwardSlow_continuous {h : ℝ} (hh : 0 ≤ h) : Continuous (forwardSlow h) :=
  continuous_fst.prodMk (continuous_snd.fst.prodMk (continuous_snd.snd.sub
    ((continuous_snd.fst.pow 2).mul
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 2 * h)).comp continuous_snd.snd))))

theorem liftedReference_isCompact {h a b : ℝ} (hh : 0 ≤ h) :
    IsCompact (liftedReference h a b) := by
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
  exact (isClosed_le continuous_const (forwardSlow_continuous hh).snd.snd).inter
    ((isClosed_le (continuous_const.mul (continuous_const.mul continuous_snd.snd))
      (continuous_fst.pow 2)).inter
      (isClosed_le (continuous_fst.pow 2)
        (continuous_const.mul (continuous_const.mul continuous_snd.snd))))

theorem activeReference_subset_lifted_image {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) :
    PrimaryRepresentatives.activeReference h a b ⊆ forwardSlow h '' liftedReference h a b := by
  intro p hp
  have hb := PrimaryRepresentatives.activeReference_subset_box hh hh1 ha hab hp
  rcases hp with ⟨hR, hT, rho, hrho, he, hX⟩
  have hrhopos : 0 < rho := lt_of_lt_of_le (by norm_num) hrho.1
  refine ⟨(p.1, (p.2.1, rho)), ⟨⟨hb.1, hb.2.1, hrho⟩, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [forwardSlow, he] using hT
    · exact (le_div_iff₀ (by positivity : 0 < 2 * rho)).mp hX.1
    · exact (div_le_iff₀ (by positivity : 0 < 2 * rho)).mp hX.2
  · exact Prod.ext rfl (Prod.ext rfl he)

theorem lifted_image_subset_activeReference {h a b : ℝ} :
    forwardSlow h '' liftedReference h a b ⊆ PrimaryRepresentatives.activeReference h a b := by
  rintro _ ⟨p, hp, rfl⟩
  have hrho : 0 < p.2.2 := lt_of_lt_of_le (by norm_num) hp.1.2.2.1
  refine ⟨(Real.sqrt_nonneg a).trans hp.1.1.1, hp.2.1, p.2.2, hp.1.2.2, rfl, ?_⟩
  exact ⟨(le_div_iff₀ (by positivity : 0 < 2 * p.2.2)).mpr hp.2.2.1,
    (div_le_iff₀ (by positivity : 0 < 2 * p.2.2)).mpr hp.2.2.2⟩

theorem referenceCompact_eq_lifted_image {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) :
    PrimaryRepresentatives.referenceCompact h a b = forwardSlow h '' liftedReference h a b := by
  apply Subset.antisymm
  · exact closure_minimal (activeReference_subset_lifted_image hh hh1 ha hab)
      (((liftedReference_isCompact hh).image (forwardSlow_continuous hh)).isClosed)
  · exact lifted_image_subset_activeReference.trans subset_closure

theorem referenceCompact_eq_activeReference {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) :
    PrimaryRepresentatives.referenceCompact h a b = PrimaryRepresentatives.activeReference h a b :=
        by
  rw [referenceCompact_eq_lifted_image hh hh1 ha hab]
  exact Subset.antisymm lifted_image_subset_activeReference
    (activeReference_subset_lifted_image hh hh1 ha hab)

/-- Stable domain, given by `{p | 0 < p.1 ∧ (p.2.2, p.2.1) ∈ stableTarget (2 * h)}`. -/
noncomputable def stableDomain (h : ℝ) : Set Slow :=
  {p | 0 < p.1 ∧ (p.2.2, p.2.1) ∈ stableTarget (2 * h)}

/-- Stable Q, given by `(stableInverse (2 * h) (p.2.2, p.2.1)).1`. -/
noncomputable def stableQ (h : ℝ) (p : Slow) : ℝ :=
  (stableInverse (2 * h) (p.2.2, p.2.1)).1

/-- Stable eta, given by `p.2.1 / stableQ h p ^ CoordinateAlgebra.D h`. -/
noncomputable def stableEta (h : ℝ) (p : Slow) : ℝ :=
  p.2.1 / stableQ h p ^ CoordinateAlgebra.D h

/-- Stable X, given by `p.1 ^ 2 / (2 * stableQ h p)`. -/
noncomputable def stableX (h : ℝ) (p : Slow) : ℝ := p.1 ^ 2 / (2 * stableQ h p)

/-- Stable inner, given by `(stableX h p, stableEta h p)`. -/
noncomputable def stableInner (h : ℝ) (p : Slow) : ℝ × ℝ := (stableX h p, stableEta h p)

theorem stableDomain_open (h : ℝ) : IsOpen (stableDomain h) :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((stableTarget_open (2 * h)).preimage (continuous_snd.snd.prodMk continuous_snd.fst))

theorem stableQ_spec {h : ℝ} {p : Slow} (hp : p ∈ stableDomain h) :
    0 < stableQ h p ∧ forwardScalar (2 * h) p.2.1 (stableQ h p) = p.2.2 := by
  have hs := stableInverse_spec hp.2
  refine ⟨hs.1.1, ?_⟩
  have hz : (stableInverse (2 * h) (p.2.2, p.2.1)).2 = p.2.1 := by
    simpa only [forwardMap] using congrArg (fun x : ℝ × ℝ => x.2) hs.2
  have hq := congrArg (fun x : ℝ × ℝ => x.1) hs.2
  simpa only [forwardMap, hz, stableQ] using hq

theorem stableQ_smoothAt {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    {p : Slow} (hp : p ∈ stableDomain h) : ContDiffAt ℝ ∞ (stableQ h) p :=
  ((stableInverse_smoothAt (by linarith) (by linarith) hp.2).comp p
    (contDiffAt_snd.snd.prodMk contDiffAt_snd.fst)).fst

theorem stableInner_smoothAt {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    {p : Slow} (hp : p ∈ stableDomain h) : ContDiffAt ℝ ∞ (stableInner h) p := by
  have hq := stableQ_smoothAt hh hh1 hp
  have hpos := (stableQ_spec hp).1
  exact ((contDiffAt_fst.pow 2).div (contDiffAt_const.mul hq) (by positivity)).prodMk
    (contDiffAt_snd.fst.div (hq.rpow_const_of_ne hpos.ne')
      (Real.rpow_pos_of_pos hpos _).ne')

theorem positiveTime_mem_stableDomain {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hR : 0 < p.1) (hT : 0 < p.2.2) : p ∈ stableDomain h :=
  ⟨hR, positiveTime_mem_stableTarget (by linarith) (by linarith) hT⟩

theorem stableQ_eq_chartQ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) : stableQ h p = SimilarityHomogeneity.chartQ h p := by
  unfold stableQ
  rw [stableInverse_eq_inverseMap (by linarith) (by linarith) hp]
  rfl

theorem stableInner_eq_chartInner {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) : stableInner h p = SimilarityHomogeneity.chartInner h p := by
  apply Prod.ext
  · change p.1 ^ 2 / (2 * stableQ h p) = (p.1 ^ 2 / 2) / SimilarityHomogeneity.chartQ h p
    rw [stableQ_eq_chartQ hh hh1 hp]
    ring
  · change p.2.1 / stableQ h p ^ CoordinateAlgebra.D h =
      p.2.1 / SimilarityHomogeneity.chartQ h p ^ ((1 - 2 * h) / 2)
    rw [stableQ_eq_chartQ hh hh1 hp, show CoordinateAlgebra.D h = (1 - 2 * h) / 2 by
      unfold CoordinateAlgebra.D; ring]

theorem referenceCompact_subset_stableDomain {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) :
    PrimaryRepresentatives.referenceCompact h a b ⊆ stableDomain h := by
  intro p hp
  have hR := PrimaryRepresentatives.referenceCompact_radius_pos hh hh1 ha hab hp
  rw [referenceCompact_eq_activeReference hh hh1 ha hab] at hp
  obtain ⟨_, hT, rho, hrho, he, _⟩ := hp
  have hrhopos : 0 < rho := lt_of_lt_of_le (by norm_num) hrho.1
  refine ⟨hR, ⟨(rho, p.2.1), ⟨hrhopos, ?_⟩, Prod.ext he rfl⟩⟩
  have hm := scalarSlope_lower_of_nonnegative (show 0 ≤ 2 * h by linarith) hrhopos
    (show 0 ≤ forwardScalar (2 * h) p.2.1 rho by rwa [he])
  linarith

theorem stableQ_bounds_reference {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) {p : Slow}
    (hp : p ∈ PrimaryRepresentatives.referenceCompact h a b) :
    stableQ h p ∈ Icc (1 / 2 : ℝ) 2 ∧ stableX h p ∈ Icc a b := by
  rw [referenceCompact_eq_activeReference hh hh1 ha hab] at hp
  obtain ⟨_, hT, rho, hrho, he, hX⟩ := hp
  have hrhopos : 0 < rho := lt_of_lt_of_le (by norm_num) hrho.1
  have hm := scalarSlope_lower_of_nonnegative (show 0 ≤ 2 * h by linarith) hrhopos
    (show 0 ≤ forwardScalar (2 * h) p.2.1 rho by rwa [he])
  have hs : (rho, p.2.1) ∈ stableSource (2 * h) := ⟨hrhopos, by dsimp; linarith⟩
  have ht : forwardMap (2 * h) (rho, p.2.1) = (p.2.2, p.2.1) := Prod.ext he rfl
  have hq := congrArg (fun x : ℝ × ℝ => x.1)
    (stableInverse_forwardMap (by linarith : 0 ≤ 2 * h) (by linarith : 2 * h ≤ 1) hs)
  rw [ht] at hq
  change stableQ h p = rho at hq
  simpa only [stableX, hq] using And.intro hrho hX

theorem stableEta_sq {h : ℝ} {p : Slow} (hp : p ∈ stableDomain h) :
    stableEta h p ^ 2 = p.2.1 ^ 2 * stableQ h p ^ (2 * h) / stableQ h p := by
  have hq := (stableQ_spec hp).1
  unfold stableEta
  rw [div_pow, ← Real.rpow_mul_natCast hq.le,
    show CoordinateAlgebra.D h * (2 : ℕ) = 1 - 2 * h by unfold CoordinateAlgebra.D; ring,
    Real.rpow_sub hq, Real.rpow_one]
  field_simp

theorem stableEta_mem_reference {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) {p : Slow}
    (hp : p ∈ PrimaryRepresentatives.referenceCompact h a b) : stableEta h p ∈ Icc (-1) 1 := by
  have hd := referenceCompact_subset_stableDomain hh hh1 ha hab hp
  have hq := stableQ_spec hd
  have ht := (PrimaryRepresentatives.referenceCompact_subset_box hh hh1 ha hab hp).2.2.1
  have hs : stableEta h p ^ 2 ≤ 1 := by
    rw [stableEta_sq hd]
    apply (div_le_one hq.1).mpr
    dsimp only [forwardScalar] at hq
    linarith [hq.2]
  exact abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hs)

theorem reference_zeroTime_axial_ne {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) {p : Slow}
    (hp : p ∈ PrimaryRepresentatives.referenceCompact h a b) (ht : p.2.2 = 0) : p.2.1 ≠ 0 := by
  have hq := stableQ_spec (referenceCompact_subset_stableDomain hh hh1 ha hab hp)
  intro hz
  simpa [forwardScalar, hz, ht, hq.1.ne'] using hq.2

/-- An open stable-branch neighborhood with fixed radial and similarity
coordinate bounds. Its positive-time part is the physical domain. -/
noncomputable def boundedDomain (h a b : ℝ) : Set Slow :=
  stableDomain h ∩ {p | stableQ h p ∈ Ioo (1 / 4 : ℝ) 4 ∧ stableX h p ∈ Ioo (a / 2) (2 * b)}

theorem boundedDomain_open {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (a b : ℝ) :
    IsOpen (boundedDomain h a b) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hD := (stableDomain_open h).mem_nhds hp.1
  have hq := (stableQ_smoothAt hh hh1 hp.1).continuousAt.eventually
    (isOpen_Ioo.mem_nhds hp.2.1)
  have hX := (stableInner_smoothAt hh hh1 hp.1).fst.continuousAt.eventually
    (isOpen_Ioo.mem_nhds hp.2.2)
  filter_upwards [hD, hq, hX] with x hx hqx hXx
  exact ⟨hx, hqx, hXx⟩

theorem referenceCompact_subset_boundedDomain {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) :
    PrimaryRepresentatives.referenceCompact h a b ⊆ boundedDomain h a b := by
  intro p hp
  have hb := stableQ_bounds_reference hh hh1 ha hab hp
  refine ⟨referenceCompact_subset_stableDomain hh hh1 ha hab hp, ?_, ?_⟩
  · exact ⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩
  · exact ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩

/-- Three-mesh open box; the actual enlarged support uses two meshes. -/
noncomputable def openGrid (n : ℕ) (k : SlotColoring.Grid) : Set Slow :=
  let s := SquaredPartition.nativeSpacing n
  Ioo (s * (k 0 : ℝ) - 3 * s) (s * (k 0 : ℝ) + 3 * s) ×ˢ
    (Ioo (s * (k 1 : ℝ) - 3 * s) (s * (k 1 : ℝ) + 3 * s) ×ˢ
      Ioo (s * (k 2 : ℝ) - 3 * s) (s * (k 2 : ℝ) + 3 * s))

/-- Positive cell, given by `openGrid n k ∩ positiveTime`. -/
noncomputable def positiveCell (n : ℕ) (k : SlotColoring.Grid) : Set Slow :=
  openGrid n k ∩ positiveTime

theorem positiveCell_open (n : ℕ) (k : SlotColoring.Grid) : IsOpen (positiveCell n k) :=
  (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)).inter positiveTime_open

theorem positiveCell_convex (n : ℕ) (k : SlotColoring.Grid) : Convex ℝ (positiveCell n k) :=
  ((convex_Ioo _ _).prod ((convex_Ioo _ _).prod (convex_Ioo _ _))).inter positiveTime_convex

theorem openGrid_subset_gridBox (n : ℕ) (k : SlotColoring.Grid) :
    openGrid n k ⊆ PrimaryRepresentatives.gridBox n k 3 := by
  intro p hp j
  have hj : (SquaredPartition.nativeSpacing n * (k j : ℝ) - 3 * SquaredPartition.nativeSpacing n <
      PrimaryRepresentatives.position p j) ∧
      PrimaryRepresentatives.position p j <
        SquaredPartition.nativeSpacing n * (k j : ℝ) + 3 * SquaredPartition.nativeSpacing n := by
    fin_cases j
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
  exact abs_le.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩

theorem gridBox_two_subset_openGrid {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) :
    PrimaryRepresentatives.gridBox n k 2 ⊆ openGrid n k := by
  intro p hp
  have hs := SquaredPartition.nativeSpacing_pos hn
  have hc (j : Fin 3) : SquaredPartition.nativeSpacing n * (k j : ℝ) - 3 *
      SquaredPartition.nativeSpacing n <
      PrimaryRepresentatives.position p j ∧
      PrimaryRepresentatives.position p j <
        SquaredPartition.nativeSpacing n * (k j : ℝ) + 3 * SquaredPartition.nativeSpacing n := by
    have hj := abs_le.mp (hp j)
    constructor <;> linarith [hj.1, hj.2]
  exact ⟨hc 0, hc 1, hc 2⟩

theorem representative_mem_cell (K : Set Slow) (L : ActiveLabel K) :
    representative K L ∈ positiveCell L.val.1 L.val.2 := by
  have hs := SquaredPartition.nativeSpacing_pos L.property.1
  have hr := PrimaryRepresentatives.nativeMask_tsupport_subset L.property.1 L.val.2
    (representative_mem_tsupport K L)
  refine ⟨gridBox_two_subset_openGrid L.property.1 L.val.2 (fun j => ?_), representative_time_pos K
      L⟩
  exact (hr j).trans (by nlinarith)

theorem enlarged_positive_subset_cell {n : ℕ} (hn : 1 ≤ n) (k : SlotColoring.Grid) :
    PrimaryRepresentatives.gridBox n k 2 ∩ positiveTime ⊆ positiveCell n k :=
  fun _ hp => ⟨gridBox_two_subset_openGrid hn k hp.1, hp.2⟩

theorem mesh_four_tendsto_zero :
    Tendsto (fun n : ℕ => 4 * SquaredPartition.nativeSpacing n) atTop (𝓝 0) := by
  have h := PrimaryRepresentatives.grid_mesh_tendsto_zero.const_mul (4 / 3 : ℝ)
  convert! h using 1
  · funext n
    simp only [SquaredPartition.nativeSpacing]
    ring
  · norm_num

/-- The positive cells eventually lie in any open neighborhood of the
compact reference set. No lower bound for their positive time is used. -/
theorem positiveCell_eventually_subset {K U : Set Slow} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : ℕ, ∀ L : ActiveLabel K, N ≤ L.val.1 → positiveCell L.val.1 L.val.2 ⊆ U := by
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 mesh_four_tendsto_zero).2 r hr)
  refine ⟨N, fun L hL p hp => hsub ?_⟩
  apply Metric.mem_cthickening_of_dist_le p (representative K L) r K (representative_mem K L)
  have h0 := PrimaryRepresentatives.nativeMask_tsupport_subset L.property.1 L.val.2
    (representative_mem_tsupport K L)
  have hd := PrimaryRepresentatives.gridBox_distance (openGrid_subset_gridBox _ _ hp.1) h0
  have hd' : ‖p - representative K L‖ ≤ 4 * SquaredPartition.nativeSpacing L.val.1 := by
    simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using hd
  simpa only [dist_eq_norm] using hd'.trans (hN _ hL).le

/-- Cell bound, given by `max (2 * Real.sqrt b + 1) 3`. -/
noncomputable def cellBound (b : ℝ) : ℝ := max (2 * Real.sqrt b + 1) 3

theorem cellBound_pos (b : ℝ) : 0 < cellBound b :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_right _ _)

theorem baseChart_norm_bound {a b : ℝ} (ha : 0 < a) {p : Slow}
    (hp : p ∈ PrimaryRepresentatives.baseChart a b) :
    Real.sqrt a / 2 ≤ p.1 ∧ ‖p‖ ≤ cellBound b := by
  have hR : 0 < p.1 := (half_pos (Real.sqrt_pos.mpr ha)).trans hp.1.1
  refine ⟨hp.1.1.le, ?_⟩
  change max |p.1| (max |p.2.1| |p.2.2|) ≤ cellBound b
  rw [abs_of_pos hR]
  apply max_le
  · exact hp.1.2.le.trans (le_max_left _ _)
  · apply max_le
    · exact (abs_le.mpr ⟨hp.2.1.1.le, hp.2.1.2.le⟩).trans (le_max_right _ _)
    · apply le_trans _ (le_max_right _ _)
      exact abs_le.mpr ⟨by linarith [hp.2.2.1], hp.2.2.2.le⟩

/-- The same positive representative and a convex open domain work for
every positive-time point in its enlarged two-mesh box. All coordinate
range constants are uniform as time approaches zero. -/
theorem exists_positive_reference_charts {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, ∀ L : ActiveLabel (PrimaryRepresentatives.referenceCompact h a b), N ≤ L.val.1 →
      IsOpen (positiveCell L.val.1 L.val.2) ∧ Convex ℝ (positiveCell L.val.1 L.val.2) ∧
      representative (PrimaryRepresentatives.referenceCompact h a b) L ∈ positiveCell L.val.1
          L.val.2 ∧
      PrimaryRepresentatives.gridBox L.val.1 L.val.2 2 ∩ positiveTime ⊆ positiveCell L.val.1
          L.val.2 ∧
      ∀ p ∈ positiveCell L.val.1 L.val.2,
        0 < p.1 ∧ Real.sqrt a / 2 ≤ p.1 ∧ ‖p‖ ≤ cellBound b ∧ 0 < p.2.2 ∧
          SimilarityHomogeneity.chartQ h p ∈ Ioo (1 / 4 : ℝ) 4 ∧
          SimilarityHomogeneity.chartX h p ∈ Ioo (a / 2) (2 * b) := by
  obtain ⟨N, hN⟩ := positiveCell_eventually_subset
    (PrimaryRepresentatives.referenceCompact_isCompact hh.le hh1 ha hab)
    ((boundedDomain_open hh.le hh1.le a b).inter (PrimaryRepresentatives.baseChart_open a b))
    (show PrimaryRepresentatives.referenceCompact h a b ⊆
        boundedDomain h a b ∩ PrimaryRepresentatives.baseChart a b from fun _ hp =>
      ⟨referenceCompact_subset_boundedDomain hh.le hh1 ha hab hp,
        PrimaryRepresentatives.referenceCompact_subset_baseChart hh.le hh1 ha hab hp⟩)
  refine ⟨N, fun L hL => ⟨positiveCell_open _ _, positiveCell_convex _ _,
    representative_mem_cell _ L, enlarged_positive_subset_cell L.property.1 _, ?_⟩⟩
  intro p hp
  have hb := (hN L hL hp).1
  have hnorm := baseChart_norm_bound ha (hN L hL hp).2
  have hT : 0 < p.2.2 := hp.2
  refine ⟨hb.1.1, hnorm.1, hnorm.2, hT, ?_, ?_⟩
  · have hqb := hb.2.1
    rwa [stableQ_eq_chartQ hh hh1 hT] at hqb
  · have he := congrArg Prod.fst (stableInner_eq_chartInner hh hh1 hT)
    change stableX h p = SimilarityHomogeneity.chartX h p at he
    exact he ▸ hb.2.2

/-! ## Compact bounds use the genuine extension, with physical jet equality -/

theorem stableQ_eventuallyEq_chartQ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) : stableQ h =ᶠ[𝓝 p] SimilarityHomogeneity.chartQ h := by
  filter_upwards [positiveTime_open.mem_nhds hp] with q hq
  exact stableQ_eq_chartQ hh hh1 hq

theorem stableInner_eventuallyEq_chartInner {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) : stableInner h =ᶠ[𝓝 p] SimilarityHomogeneity.chartInner h := by
  filter_upwards [positiveTime_open.mem_nhds hp] with q hq
  exact stableInner_eq_chartInner hh hh1 hq

theorem iteratedFDeriv_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Slow → E} {p : Slow} (he : f =ᶠ[𝓝 p] g) (n : ℕ) :
    iteratedFDeriv ℝ n f p = iteratedFDeriv ℝ n g p := by
  have he' : f =ᶠ[𝓝[univ] p] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using he'.iteratedFDerivWithin_eq he.self_of_nhds n

theorem stableQ_iteratedFDeriv_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) (n : ℕ) :
    iteratedFDeriv ℝ n (stableQ h) p = iteratedFDeriv ℝ n (SimilarityHomogeneity.chartQ h) p :=
  iteratedFDeriv_eq_of_eventuallyEq (stableQ_eventuallyEq_chartQ hh hh1 hp) n

theorem stableInner_iteratedFDeriv_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) (n : ℕ) :
    iteratedFDeriv ℝ n (stableInner h) p = iteratedFDeriv ℝ n (SimilarityHomogeneity.chartInner h)
        p :=
  iteratedFDeriv_eq_of_eventuallyEq (stableInner_eventuallyEq_chartInner hh hh1 hp) n

theorem compact_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Slow} (hK : IsCompact K) {f : Slow → E}
    (hf : ∀ p ∈ K, ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ‖iteratedFDeriv ℝ n f p‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ n f) K := by
    intro p hp
    apply ((hf p hp).iteratedFDeriv_right (m := 0) ?_).continuousAt.continuousWithinAt
    simpa only [zero_add] using
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le
  obtain ⟨C, hC, hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun p hp => hb _ ⟨p, hp, rfl⟩⟩

/-- Stable pullback, given by `stableQ h p ^ exponent * f (stableInner h p)`. -/
noncomputable def stablePullback (h exponent : ℝ) (f : (ℝ × ℝ) → ℝ) (p : Slow) : ℝ :=
  stableQ h p ^ exponent * f (stableInner h p)

/-- Physical pullback, given by `SimilarityHomogeneity.chartQ h p ^ exponent * f
(SimilarityHomogeneity.chartInner h p)`. -/
noncomputable def physicalPullback (h exponent : ℝ) (f : (ℝ × ℝ) → ℝ) (p : Slow) : ℝ :=
  SimilarityHomogeneity.chartQ h p ^ exponent * f (SimilarityHomogeneity.chartInner h p)

theorem stablePullback_smoothAt {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    (exponent : ℝ) {f : (ℝ × ℝ) → ℝ} {p : Slow} (hp : p ∈ stableDomain h)
    (hf : ContDiffAt ℝ ∞ f (stableInner h p)) : ContDiffAt ℝ ∞ (stablePullback h exponent f) p :=
  ((stableQ_smoothAt hh hh1 hp).rpow_const_of_ne (stableQ_spec hp).1.ne').mul
    (hf.comp p (stableInner_smoothAt hh hh1 hp))

theorem stablePullback_eventuallyEq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (exponent : ℝ) (f : (ℝ × ℝ) → ℝ) {p : Slow} (hp : 0 < p.2.2) :
    stablePullback h exponent f =ᶠ[𝓝 p] physicalPullback h exponent f := by
  filter_upwards [stableQ_eventuallyEq_chartQ hh hh1 hp,
    stableInner_eventuallyEq_chartInner hh hh1 hp] with q hq hi
  exact congrArg₂ (fun r x => r ^ exponent * f x) hq hi

/-- Actual physical derivatives have one compact bound down to arbitrarily
small positive time. The boundary values used in the proof are the genuine
stable extension, not derivatives of a totalized inverse at zero time. -/
theorem physicalPullback_uniform_jet_bound {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (exponent : ℝ) {f : (ℝ × ℝ) → ℝ}
    (hf : ∀ x ∈ Icc a b ×ˢ Icc (-1 : ℝ) 1, ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ PrimaryRepresentatives.referenceCompact h a b,
      0 < p.2.2 → ‖iteratedFDeriv ℝ n (physicalPullback h exponent f) p‖ ≤ C := by
  have hs : ∀ p ∈ PrimaryRepresentatives.referenceCompact h a b,
      ContDiffAt ℝ ∞ (stablePullback h exponent f) p := by
    intro p hp
    apply stablePullback_smoothAt hh.le hh1.le exponent
      (referenceCompact_subset_stableDomain hh.le hh1 ha hab hp)
    exact hf _ ⟨(stableQ_bounds_reference hh.le hh1 ha hab hp).2,
      stableEta_mem_reference hh.le hh1 ha hab hp⟩
  obtain ⟨C, hC, hb⟩ := compact_jet_bound
    (PrimaryRepresentatives.referenceCompact_isCompact hh.le hh1 ha hab) hs n
  refine ⟨C, hC, fun p hp hT => ?_⟩
  rw [← iteratedFDeriv_eq_of_eventuallyEq (stablePullback_eventuallyEq hh hh1 exponent f hT) n]
  exact hb p hp

/-! ## Compact reference data are transferred only at positive time -/

theorem shearVector_eq_on_positive {F G Fext Gext : Slow → ℝ}
    (hF : EqOn F Fext positiveTime) (hG : EqOn G Gext positiveTime) :
    EqOn (PhaseEstimates.shearVector F G) (PhaseEstimates.shearVector Fext Gext) positiveTime := by
  intro p hp
  have hf : F =ᶠ[𝓝 p] Fext := by
    filter_upwards [positiveTime_open.mem_nhds hp] with q hq
    exact hF hq
  have hg : G =ᶠ[𝓝 p] Gext := by
    filter_upwards [positiveTime_open.mem_nhds hp] with q hq
    exact hG hq
  have hdf : fderiv ℝ F p = fderiv ℝ Fext p := hf.fderiv_eq
  have hdg : fderiv ℝ G p = fderiv ℝ Gext p := hg.fderiv_eq
  simp only [PhaseEstimates.shearVector, PhaseCalculus.slowR, hdf, hdg]

/-- To closed, given by `⟨L.val, L.property.1, representative K L, representative_mem K L,
representative_mem_tsupport K L⟩`. -/
noncomputable def ActiveLabel.toClosed {K : Set Slow} (L : ActiveLabel K) :
    PrimaryRepresentatives.ActiveLabel K :=
  ⟨L.val, L.property.1, representative K L, representative_mem K L, representative_mem_tsupport K L⟩

@[simp] theorem ActiveLabel.toClosed_val {K : Set Slow} (L : ActiveLabel K) :
    L.toClosed.val = L.val := rfl

/-- The reference functions on the compact closure are explicit extensions.
Only their values at the positive representatives are identified with the
physical data. No equality at zero time is assumed. -/
theorem representative_parameter_bounds {K : Set Slow} (hK : IsCompact K)
    {F Fext : Slow → ℝ} {g gext : Slow → MovingFrameODE.Plane}
    (hF : ContinuousOn Fext K) (hg : ContinuousOn gext K)
    (hR : ∀ p ∈ K, 0 < p.1)
    (hc : ∀ p ∈ K, PrimaryRepresentatives.ReferenceCone (Fext p) (gext p))
    (hFeq : EqOn F Fext (positivePart K)) (hgeq : EqOn g gext (positivePart K)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ L : ActiveLabel K,
      PrimaryRepresentatives.ParameterBounds M (representative K L).1
        (F (representative K L)) (g (representative K L)) := by
  obtain ⟨M, hM, hb⟩ := PrimaryRepresentatives.compact_parameter_bounds hK hF hg hR hc
  refine ⟨M, hM, fun L => ?_⟩
  have hr : representative K L ∈ positivePart K :=
    ⟨representative_mem K L, representative_time_pos K L⟩
  rw [hFeq hr, hgeq hr]
  exact hb _ hr.1

/-- The target-direction margin is transferred from continuous extended
reference data to the actual positive-time target and representative. -/
theorem representative_target_margin {K : Set Slow} (hK : IsCompact K)
    {F Fext : Slow → ℝ} {g gext T Text : Slow → MovingFrameODE.Plane}
    (hF : ContinuousOn Fext K) (hg : ContinuousOn gext K) (hT : ContinuousOn Text K)
    (hc : ∀ p ∈ K, PrimaryRepresentatives.ReferenceCone (Fext p) (gext p))
    (ht : ∀ p ∈ K, PrimaryRepresentatives.TargetCone (Fext p) (gext p) (Text p))
    (hFeq : EqOn F Fext (positivePart K)) (hgeq : EqOn g gext (positivePart K))
    (hTeq : EqOn T Text (positivePart K)) :
    ∃ u eta : ℝ, 0 < u ∧ 0 < eta ∧ ∃ N : ℕ,
      ∀ L : ActiveLabel K, N ≤ L.val.1 → ∀ p ∈ positivePart K,
        p ∈ PrimaryRepresentatives.gridBox L.val.1 L.val.2 2 →
          ⟪T p, PrimaryRepresentatives.normalDirection (g (representative K L))⟫_ℝ ≤ -eta ∧
          |PrimaryRepresentatives.c0 (F (representative K L)) (g (representative K L)) *
            ⟪T p, PrimaryRepresentatives.transverseDirection (g (representative K L))⟫_ℝ /
            ⟪T p, PrimaryRepresentatives.normalDirection (g (representative K L))⟫_ℝ| + eta ≤
              PrimaryRepresentatives.slopeRatio u := by
  obtain ⟨u, eta, delta, hu, heta, hdelta, hb⟩ :=
    PrimaryRepresentatives.compact_mixed_target_margin hK hF hg hT hc ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.1 PrimaryRepresentatives.grid_mesh_tendsto_zero).2 delta hdelta)
  refine ⟨u, eta, hu, heta, N, fun L hL p hp hbox => ?_⟩
  have hr : representative K L ∈ positivePart K :=
    ⟨representative_mem K L, representative_time_pos K L⟩
  have hd : dist p (representative K L) < delta := by
    simpa only [dist_eq_norm] using (representative_enlarged_distance K L hbox).trans_lt (hN _ hL)
  have hm := hb _ hr.1 p hp.1 hd
  rwa [← hFeq hr, ← hgeq hr, ← hTeq hp] at hm

end NavierStokes.PositiveRepresentatives
