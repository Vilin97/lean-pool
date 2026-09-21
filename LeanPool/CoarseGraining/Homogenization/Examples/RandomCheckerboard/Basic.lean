/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.EllipticSupport
import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Restriction
import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Bernoulli checkerboard: the honest carrier-valued sample map

This file constructs the scalar Bernoulli checkerboard as a *carrier-valued*
random field.  The random medium is indexed by `ℤ^d`; each open unit cube
centered at an integer lattice point receives conductance `lam` or `Lam`, while
cell walls are assigned the deterministic value `lam`.  The deterministic wall
convention keeps stationarity and signed-permutation invariance exact for
pointwise coefficient fields.

Following the carrier redesign, the sample map `checkerRegField lam Lam` lands
in the honest-fields carrier `RegCoeffField d`: every realization is entrywise
Borel measurable (piecewise-constant on the Borel cell decomposition) and
locally integrable (bounded by `max |lam| |Lam|`).  The sample map is
**genuinely measurable** for the canonical carrier σ-algebra
`pointwiseSigmaR ⊔ entryTestSigmaR`: the pointwise lane is the coin evaluation
at the cell of the point, and the entry-test lane is a *finite-cell
decomposition* — the entry integral against a compactly supported probe is an
affine function of the finitely many coins whose cells meet the probe's
support.  The same decomposition, restricted through `restrictReg`, gives
measurability into the restriction σ-algebra `RestrictionSigmaR U` from the
coins of the cells meeting `U`, the input for unit-range dependence of the
checkerboard law (`CarrierLaw.lean`).

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization
namespace Examples
namespace RandomCheckerboard

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Integer lattice indices for checkerboard cells. -/
abbrev Lattice (d : ℕ) :=
  Fin d → ℤ

/-- A checkerboard environment: one coin at each lattice cell. -/
abbrev Sample (d : ℕ) :=
  Lattice d → Bool

/-- The open unit cube centered at `z`. -/
def openUnitCell {d : ℕ} (z : Lattice d) : Set (Vec d) :=
  {x | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)}

/-- Open checkerboard cells are Borel-measurable. -/
theorem measurableSet_openUnitCell {d : ℕ} (z : Lattice d) :
    MeasurableSet (openUnitCell z : Set (Vec d)) := by
  classical
  have hopen : IsOpen (openUnitCell z : Set (Vec d)) := by
    unfold openUnitCell
    have hset :
        {x : Vec d | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)} =
          ⋂ i : Fin d, {x : Vec d | |x i - (z i : ℝ)| < (1 / 2 : ℝ)} := by
      ext x
      simp
    rw [hset]
    refine isOpen_iInter_of_finite fun i : Fin d => ?_
    have hleft : Continuous fun x : Vec d => |x i - (z i : ℝ)| :=
      ((continuous_apply i).sub continuous_const).abs
    have hright : Continuous fun _ : Vec d => (1 / 2 : ℝ) :=
      continuous_const
    exact isOpen_lt hleft hright
  exact hopen.measurableSet

/-- The set of lattice cells whose open interiors meet `U`. -/
def cellsMeeting {d : ℕ} (U : Set (Vec d)) : Set (Lattice d) :=
  {z | ∃ x ∈ U, x ∈ openUnitCell z}

/-- Monotonicity of `cellsMeeting` under set inclusion. -/
theorem cellsMeeting_mono {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V) :
    cellsMeeting U ⊆ cellsMeeting V := by
  rintro z ⟨x, hxU, hxz⟩
  exact ⟨x, hUV hxU, hxz⟩

/-- A point belongs to at most one open unit cell. -/
theorem openUnitCell_unique {d : ℕ} {x : Vec d} {z w : Lattice d}
    (hz : x ∈ openUnitCell z) (hw : x ∈ openUnitCell w) :
    z = w := by
  funext i
  by_contra hne
  have hzw_int : (1 : ℤ) ≤ |z i - w i| :=
    Int.one_le_abs (sub_ne_zero.mpr hne)
  have hzw : (1 : ℝ) ≤ |(z i : ℝ) - (w i : ℝ)| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast hzw_int
  have hz_i := hz i
  have hw_i := hw i
  have hsplit :
      (z i : ℝ) - (w i : ℝ) =
        - (x i - (z i : ℝ)) + (x i - (w i : ℝ)) := by ring
  have htriangle :
      |(z i : ℝ) - (w i : ℝ)| <
        (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
    calc
      |(z i : ℝ) - (w i : ℝ)|
          = |- (x i - (z i : ℝ)) + (x i - (w i : ℝ))| := by rw [hsplit]
      _ ≤ |-(x i - (z i : ℝ))| + |x i - (w i : ℝ)| := abs_add_le _ _
      _ = |x i - (z i : ℝ)| + |x i - (w i : ℝ)| := by rw [abs_neg]
      _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hz_i hw_i
  norm_num at htriangle
  linarith

/-- Bounded observation sets meet only finitely many open checkerboard cells. -/
theorem finite_cellsMeeting_of_isBounded {d : ℕ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) :
    (cellsMeeting U).Finite := by
  classical
  rcases Bornology.IsBounded.isBoundedDomain hU with ⟨R, hRpos, hR⟩
  let N : ℤ := ⌈R + 1⌉
  have hfiniteBox :
      ({z : Lattice d | ∀ i : Fin d, z i ∈ Set.Icc (-N) N}).Finite := by
    simpa using
      (Set.Finite.pi' (fun _ : Fin d => (Set.finite_Icc (-N) N)))
  refine hfiniteBox.subset ?_
  intro z hz i
  rcases hz with ⟨x, hxU, hxz⟩
  have hxR : |x i| ≤ R := hR x hxU i
  have hxz_i : |x i - (z i : ℝ)| < (1 / 2 : ℝ) := hxz i
  have hz_abs : |(z i : ℝ)| ≤ R + 1 := by
    calc
      |(z i : ℝ)|
          = |x i - (x i - (z i : ℝ))| := by congr 1; ring
      _ ≤ |x i| + |x i - (z i : ℝ)| := by
            have htri := abs_sub_le (x i) 0 (x i - (z i : ℝ))
            simpa [abs_sub_comm (z i : ℝ) (x i)] using htri
      _ ≤ R + 1 := by linarith
  have hceil : R + 1 ≤ (N : ℝ) := by
    simpa [N] using (Int.le_ceil (R + 1))
  have hleN_real : (z i : ℝ) ≤ (N : ℝ) :=
    (le_abs_self (z i : ℝ)).trans (hz_abs.trans hceil)
  have hnegN_real : (-(N : ℤ) : ℝ) ≤ (z i : ℝ) := by
    have hneg : -(R + 1) ≤ (z i : ℝ) := by
      have hnegabs : -|(z i : ℝ)| ≤ (z i : ℝ) := by
        have h := le_abs_self (-(z i : ℝ))
        rw [abs_neg] at h
        linarith
      linarith
    have hN : (-(N : ℤ) : ℝ) ≤ -(R + 1) := by
      norm_num [Int.cast_neg]
      linarith
    exact hN.trans hneg
  constructor
  · exact_mod_cast hnegN_real
  · exact_mod_cast hleN_real

/-- Conductance value associated with a coin.  `true` is heads and gives
`lam`; `false` gives `Lam`. -/
def coinConductance (lam Lam : ℝ) (b : Bool) : ℝ :=
  if b then lam else Lam

/-- A deterministic representative on walls and a random scalar value in the
unique open unit cell containing the point. -/
def scalarAt (lam Lam : ℝ) {d : ℕ} (ω : Sample d) (x : Vec d) : ℝ :=
  by
    classical
    exact
      if h : ∃ z : Lattice d, x ∈ openUnitCell z then
        coinConductance lam Lam (ω (Classical.choose h))
      else
        lam

/-- The scalar Bernoulli checkerboard coefficient field (raw sample). -/
def coeffField (lam Lam : ℝ) {d : ℕ} (ω : Sample d) : CoeffField d :=
  fun x => scalarMatrix (d := d) (scalarAt lam Lam ω x)

theorem scalarAt_of_mem_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d} {z : Lattice d}
    (hz : x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = coinConductance lam Lam (ω z) := by
  classical
  unfold scalarAt
  let h : ∃ w : Lattice d, x ∈ openUnitCell w := ⟨z, hz⟩
  rw [dif_pos h]
  congr 1
  exact congrArg ω (openUnitCell_unique (Classical.choose_spec h) hz)

theorem scalarAt_of_not_mem_any_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d}
    (hx : ¬ ∃ z : Lattice d, x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = lam := by
  classical
  unfold scalarAt
  rw [dif_neg hx]

/-- The region where the checkerboard scalar takes the upper value `Lam`. -/
def upperConductanceRegion {d : ℕ} (ω : Sample d) : Set (Vec d) :=
  ⋃ z : {z : Lattice d // ω z = false}, openUnitCell z.1

theorem measurableSet_upperConductanceRegion {d : ℕ} (ω : Sample d) :
    MeasurableSet (upperConductanceRegion ω : Set (Vec d)) := by
  classical
  unfold upperConductanceRegion
  exact MeasurableSet.iUnion fun z => measurableSet_openUnitCell z.1

theorem scalarAt_eq_if_upperConductanceRegion {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d} :
    scalarAt lam Lam ω x =
      if x ∈ upperConductanceRegion ω then Lam else lam := by
  classical
  by_cases hxUpper : x ∈ upperConductanceRegion ω
  · rcases Set.mem_iUnion.mp hxUpper with ⟨z, hxz⟩
    have hcell : x ∈ openUnitCell z.1 := hxz
    have hz : ω z.1 = false := z.2
    simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hcell,
      coinConductance, hz, hxUpper]
  · by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
    · let z : Lattice d := Classical.choose hx
      have hzcell : x ∈ openUnitCell z := Classical.choose_spec hx
      have hztrue : ω z = true := by
        cases hωz : ω z
        · exact False.elim (hxUpper (Set.mem_iUnion.2 ⟨⟨z, hωz⟩, hzcell⟩))
        · rfl
      simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hzcell,
        coinConductance, hztrue, hxUpper]
    · simp [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hx,
        hxUpper]

/-- For each sample, the scalar checkerboard representative is Borel-measurable
in space. -/
theorem measurable_scalarAt_spatial {d : ℕ} {lam Lam : ℝ} (ω : Sample d) :
    Measurable (fun x : Vec d => scalarAt lam Lam ω x) := by
  classical
  have hpiece :
      Measurable
        ((upperConductanceRegion ω).piecewise
          (fun _ : Vec d => Lam) (fun _ : Vec d => lam)) :=
    Measurable.piecewise (measurableSet_upperConductanceRegion ω)
      measurable_const measurable_const
  convert hpiece using 1
  funext x
  simp [Set.piecewise, scalarAt_eq_if_upperConductanceRegion]

theorem measurable_coeffField_spatial {d : ℕ} {lam Lam : ℝ} (ω : Sample d) :
    Measurable (fun x : Vec d => coeffField lam Lam ω x) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  by_cases hij : i = j
  · subst j
    simpa [coeffField, scalarMatrix] using measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
  · simp [coeffField, scalarMatrix, hij]

theorem scalarAt_eq_lam_or_Lam {d : ℕ} {lam Lam : ℝ} (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω x = lam ∨ scalarAt lam Lam ω x = Lam := by
  rw [scalarAt_eq_if_upperConductanceRegion]
  by_cases hx : x ∈ upperConductanceRegion ω <;> simp [hx]

theorem abs_scalarAt_le {d : ℕ} {lam Lam : ℝ} (ω : Sample d) (x : Vec d) :
    |scalarAt lam Lam ω x| ≤ max |lam| |Lam| := by
  rcases scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω x with h | h
  · rw [h]; exact le_max_left _ _
  · rw [h]; exact le_max_right _ _

theorem scalarMatrix_isEllipticMatrix_between {d : ℕ} {lam Lam sigma : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (hsigma : sigma = lam ∨ sigma = Lam) :
    IsEllipticMatrix lam Lam (scalarMatrix (d := d) sigma) := by
  rcases hsigma with hsigma | hsigma
  · subst sigma
    exact (isEllipticMatrix_scalarMatrix (d := d) hlam).mono hlam le_rfl hle
  · subst sigma
    have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
    exact (isEllipticMatrix_scalarMatrix (d := d) hLam).mono hlam hle le_rfl

/-! ## The sample-side σ-algebras and the Bernoulli product law -/
/-- The sigma-algebra generated by one lattice coin. -/
def sampleCoordinateSigma {d : ℕ} (z : Lattice d) : MeasurableSpace (Sample d) :=
  MeasurableSpace.comap (fun ω : Sample d => ω z) inferInstance
/-- The sigma-algebra generated by all coins in a set of lattice cells. -/
def sampleCellsSigma {d : ℕ} (S : Set (Lattice d)) : MeasurableSpace (Sample d) :=
  ⨆ z : Lattice d, ⨆ _ : z ∈ S, sampleCoordinateSigma z

theorem measurable_eval_sampleCellsSigma {d : ℕ} {S : Set (Lattice d)}
    {z : Lattice d} (hz : z ∈ S) :
    @Measurable (Sample d) Bool (sampleCellsSigma S) inferInstance (fun ω => ω z) := by
  let : MeasurableSpace (Sample d) := sampleCellsSigma S
  change Measurable (fun ω : Sample d => ω z)
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)

/-- Every cells σ-algebra is coarser than the ambient product σ-algebra. -/
theorem sampleCellsSigma_le {d : ℕ} (S : Set (Lattice d)) :
    sampleCellsSigma S ≤ (inferInstance : MeasurableSpace (Sample d)) := by
  refine iSup_le fun z => iSup_le fun _ => ?_
  exact (measurable_pi_apply z).comap_le

/-- The Bernoulli measure on a single coin. -/
def coinMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false ⟨(p : ℝ), NNReal.coe_nonneg p, by exact_mod_cast hp⟩

instance instIsProbabilityMeasure_coinMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (coinMeasure p hp) := by
  unfold coinMeasure
  infer_instance

/-- The product Bernoulli law on all lattice coins. -/
def sampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Sample d) :=
  Measure.infinitePi (fun _ : Lattice d => coinMeasure p hp)

instance instIsProbabilityMeasure_sampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (sampleMeasure d p hp) := by
  rw [sampleMeasure]
  infer_instance

/-! ## The carrier-valued sample map -/

/-- **The checkerboard realization as a carrier element.**  Entrywise Borel
measurability is the shipped spatial measurability of the piecewise-constant
sample; local integrability holds because every entry is bounded by
`max |lam| |Lam|` (`RegCoeffField.locallyIntegrable_of_bounded_measurable`).
This discharges gate obligation (i) of the carrier design gate. -/
def checkerRegField (lam Lam : ℝ) {d : ℕ} (ω : Sample d) : RegCoeffField d where
  toFun := coeffField lam Lam ω
  entry_measurable := fun i j => by
    by_cases hij : i = j
    · subst j
      simpa [coeffField, scalarMatrix] using
        measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
    · simp [coeffField, scalarMatrix, hij]
  entry_locInt := fun i j => by
    by_cases hij : i = j
    · subst j
      have hmeas : Measurable (fun x : Vec d => coeffField lam Lam ω x i i) := by
        simpa [coeffField, scalarMatrix] using
          measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
      refine RegCoeffField.locallyIntegrable_of_bounded_measurable hmeas
        (C := max |lam| |Lam|) fun x => ?_
      simpa [coeffField, scalarMatrix] using
        abs_scalarAt_le (lam := lam) (Lam := Lam) ω x
    · have hzero : (fun x : Vec d => coeffField lam Lam ω x i j)
          = fun _ : Vec d => (0 : ℝ) := by
        funext x
        simp [coeffField, scalarMatrix, hij]
      rw [hzero]
      exact locallyIntegrable_const (0 : ℝ)

@[simp] theorem checkerRegField_toFun {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    (checkerRegField lam Lam ω).toFun = coeffField lam Lam ω := rfl

@[simp] theorem checkerRegField_apply {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) :
    checkerRegField lam Lam ω x = coeffField lam Lam ω x := rfl

/-- Every checkerboard realization is spatially a.e. (in fact everywhere)
`(lam, Lam)`-elliptic on any measurable observation set — the regularity
conjuncts are free by the carrier type. -/
theorem checkerRegField_isAEEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} (hU : MeasurableSet U) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ω : Sample d) :
    IsAEEllipticFieldOn lam Lam U (checkerRegField lam Lam ω).toFun := by
  rw [isAEEllipticFieldOn_carrier_iff hU lam Lam]
  exact Filter.Eventually.of_forall fun x =>
    scalarMatrix_isEllipticMatrix_between (d := d) hlam hle
      (scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω x)

/-! ## Genuine measurability of the sample map (entry-test lane)

The entry integral of a checkerboard sample against a compactly supported probe
is an affine function of the finitely many coins whose cells meet the probe's
support: the **finite-cell decomposition**.  This is the honest carrier
replacement of the raw generator-trick route, and discharges gate obligation (ii)
of the carrier design gate. -/

/-- Probes are integrable (bounded, measurable, compactly supported). -/
private theorem integrable_of_isProbeR {d : ℕ} {ψ : Vec d → ℝ} (hψ : IsProbeR ψ) :
    Integrable ψ (volume : Measure (Vec d)) := by
  set K := tsupport ψ with hK
  have hKcpt : IsCompact K := hψ.hasCompactSupport
  obtain ⟨C, hC⟩ := hψ.bounded
  have hOn : IntegrableOn ψ K volume := by
    refine Measure.integrableOn_of_bounded hKcpt.measure_lt_top.ne
      hψ.measurable.aestronglyMeasurable (M := C) ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hC x
  have hself : K.indicator ψ = ψ :=
    Set.indicator_eq_self.2 (subset_tsupport ψ)
  rw [← hself, integrable_indicator_iff hKcpt.measurableSet]
  exact hOn

/-- **The pointwise finite-cell decomposition** of the scalar sample against a
probe: over any finset `F` containing all cells meeting the probe's support,
`scalarAt ω · ψ = lam ψ + ∑_{z ∈ F} (coin(ω z) − lam) · 1_{cell z} ψ`. -/
private theorem scalarAt_mul_probe_decomp {d : ℕ} (lam Lam : ℝ)
    {ψ : Vec d → ℝ} {F : Finset (Lattice d)}
    (hF : cellsMeeting (Function.support ψ) ⊆ (F : Set (Lattice d)))
    (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω x * ψ x =
      lam * ψ x + ∑ z ∈ F, (coinConductance lam Lam (ω z) - lam) *
        Set.indicator (openUnitCell z) ψ x := by
  classical
  by_cases hψx : ψ x = 0
  · simp [hψx, Set.indicator_apply]
  · have hx : x ∈ Function.support ψ := hψx
    by_cases hcell : ∃ z : Lattice d, x ∈ openUnitCell z
    · obtain ⟨z0, hz0⟩ := hcell
      have hz0F : z0 ∈ F := hF ⟨x, hx, hz0⟩
      rw [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hz0,
        Finset.sum_eq_single z0]
      · rw [Set.indicator_of_mem hz0]
        ring
      · intro z _ hzne
        have hxz : x ∉ openUnitCell z := fun hxz =>
          hzne (openUnitCell_unique hxz hz0)
        rw [Set.indicator_of_notMem hxz, mul_zero]
      · intro habs
        exact absurd hz0F habs
    · rw [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam)
        (ω := ω) hcell, Finset.sum_eq_zero, add_zero]
      intro z _
      have hxz : x ∉ openUnitCell z := fun hxz => hcell ⟨z, hxz⟩
      rw [Set.indicator_of_notMem hxz, mul_zero]

/-- **The integrated finite-cell decomposition**: the diagonal entry test of a
checkerboard sample is an affine function of the coins in any finset containing
the cells meeting the probe's support. -/
theorem entryTestR_checkerRegField_diag {d : ℕ} (lam Lam : ℝ) (i : Fin d)
    {ψ : Vec d → ℝ} (hψ : IsProbeR ψ) {F : Finset (Lattice d)}
    (hF : cellsMeeting (Function.support ψ) ⊆ (F : Set (Lattice d)))
    (ω : Sample d) :
    entryTestR i i ψ (checkerRegField lam Lam ω) =
      lam * ∫ x, ψ x ∂volume +
        ∑ z ∈ F, (coinConductance lam Lam (ω z) - lam) *
          ∫ x, Set.indicator (openUnitCell z) ψ x ∂volume := by
  classical
  have hint_ψ : Integrable (fun x => lam * ψ x) volume :=
    (integrable_of_isProbeR hψ).const_mul lam
  have hint_z : ∀ z ∈ F, Integrable
      (fun x => (coinConductance lam Lam (ω z) - lam) *
        Set.indicator (openUnitCell z) ψ x) volume := fun z _ =>
    (integrable_of_isProbeR (hψ.indicator (measurableSet_openUnitCell z))).const_mul _
  have hint_sum : Integrable
      (fun x => ∑ z ∈ F, (coinConductance lam Lam (ω z) - lam) *
        Set.indicator (openUnitCell z) ψ x) volume :=
    integrable_finsetSum F hint_z
  calc
    entryTestR i i ψ (checkerRegField lam Lam ω)
        = ∫ x, scalarAt lam Lam ω x * ψ x ∂volume := by
          unfold entryTestR
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [coeffField, scalarMatrix]
    _ = ∫ x, (lam * ψ x + ∑ z ∈ F, (coinConductance lam Lam (ω z) - lam) *
          Set.indicator (openUnitCell z) ψ x) ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact scalarAt_mul_probe_decomp lam Lam hF ω x
    _ = lam * ∫ x, ψ x ∂volume +
          ∑ z ∈ F, (coinConductance lam Lam (ω z) - lam) *
            ∫ x, Set.indicator (openUnitCell z) ψ x ∂volume := by
          rw [integral_add hint_ψ hint_sum, integral_const_mul,
            integral_finsetSum F hint_z]
          congr 1
          exact Finset.sum_congr rfl fun z _ => integral_const_mul _ _

/-- **Master entry-test measurability**: the entry test of the checkerboard
sample map against a probe is measurable for any σ-algebra on the sample space
that measures the coins of the cells meeting the probe's support. -/
theorem measurable_entryTestR_checkerRegField {d : ℕ} (lam Lam : ℝ)
    {m : MeasurableSpace (Sample d)} (i j : Fin d) {ψ : Vec d → ℝ}
    (hψ : IsProbeR ψ)
    (hcoin : ∀ z ∈ cellsMeeting (Function.support ψ),
      @Measurable (Sample d) Bool m inferInstance (fun ω => ω z)) :
    @Measurable (Sample d) ℝ m inferInstance
      (fun ω => entryTestR i j ψ (checkerRegField lam Lam ω)) := by
  classical
  by_cases hij : i = j
  · subst j
    have hbdd : Bornology.IsBounded (Function.support ψ) :=
      hψ.hasCompactSupport.isBounded.subset (subset_tsupport ψ)
    have hfin := finite_cellsMeeting_of_isBounded (d := d) hbdd
    set F : Finset (Lattice d) := hfin.toFinset with hFdef
    have hF : cellsMeeting (Function.support ψ) ⊆ (F : Set (Lattice d)) :=
      fun z hz => hfin.mem_toFinset.2 hz
    have hEq : (fun ω : Sample d => entryTestR i i ψ (checkerRegField lam Lam ω))
        = fun ω => lam * ∫ x, ψ x ∂volume +
            ∑ z ∈ F, (coinConductance lam Lam (ω z) - lam) *
              ∫ x, Set.indicator (openUnitCell z) ψ x ∂volume :=
      funext fun ω => entryTestR_checkerRegField_diag lam Lam i hψ hF ω
    rw [hEq]
    refine Measurable.add measurable_const ?_
    refine Finset.measurable_sum F fun z hz => ?_
    have hzS : z ∈ cellsMeeting (Function.support ψ) := hfin.mem_toFinset.1 hz
    have hcz : @Measurable (Sample d) ℝ m inferInstance
        (fun ω => coinConductance lam Lam (ω z)) :=
      (measurable_of_finite (coinConductance lam Lam)).comp (hcoin z hzS)
    exact (hcz.sub measurable_const).mul_const _
  · have hEq : (fun ω : Sample d => entryTestR i j ψ (checkerRegField lam Lam ω))
        = fun _ => (0 : ℝ) := by
      funext ω
      unfold entryTestR
      have hzero : ∀ x : Vec d, checkerRegField lam Lam ω x i j * ψ x = 0 := by
        intro x
        simp [coeffField, scalarMatrix, hij]
      simp only [hzero, integral_zero]
    rw [hEq]
    exact measurable_const

/-- **Master pointwise-lane measurability**: evaluation of the checkerboard
sample map at a spatial point is measurable for any σ-algebra measuring the
coin of the cell of that point (walls are deterministic). -/
theorem measurable_apply_checkerRegField {d : ℕ} (lam Lam : ℝ)
    {m : MeasurableSpace (Sample d)} (x : Vec d) (i j : Fin d)
    (hcoin : ∀ z : Lattice d, x ∈ openUnitCell z →
      @Measurable (Sample d) Bool m inferInstance (fun ω => ω z)) :
    @Measurable (Sample d) ℝ m inferInstance
      (fun ω => checkerRegField lam Lam ω x i j) := by
  classical
  by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
  · let z : Lattice d := Classical.choose hx
    have hzcell : x ∈ openUnitCell z := Classical.choose_spec hx
    have hcz : @Measurable (Sample d) ℝ m inferInstance
        (fun ω => coinConductance lam Lam (ω z)) :=
      (measurable_of_finite (coinConductance lam Lam)).comp (hcoin z hzcell)
    by_cases hij : i = j
    · subst j
      simpa [coeffField, scalarAt, hx, scalarMatrix] using hcz
    · simp [coeffField, scalarAt, hx, scalarMatrix, hij]
  · by_cases hij : i = j
    · subst j
      simp [coeffField, scalarAt, hx, scalarMatrix]
    · simp [coeffField, scalarAt, hx, scalarMatrix, hij]

/-- **The checkerboard sample map is genuinely measurable into the carrier**
(canonical σ-algebra, both lanes).  Gate obligation (ii) discharged: the entry-test
lane is the finite-cell decomposition, the pointwise lane the coin evaluation. -/
theorem measurable_checkerRegField {d : ℕ} (lam Lam : ℝ) :
    Measurable (checkerRegField lam Lam (d := d)) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_apply_checkerRegField lam Lam y i j
      (fun z _ => measurable_pi_apply z)
  · intro i j φ hφ
    exact measurable_entryTestR_checkerRegField lam Lam i j hφ
      (fun z _ => measurable_pi_apply z)

/-- The `U`-restricted checkerboard sample map is measurable into the carrier
from the σ-algebra of the coins whose cells meet `U`. -/
theorem measurable_restrictReg_checkerRegField_sampleCellsSigma {d : ℕ}
    (lam Lam : ℝ) (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable (Sample d) (RegCoeffField d)
      (sampleCellsSigma (cellsMeeting U)) inferInstance
      (fun ω => restrictReg U hU (checkerRegField lam Lam ω)) := by
  classical
  let : MeasurableSpace (Sample d) := sampleCellsSigma (cellsMeeting U)
  change Measurable (fun ω : Sample d => restrictReg U hU (checkerRegField lam Lam ω))
  refine measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    have hEq : (fun ω : Sample d => restrictReg U hU (checkerRegField lam Lam ω) y i j)
        = fun ω => Set.indicator U (fun y' => checkerRegField lam Lam ω y' i j) y :=
      funext fun ω => restrictReg_apply_entry U hU (checkerRegField lam Lam ω) y i j
    rw [hEq]
    by_cases hyU : y ∈ U
    · simp only [Set.indicator_of_mem hyU]
      refine measurable_apply_checkerRegField lam Lam y i j fun z hz => ?_
      exact measurable_eval_sampleCellsSigma (S := cellsMeeting U) ⟨y, hyU, hz⟩
    · simp only [Set.indicator_of_notMem hyU]
      exact measurable_const
  · intro i j φ hφ
    have hEq : (fun ω : Sample d =>
          entryTestR i j φ (restrictReg U hU (checkerRegField lam Lam ω)))
        = fun ω => entryTestR i j (Set.indicator U φ) (checkerRegField lam Lam ω) :=
      funext fun ω => entryTestR_restrictReg i j φ U hU (checkerRegField lam Lam ω)
    rw [hEq]
    refine measurable_entryTestR_checkerRegField lam Lam i j (hφ.indicator hU)
      fun z hz => ?_
    have hsupp : Function.support (Set.indicator U φ) ⊆ U := by
      intro x hxs
      by_contra hxU
      exact hxs (Set.indicator_of_notMem hxU φ)
    exact measurable_eval_sampleCellsSigma (S := cellsMeeting U)
      (cellsMeeting_mono hsupp hz)

/-- The checkerboard sample map is measurable into the carrier restriction
σ-algebra `RestrictionSigmaR U` from the coins whose cells meet `U` — the
unit-range dependence input. -/
theorem measurable_checkerRegField_restrictionSigmaR {d : ℕ}
    (lam Lam : ℝ) (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable (Sample d) (RegCoeffField d)
      (sampleCellsSigma (cellsMeeting U)) (RestrictionSigmaR U hU)
      (checkerRegField lam Lam) := by
  let : MeasurableSpace (Sample d) := sampleCellsSigma (cellsMeeting U)
  rw [measurable_iff_comap_le, RestrictionSigmaR, MeasurableSpace.comap_comp]
  exact (measurable_restrictReg_checkerRegField_sampleCellsSigma
    lam Lam U hU).comap_le

/-! ## Sample-space symmetries and carrier commutations -/

/-- Translate lattice indices by an integer vector. -/
def translateLattice {d : ℕ} (z : Lattice d) (w : Lattice d) : Lattice d :=
  fun i => w i + z i

/-- Translation of lattice indices is a bijection. -/
def translateLatticeEquiv {d : ℕ} (z : Lattice d) : Lattice d ≃ Lattice d where
  toFun := translateLattice z
  invFun := fun w i => w i - z i
  left_inv := by
    intro w
    funext i
    simp [translateLattice]
  right_inv := by
    intro w
    funext i
    simp [translateLattice]

/-- Shift a sample so that cell `w` reads the old coin at `w + z`. -/
def shiftSample {d : ℕ} (z : Lattice d) (ω : Sample d) : Sample d :=
  fun w => ω (translateLattice z w)

theorem shiftSample_eq_piCongrLeft {d : ℕ} (z : Lattice d) :
    shiftSample z =
      (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool)
        (translateLatticeEquiv z).symm) := by
  funext ω w
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (e := (translateLatticeEquiv z).symm)
      (β := fun _ : Lattice d => Bool) ω ((translateLatticeEquiv z) w)
  simpa [shiftSample] using! h.symm

theorem measurable_shiftSample {d : ℕ} (z : Lattice d) :
    Measurable (shiftSample z : Sample d → Sample d) := by
  rw [shiftSample_eq_piCongrLeft]
  exact (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool)
    (translateLatticeEquiv z).symm).measurable

theorem sampleMeasure_map_shiftSample {d : ℕ} (z : Lattice d)
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (shiftSample z) (sampleMeasure d p hp) = sampleMeasure d p hp := by
  rw [shiftSample_eq_piCongrLeft]
  have h :=
    Measure.infinitePi_map_piCongrLeft
      (X := fun _ : Lattice d => Bool)
      (μ := fun _ : Lattice d => coinMeasure p hp)
      (e := (translateLatticeEquiv z).symm)
  simpa [sampleMeasure] using h

theorem openUnitCell_translateLattice_iff {d : ℕ} (z w : Lattice d) (x : Vec d) :
    (fun i : Fin d => x i + (z i : ℝ)) ∈ openUnitCell (translateLattice z w) ↔
      x ∈ openUnitCell w := by
  constructor
  · intro hx i
    have hi := hx i
    simpa [translateLattice] using hi
  · intro hx i
    have hi := hx i
    simpa [translateLattice] using hi

theorem scalarAt_translate_intVec {d : ℕ} {lam Lam : ℝ}
    (z : Lattice d) (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω (fun i : Fin d => x i + (z i : ℝ)) =
      scalarAt lam Lam (shiftSample z ω) x := by
  classical
  by_cases hx : ∃ w : Lattice d, x ∈ openUnitCell w
  · let w : Lattice d := Classical.choose hx
    have hxw : x ∈ openUnitCell w := Classical.choose_spec hx
    have hxshift :
        (fun i : Fin d => x i + (z i : ℝ)) ∈ openUnitCell (translateLattice z w) :=
      (openUnitCell_translateLattice_iff z w x).2 hxw
    simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hxshift,
      scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := shiftSample z ω) hxw,
      shiftSample]
  · have hxshift :
        ¬ ∃ w : Lattice d,
          (fun i : Fin d => x i + (z i : ℝ)) ∈ openUnitCell w := by
      rintro ⟨w, hw⟩
      let w0 : Lattice d := (translateLatticeEquiv z).symm w
      have hw_eq : translateLattice z w0 = w := by
        exact (translateLatticeEquiv z).apply_symm_apply w
      have hxw0 : x ∈ openUnitCell w0 := by
        exact (openUnitCell_translateLattice_iff z w0 x).1 (by simpa [hw_eq] using hw)
      exact hx ⟨w0, hxw0⟩
    simp [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hxshift,
      scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := shiftSample z ω) hx]

/-- **Carrier commutation for translation**: the carrier translation
endomorphism intertwines the sample map with the lattice shift. -/
theorem translateReg_checkerRegField {d : ℕ} {lam Lam : ℝ}
    (z : Lattice d) (ω : Sample d) :
    translateReg (intVecToRealVec z) (checkerRegField lam Lam ω) =
      checkerRegField lam Lam (shiftSample z ω) := by
  apply RegCoeffField.ext
  intro x
  show coeffField lam Lam ω (x + intVecToRealVec z) =
    coeffField lam Lam (shiftSample z ω) x
  have h : scalarAt lam Lam ω (x + intVecToRealVec z) =
      scalarAt lam Lam (shiftSample z ω) x := by
    simpa [intVecToRealVec] using!
      scalarAt_translate_intVec (lam := lam) (Lam := Lam) z ω x
  simp only [coeffField, h]

/-! ## Unit-separation and coin independence -/

theorem dist_lt_one_of_mem_same_openUnitCell {d : ℕ} {x y : Vec d} {z : Lattice d}
    (hx : x ∈ openUnitCell z) (hy : y ∈ openUnitCell z) :
    dist x y < 1 := by
  refine (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1)).2 fun i => ?_
  have hx_i := hx i
  have hy_i := hy i
  have hsplit : x i - y i = (x i - (z i : ℝ)) - (y i - (z i : ℝ)) := by ring
  calc
    dist (x i) (y i) = |x i - y i| := by rw [Real.dist_eq]
    _ = |(x i - (z i : ℝ)) - (y i - (z i : ℝ))| := by rw [hsplit]
    _ ≤ |x i - (z i : ℝ)| + |y i - (z i : ℝ)| := by
          simpa [abs_sub_comm (z i : ℝ) (y i)] using
            abs_sub_le (x i - (z i : ℝ)) 0 (y i - (z i : ℝ))
    _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hx_i hy_i
    _ = 1 := by norm_num

theorem disjoint_cellsMeeting_of_areUnitSeparated {d : ℕ} {U V : Set (Vec d)}
    (hUV : AreUnitSeparated U V) :
    Disjoint (cellsMeeting U) (cellsMeeting V) := by
  rw [Set.disjoint_left]
  intro z hzU hzV
  rcases hzU with ⟨x, hxU, hxz⟩
  rcases hzV with ⟨y, hyV, hyz⟩
  have hsep : 1 ≤ dist x y := hUV hxU hyV
  have hlt : dist x y < 1 := dist_lt_one_of_mem_same_openUnitCell hxz hyz
  exact not_le_of_gt hlt hsep

theorem iIndep_sampleCoordinateSigma {d : ℕ} (p : ℝ≥0) (hp : p ≤ 1) :
    ProbabilityTheory.iIndep
      (fun z : Lattice d => sampleCoordinateSigma z) (sampleMeasure d p hp) := by
  have hfun :
      ProbabilityTheory.iIndepFun
        (fun z : Lattice d => fun ω : Sample d => (fun b : Bool => b) (ω z))
        (sampleMeasure d p hp) := by
    simpa [sampleMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : Lattice d => coinMeasure p hp)
        (X := fun _ : Lattice d => fun b : Bool => b)
        (mX := fun _ => measurable_id))
  have hraw :=
    (ProbabilityTheory.iIndepFun_iff_iIndep
      (m := fun _ : Lattice d => inferInstance)
      (f := fun z : Lattice d => fun ω : Sample d => (fun b : Bool => b) (ω z))
      (μ := sampleMeasure d p hp)).1 hfun
  simpa [sampleCoordinateSigma] using hraw

theorem indep_sampleCellsSigma_of_disjoint {d : ℕ} {S T : Set (Lattice d)}
    (hST : Disjoint S T) (p : ℝ≥0) (hp : p ≤ 1) :
    ProbabilityTheory.Indep (sampleCellsSigma S) (sampleCellsSigma T) (sampleMeasure d p hp) := by
  have hle :
      ∀ z : Lattice d,
        sampleCoordinateSigma z ≤ (inferInstance : MeasurableSpace (Sample d)) := by
    intro z
    exact (measurable_pi_apply z).comap_le
  have hInd := iIndep_sampleCoordinateSigma (d := d) p hp
  simpa [sampleCellsSigma] using
    (ProbabilityTheory.indep_iSup_of_disjoint
      (m := fun z : Lattice d => sampleCoordinateSigma z)
      (μ := sampleMeasure d p hp) hle hInd (S := S) (T := T) hST)

/-! ## Signed-permutation symmetry -/

def signInt (r : ℝ) : ℤ :=
  if r = 1 then 1 else -1

theorem signInt_cast_eq {r : ℝ} (hr : r = 1 ∨ r = -1) :
    (signInt r : ℝ) = r := by
  rcases hr with h | h
  · subst r
    norm_num [signInt]
  · subst r
    norm_num [signInt]

theorem signInt_mul_self {r : ℝ} (hr : r = 1 ∨ r = -1) :
    signInt r * signInt r = 1 := by
  rcases hr with h | h
  · subst r
    norm_num [signInt]
  · subst r
    norm_num [signInt]

def signedLatticeEquiv {d : ℕ} (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) : Lattice d ≃ Lattice d where
  toFun := fun w i => signInt (s (σ.symm i)) * w (σ.symm i)
  invFun := fun w i => signInt (s i) * w (σ i)
  left_inv := by
    intro w
    funext i
    have hsq := signInt_mul_self (hs i)
    dsimp
    rw [Equiv.symm_apply_apply]
    calc
      signInt (s i) * (signInt (s i) * w i)
          = (signInt (s i) * signInt (s i)) * w i := by ring
      _ = w i := by simp [hsq]
  right_inv := by
    intro w
    funext i
    have hsq := signInt_mul_self (hs (σ.symm i))
    dsimp
    rw [Equiv.apply_symm_apply]
    calc
      signInt (s (σ.symm i)) * (signInt (s (σ.symm i)) * w i)
          = (signInt (s (σ.symm i)) * signInt (s (σ.symm i))) * w i := by ring
      _ = w i := by simp [hsq]

theorem signedLatticeEquiv_apply_sigma {d : ℕ} (σ : Equiv.Perm (Fin d))
    (s : Fin d → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (w : Lattice d) (i : Fin d) :
    signedLatticeEquiv σ s hs w (σ i) = signInt (s i) * w i := by
  simp [signedLatticeEquiv]

def reindexSample {d : ℕ} (e : Lattice d ≃ Lattice d) (ω : Sample d) : Sample d :=
  fun w => ω (e w)

theorem reindexSample_eq_piCongrLeft {d : ℕ} (e : Lattice d ≃ Lattice d) :
    reindexSample e =
      (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool) e.symm) := by
  funext ω w
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (e := e.symm) (β := fun _ : Lattice d => Bool) ω (e w)
  simpa [reindexSample] using h.symm

theorem measurable_reindexSample {d : ℕ} (e : Lattice d ≃ Lattice d) :
    Measurable (reindexSample e : Sample d → Sample d) := by
  rw [reindexSample_eq_piCongrLeft]
  exact (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool) e.symm).measurable

theorem sampleMeasure_map_reindexSample {d : ℕ} (e : Lattice d ≃ Lattice d)
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (reindexSample e) (sampleMeasure d p hp) = sampleMeasure d p hp := by
  rw [reindexSample_eq_piCongrLeft]
  have h :=
    Measure.infinitePi_map_piCongrLeft
      (X := fun _ : Lattice d => Bool)
      (μ := fun _ : Lattice d => coinMeasure p hp)
      (e := e.symm)
  simpa [sampleMeasure] using h

theorem matVecMul_signedPermutation_apply {d : ℕ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (_hs : ∀ i, s i = 1 ∨ s i = -1)
    (hR : ∀ i j, R i j = if i = σ j then s j else 0)
    (x : Vec d) (i : Fin d) :
    matVecMul R x i = s (σ.symm i) * x (σ.symm i) := by
  unfold matVecMul
  rw [Finset.sum_eq_single (σ.symm i)]
  · rw [hR i (σ.symm i)]
    simp
  · intro j _ hj
    rw [hR i j]
    have hij : i ≠ σ j := by
      intro hij
      apply hj
      exact σ.injective (by simpa using hij.symm)
    simp [hij]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem openUnitCell_signedPermutation_iff {d : ℕ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hR : ∀ i j, R i j = if i = σ j then s j else 0)
    (w : Lattice d) (x : Vec d) :
    matVecMul R x ∈ openUnitCell (signedLatticeEquiv σ s hs w) ↔
      x ∈ openUnitCell w := by
  constructor
  · intro hx i
    have hcoord := hx (σ i)
    have hmul := signInt_cast_eq (hs i)
    have hrewrite :
        matVecMul R x (σ i) - (signedLatticeEquiv σ s hs w (σ i) : ℝ) =
          s i * (x i - (w i : ℝ)) := by
      rw [matVecMul_signedPermutation_apply hs hR]
      simp [signedLatticeEquiv_apply_sigma, hmul]
      ring
    rw [hrewrite] at hcoord
    rcases hs i with hsi | hsi
    · simpa [hsi] using hcoord
    · simpa [hsi, abs_sub_comm] using hcoord
  · intro hx i
    let j : Fin d := σ.symm i
    have hxj := hx j
    have hmul := signInt_cast_eq (hs j)
    have hrewrite :
        matVecMul R x i - (signedLatticeEquiv σ s hs w i : ℝ) =
          s j * (x j - (w j : ℝ)) := by
      rw [matVecMul_signedPermutation_apply hs hR]
      simp [j, signedLatticeEquiv, hmul]
      ring
    rw [hrewrite]
    rcases hs j with hsj | hsj
    · simpa [hsj] using hxj
    · simpa [hsj, abs_sub_comm] using hxj

theorem scalarAt_signedPermutation {d : ℕ} {lam Lam : ℝ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hR : ∀ i j, R i j = if i = σ j then s j else 0)
    (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω (matVecMul R x) =
      scalarAt lam Lam (reindexSample (signedLatticeEquiv σ s hs) ω) x := by
  classical
  by_cases hx : ∃ w : Lattice d, x ∈ openUnitCell w
  · let w : Lattice d := Classical.choose hx
    have hxw : x ∈ openUnitCell w := Classical.choose_spec hx
    have hRx :
        matVecMul R x ∈ openUnitCell (signedLatticeEquiv σ s hs w) :=
      (openUnitCell_signedPermutation_iff hs hR w x).2 hxw
    simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hRx,
      scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam)
        (ω := reindexSample (signedLatticeEquiv σ s hs) ω) hxw,
      reindexSample]
  · have hRx :
        ¬ ∃ w : Lattice d, matVecMul R x ∈ openUnitCell w := by
      rintro ⟨w, hw⟩
      let w0 : Lattice d := (signedLatticeEquiv σ s hs).symm w
      have hw_eq : signedLatticeEquiv σ s hs w0 = w :=
        (signedLatticeEquiv σ s hs).apply_symm_apply w
      have hxw0 : x ∈ openUnitCell w0 :=
        (openUnitCell_signedPermutation_iff hs hR w0 x).1 (by simpa [hw_eq] using hw)
      exact hx ⟨w0, hxw0⟩
    simp [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hRx,
      scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam)
        (ω := reindexSample (signedLatticeEquiv σ s hs) ω) hx]

/-- **Carrier commutation for rotation**: the carrier signed-permutation
endomorphism intertwines the sample map with the lattice reindexing. -/
theorem rotateReg_checkerRegField {d : ℕ} {lam Lam : ℝ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hRdef : ∀ i j, R i j = if i = σ j then s j else 0)
    (hR : IsSignedPermutationMatrix R) (ω : Sample d) :
    rotateReg R hR (checkerRegField lam Lam ω) =
      checkerRegField lam Lam (reindexSample (signedLatticeEquiv σ s hs) ω) := by
  apply RegCoeffField.ext
  intro x
  show (matTranspose R) * (coeffField lam Lam ω (matVecMul R x)) * R =
    coeffField lam Lam (reindexSample (signedLatticeEquiv σ s hs) ω) x
  have hscalar :
      scalarAt lam Lam ω (matVecMul R x) =
        scalarAt lam Lam (reindexSample (signedLatticeEquiv σ s hs) ω) x :=
    scalarAt_signedPermutation hs hRdef ω x
  simp [coeffField, scalarMatrix, hscalar, hR.transpose_mul_self]

/-- **Carrier commutation for the adjoint**: every checkerboard realization is
symmetric (a scalar matrix field), so the carrier adjoint fixes it. -/
theorem adjointReg_checkerRegField {d : ℕ} {lam Lam : ℝ} (ω : Sample d) :
    adjointReg (checkerRegField lam Lam ω) = checkerRegField lam Lam ω := by
  apply RegCoeffField.ext
  intro x
  show (coeffField lam Lam ω x).transpose = coeffField lam Lam ω x
  funext i j
  by_cases hij : i = j
  · subst j
    simp [coeffField, scalarMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [coeffField, Matrix.transpose_apply, scalarMatrix,
      Matrix.one_apply_ne hij, Matrix.one_apply_ne hji]

end

end RandomCheckerboard
end Examples
end Homogenization
