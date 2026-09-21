/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.ClampedObservable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily
import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SliceMeasurability

/-!
# The carrier-measurable clamped observable

The shipped fixed-phase Efron–Stein chain exhibited a product-measurable
observable on the **raw** tuple space `(↥K → CoeffField d)` via the fine
`PointwiseLocalSigma` generator trick (`measurable_coreLocalEnergy`).  On the honest
carrier that trick is unavailable (fine local events are not carrier events),
and the truncated per-core energy is a genuinely nonlinear functional of the
field, so its entry-test lane is not a transported generator.

This file replaces that measurability heart with an **honest carrier
construction**:

* `coreWindow` — the open core window (open interior box ∩ open cube), whose
  difference from the half-open core piece `coreBox ∩ cubeSet` is Lebesgue-null;
* `coreGoodSet` — the genuinely measurable event (a `slicePart` rational-ball
  intersection, Packet P4b) that the field is a.e. `(1,Θ)`-elliptic on the core
  window;
* `coreLocalEnergyR` — the per-core energy of the truncated glued field,
  totalized by `0` off `coreGoodSet`;
* `measurable_coreLocalEnergyR` — **the measurability heart**: on `coreGoodSet`
  the truncation is a.e. invisible, so the energy decomposes as a corridor
  constant plus an indicator-weighted block-coefficient integral over the open
  window, measurable through the carrier `L²` realization engine of
  `CarrierMuFamily` (dense-probe inner products = localized `entryTestR`
  generators);
* `phaseSplitEnergyR`, `rawPhaseObservableR`, `clampedPhaseObservableR` — the
  assembled genuinely product-measurable clamped observable on carrier tuples;
* `clampedPhaseObservableR_restrict_eq_of_field` — the diagonal identity: on the
  carrier restriction tuple of a measurable, a.e. `(1,Θ)`-elliptic field it
  reproduces the fixed-phase observable exactly (via the shipped raw five-link
  identity).

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

open Homogenization
open scoped MeasureTheory BigOperators
open MeasureTheory

namespace Homogenization

variable {d : ℕ}

/-! ## The open core window and its null boundary -/

/-- The open interior box of `coreBox` (product of open intervals). -/
def coreBoxIoo (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) : Set (Vec d) :=
  Set.pi Set.univ
    (fun i => Set.Ioo (σ i + k i * ℓ + 1) (σ i + (k i + 1) * ℓ - 1))

theorem coreBoxIoo_subset_coreBox {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ} :
    coreBoxIoo ℓ σ k ⊆ coreBox ℓ σ k :=
  Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)

theorem isOpen_coreBoxIoo (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    IsOpen (coreBoxIoo ℓ σ k) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

/-- The closed core box agrees with its open interior box up to a null set. -/
theorem coreBox_ae_eq_coreBoxIoo (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    coreBox ℓ σ k =ᵐ[MeasureTheory.volume] coreBoxIoo ℓ σ k := by
  unfold coreBox coreBoxIoo
  rw [Set.pi_univ_Icc]
  exact (MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc
    (f := fun i : Fin d => σ i + k i * ℓ + 1)
    (g := fun i : Fin d => σ i + (k i + 1) * ℓ - 1)).symm

/-- The open core window: interior box ∩ open cube. -/
def coreWindow (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (m : ℤ) : Set (Vec d) :=
  coreBoxIoo ℓ σ k ∩ openCubeSet (originCube d m)

theorem isOpen_coreWindow (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (m : ℤ) :
    IsOpen (coreWindow ℓ σ k m) :=
  (isOpen_coreBoxIoo ℓ σ k).inter (isOpen_openCubeSet (originCube d m))

theorem measurableSet_coreWindow (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (m : ℤ) :
    MeasurableSet (coreWindow ℓ σ k m) :=
  (isOpen_coreWindow ℓ σ k m).measurableSet

theorem coreWindow_subset_cubeSet {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ} {m : ℤ} :
    coreWindow ℓ σ k m ⊆ cubeSet (originCube d m) :=
  fun _ hx => openCubeSet_subset_cubeSet (originCube d m) hx.2

theorem coreWindow_subset_coreBox {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ} {m : ℤ} :
    coreWindow ℓ σ k m ⊆ coreBox ℓ σ k :=
  fun _ hx => coreBoxIoo_subset_coreBox hx.1

/-- The half-open core piece agrees with the open core window up to a null
set. -/
theorem corePiece_ae_eq_coreWindow (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (m : ℤ) :
    ((coreBox ℓ σ k ∩ cubeSet (originCube d m) : Set (Vec d)))
      =ᵐ[MeasureTheory.volume] coreWindow ℓ σ k m :=
  MeasureTheory.ae_eq_set_inter (coreBox_ae_eq_coreBoxIoo ℓ σ k)
    (cubeSet_ae_eq_openCubeSet (originCube d m))

theorem isFiniteMeasure_volumeMeasureOn_coreWindow (ℓ : ℝ) (σ : Vec d)
    (k : Fin d → ℤ) (m : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (coreWindow ℓ σ k m)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono coreWindow_subset_cubeSet)
    (volume_cubeSet_lt_top (originCube d m))

theorem isFiniteMeasure_volumeMeasureOn_corePiece (ℓ : ℝ) (σ : Vec d)
    (k : Fin d → ℤ) (m : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (coreBox ℓ σ k ∩ cubeSet (originCube d m))) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (measure_mono Set.inter_subset_right)
    (volume_cubeSet_lt_top (originCube d m))

/-! ## The good event -/

/-- The genuinely measurable good event: the field is a.e. `(1,Θ)`-elliptic on
the open core window (as a `slicePart` rational-ball intersection). -/
def coreGoodSet (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (k : Fin d → ℤ) (m : ℤ) :
    Set (RegCoeffField d) :=
  slicePart (coreWindow ℓ σ k m) 1 Θ

theorem measurableSet_coreGoodSet (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (k : Fin d → ℤ)
    (m : ℤ) : MeasurableSet (coreGoodSet ℓ σ Θ k m) :=
  LocalSigmaR_le (coreWindow ℓ σ k m) _ (measurableSet_slicePart 1 Θ)

/-- Membership in the good event is exactly a.e. `(1,Θ)`-ellipticity on the open
core window. -/
theorem mem_coreGoodSet_iff {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {k : Fin d → ℤ} {m : ℤ}
    {b : RegCoeffField d} :
    b ∈ coreGoodSet ℓ σ Θ k m ↔
      ∀ᵐ x ∂(volume.restrict (coreWindow ℓ σ k m)), IsEllipticMatrix 1 Θ (b x) := by
  rw [coreGoodSet, ← setOf_aeRestrict_isEllipticMatrix_eq_slicePart
    (isOpen_coreWindow ℓ σ k m) 1 Θ]
  rfl

/-- On the good event, the field is a.e. `(1,Θ)`-elliptic on the half-open core
piece as well (null boundary). -/
theorem ae_isEllipticMatrix_corePiece_of_mem_coreGoodSet {ℓ : ℝ} {σ : Vec d}
    {Θ : ℝ} {k : Fin d → ℤ} {m : ℤ} {b : RegCoeffField d}
    (hb : b ∈ coreGoodSet ℓ σ Θ k m) :
    ∀ᵐ x ∂(volume.restrict (coreBox ℓ σ k ∩ cubeSet (originCube d m))),
      IsEllipticMatrix 1 Θ (b x) := by
  rw [Measure.restrict_congr_set (corePiece_ae_eq_coreWindow ℓ σ k m)]
  exact mem_coreGoodSet_iff.1 hb

/-- The slice level attached to the ellipticity constant `Θ`. -/
noncomputable def thetaSliceLevel (Θ : ℝ) : ℕ := ⌈Θ⌉₊

/-- On the good event, the field lies in the AEE quantitative slice of the open
core window at level `⌈Θ⌉₊`. -/
theorem aeeSlice_coreWindow_of_mem_coreGoodSet {ℓ : ℝ} {σ : Vec d} {Θ : ℝ}
    {k : Fin d → ℤ} {m : ℤ} {b : RegCoeffField d}
    (hb : b ∈ coreGoodSet ℓ σ Θ k m) :
    AEEQuantitativeEllipticSlice (coreWindow ℓ σ k m) (thetaSliceLevel Θ) b.toFun := by
  rw [aeeQuantitativeEllipticSlice_carrier_iff _ (measurableSet_coreWindow ℓ σ k m)]
  filter_upwards [mem_coreGoodSet_iff.1 hb] with x hx
  have h1 : (0 : ℝ) < ((thetaSliceLevel Θ : ℝ) + 1)⁻¹ := by positivity
  have h2 : ((thetaSliceLevel Θ : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    have : (0 : ℝ) ≤ (thetaSliceLevel Θ : ℝ) := by positivity
    linarith
  have h3 : Θ ≤ (thetaSliceLevel Θ : ℝ) + 1 := by
    have := Nat.le_ceil Θ
    have hcast : (⌈Θ⌉₊ : ℝ) ≤ (thetaSliceLevel Θ : ℝ) := le_of_eq rfl
    unfold thetaSliceLevel
    linarith [Nat.le_ceil Θ]
  exact hx.mono h1 h2 h3

/-! ## The totalized per-core energy -/

/-- The per-core energy of the truncated glued field, totalized by `0` off the
genuinely measurable good event. -/
noncomputable def coreLocalEnergyR (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (m : ℤ)
    (X : BlockState d) (k : Fin d → ℤ) (b : RegCoeffField d) : ℝ := by
  classical
  exact if b ∈ coreGoodSet ℓ σ Θ k m then
    coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k ∩ cubeSet (originCube d m)) X b.toFun
  else 0

theorem coreLocalEnergyR_of_mem {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    {X : BlockState d} {k : Fin d → ℤ} {b : RegCoeffField d}
    (hb : b ∈ coreGoodSet ℓ σ Θ k m) :
    coreLocalEnergyR ℓ σ Θ m X k b
      = coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k ∩ cubeSet (originCube d m)) X b.toFun := by
  classical
  simp [coreLocalEnergyR, hb]

/-! ## The decomposition on the good event -/

/-- The truncated glued field of an entrywise-measurable field is genuinely
`(1,Θ)`-elliptic on any measurable set (general-`W` version of the cube
statement in `ClampedObservable`). -/
theorem isEllipticFieldOn_glueField_of_field_set {ℓ : ℝ} {σ : Vec d} {Θ : ℝ}
    {W : Set (Vec d)} (hW : MeasurableSet W) (hΘ : 1 ≤ Θ) {b : CoeffField d}
    (hbmeas : ∀ i j : Fin d, Measurable fun x : Vec d => b x i j) :
    IsEllipticFieldOn 1 Θ W (glueField ℓ σ Θ b) := by
  classical
  have hcorrM : MeasurableSet (corridorSet ℓ σ) := measurableSet_corridorSet ℓ σ
  have hmeasField :
      Measurable (fun x : Vec d => fun i j =>
        if x ∈ W then (corridorField ℓ σ b) x i j else 0) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have hrw :
        (fun x : Vec d => if x ∈ W then (corridorField ℓ σ b) x i j else 0)
          = fun x : Vec d =>
            if x ∈ W then
              (if x ∈ corridorSet ℓ σ then (1 : Mat d) i j else b x i j) else 0 := by
      funext x
      by_cases hxW : x ∈ W
      · simp only [hxW, if_true]
        by_cases hxc : x ∈ corridorSet ℓ σ
        · rw [corridorField_apply_of_mem hxc]; simp [hxc]
        · rw [corridorField_apply_of_not_mem hxc]; simp [hxc]
      · simp [hxW]
    rw [hrw]
    exact Measurable.ite hW
      (Measurable.ite hcorrM measurable_const (hbmeas i j)) measurable_const
  exact isEllipticFieldOn_ellipticTruncate hW hΘ hmeasField

/-- **The decomposition of the per-core energy on the good event.**  The
truncation is invisible off the corridor, so the energy is a corridor constant
plus an indicator-weighted sum of block-coefficient entry integrals over the
open core window. -/
theorem coreLocalEnergy_eq_corridorPiece_add_sum {ℓ : ℝ} {σ : Vec d} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) {m : ℤ} (X : BlockState d)
    (hX : MemBlockL2 (cubeSet (originCube d m)) X.eval)
    {k : Fin d → ℤ} {b : RegCoeffField d} (hb : b ∈ coreGoodSet ℓ σ Θ k m) :
    coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k ∩ cubeSet (originCube d m)) X b.toFun
      = (∫ x in (coreBox ℓ σ k ∩ cubeSet (originCube d m)) ∩ corridorSet ℓ σ,
            blockEnergyDensity (fun _ => (1 : Mat d)) X x ∂volume)
        + ∑ α, ∑ β,
            ∫ x in coreWindow ℓ σ k m,
              Set.indicator
                  ((coreBox ℓ σ k ∩ cubeSet (originCube d m)) \ corridorSet ℓ σ)
                  (blockEnergyEntryWeight X α β) x
                * toFullBlockMat (blockCoeffField b.toFun x) α β ∂volume := by
  classical
  set W : Set (Vec d) := coreBox ℓ σ k ∩ cubeSet (originCube d m) with hWdef
  set V : Set (Vec d) := coreWindow ℓ σ k m with hVdef
  set T : Set (Vec d) := W \ corridorSet ℓ σ with hTdef
  have hWmeas : MeasurableSet W :=
    (measurableSet_coreBox ℓ σ k).inter (measurableSet_cubeSet (originCube d m))
  have hcorrM : MeasurableSet (corridorSet ℓ σ) := measurableSet_corridorSet ℓ σ
  have hTmeas : MeasurableSet T := hWmeas.diff hcorrM
  have : IsFiniteMeasure (volumeMeasureOn W) :=
    isFiniteMeasure_volumeMeasureOn_corePiece ℓ σ k m
  have : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_volumeMeasureOn_coreWindow ℓ σ k m
  -- L² membership on the core piece and the window
  have hXW : MemBlockL2 W X.eval :=
    hX.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  have hXV : MemBlockL2 V X.eval :=
    hX.mono_measure (Measure.restrict_mono coreWindow_subset_cubeSet le_rfl)
  -- a.e. ellipticity on the core piece
  have hbW : ∀ᵐ x ∂(volume.restrict W), IsEllipticMatrix 1 Θ (b x) :=
    ae_isEllipticMatrix_corePiece_of_mem_coreGoodSet hb
  -- integrability of the glued density on the core piece
  have hglueEll : IsEllipticFieldOn 1 Θ W (glueField ℓ σ Θ b.toFun) :=
    isEllipticFieldOn_glueField_of_field_set hWmeas hΘ
      (fun i j => b.entry_measurable i j)
  have hIntOn : IntegrableOn (blockEnergyDensity (glueField ℓ σ Θ b.toFun) X) W := by
    have hpair := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (a := glueField ℓ σ Θ b.toFun) hXW hXW hglueEll
    have hEq : blockEnergyDensity (glueField ℓ σ Θ b.toFun) X
        = fun x => (1 / 2 : ℝ) *
            blockPairingIntegrand (glueField ℓ σ Θ b.toFun) X X x := by
      funext x; rfl
    rw [hEq]
    exact hpair.const_mul (1 / 2)
  -- split off the corridor
  have hsplit :
      (∫ x in W, blockEnergyDensity (glueField ℓ σ Θ b.toFun) X x ∂volume)
        = (∫ x in W ∩ corridorSet ℓ σ,
              blockEnergyDensity (glueField ℓ σ Θ b.toFun) X x ∂volume)
          + ∫ x in T, blockEnergyDensity (glueField ℓ σ Θ b.toFun) X x ∂volume :=
    (MeasureTheory.integral_inter_add_sdiff hcorrM hIntOn).symm
  -- corridor piece: the glued field is the identity there
  have hcorrEq :
      (∫ x in W ∩ corridorSet ℓ σ,
          blockEnergyDensity (glueField ℓ σ Θ b.toFun) X x ∂volume)
        = ∫ x in W ∩ corridorSet ℓ σ,
            blockEnergyDensity (fun _ => (1 : Mat d)) X x ∂volume := by
    refine MeasureTheory.setIntegral_congr_fun (hWmeas.inter hcorrM) (fun x hx => ?_)
    have hval : glueField ℓ σ Θ b.toFun x = (1 : Mat d) :=
      glueField_apply_of_mem_corridor hΘ hx.2
    simp only [blockEnergyDensity, blockCoeffField, hval]
  -- off the corridor the truncation is a.e. invisible
  have hbT : ∀ᵐ x ∂(volume.restrict T), IsEllipticMatrix 1 Θ (b x) :=
    ae_restrict_of_ae_restrict_of_subset Set.sdiff_subset hbW
  have hTglue :
      (∫ x in T, blockEnergyDensity (glueField ℓ σ Θ b.toFun) X x ∂volume)
        = ∫ x in T, blockEnergyDensity b.toFun X x ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hbT, ae_restrict_mem hTmeas] with x hxEll hxT
    have hcorr : corridorField ℓ σ b.toFun x = b.toFun x :=
      corridorField_apply_of_not_mem hxT.2
    have hval : glueField ℓ σ Θ b.toFun x = b.toFun x := by
      unfold glueField
      rw [ellipticTruncate_of_elliptic (by rw [hcorr]; exact hxEll), hcorr]
    simp only [blockEnergyDensity, blockCoeffField, hval]
  -- move to the open window
  have hWVnull : volume (W \ V) = 0 :=
    ((MeasureTheory.ae_eq_set.1 (corePiece_ae_eq_coreWindow ℓ σ k m)).1)
  have hTV : T =ᵐ[MeasureTheory.volume] ((T ∩ V : Set (Vec d))) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null ?_ hWVnull
      intro x hx
      exact ⟨hx.1.1, fun hxV => hx.2 ⟨hx.1, hxV⟩⟩
    · exact measure_mono_null
        (fun x hx => absurd hx.1.1 hx.2) hWVnull
  have hTwindow :
      (∫ x in T, blockEnergyDensity b.toFun X x ∂volume)
        = ∫ x in V, Set.indicator T (fun x => blockEnergyDensity b.toFun X x) x ∂volume := by
    rw [MeasureTheory.setIntegral_congr_set hTV,
      MeasureTheory.setIntegral_indicator hTmeas, Set.inter_comm V T]
  -- the pointwise entry-weight expansion under the indicator
  have hpoint : (fun x => Set.indicator T (fun x => blockEnergyDensity b.toFun X x) x)
      = fun x => ∑ α, ∑ β,
          Set.indicator T (blockEnergyEntryWeight X α β) x
            * toFullBlockMat (blockCoeffField b.toFun x) α β := by
    funext x
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, blockEnergyDensity_eq_sum_entryWeights]
      refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
      rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      symm
      refine Finset.sum_eq_zero (fun α _ => Finset.sum_eq_zero (fun β _ => ?_))
      rw [Set.indicator_of_notMem hx, zero_mul]
  -- slice membership and integrability of the weighted entries on the window
  have hSliceb : AEEQuantitativeEllipticSlice V (thetaSliceLevel Θ) b.toFun :=
    aeeSlice_coreWindow_of_mem_coreGoodSet hb
  have hInt_αβ : ∀ α β : BlockCoord d,
      Integrable
        (fun x => Set.indicator T (blockEnergyEntryWeight X α β) x
          * toFullBlockMat (blockCoeffField b.toFun x) α β) (volumeMeasureOn V) := by
    intro α β
    exact hSliceb.integrable_weightedFullBlockCoeffEntry_of_integrable
      ((integrable_blockEnergyEntryWeight_of_memBlockL2 hXV α β).indicator hTmeas) α β
  have hsum :
      (∫ x in V, (∑ α, ∑ β,
          Set.indicator T (blockEnergyEntryWeight X α β) x
            * toFullBlockMat (blockCoeffField b.toFun x) α β) ∂volume)
        = ∑ α, ∑ β,
            ∫ x in V, Set.indicator T (blockEnergyEntryWeight X α β) x
              * toFullBlockMat (blockCoeffField b.toFun x) α β ∂volume := by
    rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hInt_αβ α β))]
    exact Finset.sum_congr rfl
      (fun α _ => integral_finsetSum _ (fun β _ => hInt_αβ α β))
  -- assemble
  unfold coreLocalEnergy
  rw [hsplit, hcorrEq, hTglue, hTwindow, hpoint, hsum]

/-! ## The measurability heart -/

/-- **The totalized per-core energy is genuinely measurable on the carrier.**
On the good event the energy is a corridor constant plus indicator-weighted
block-coefficient entry integrals over the open core window, each measurable
through the carrier `L²` realization engine; off the good event it is `0`, and
the good event itself is genuinely measurable (`slicePart`). -/
theorem measurable_coreLocalEnergyR {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} (X : BlockState d)
    (hX : MemBlockL2 (cubeSet (originCube d m)) X.eval) (k : Fin d → ℤ) :
    Measurable (coreLocalEnergyR ℓ σ Θ m X k) := by
  classical
  set V : Set (Vec d) := coreWindow ℓ σ k m with hVdef
  set T : Set (Vec d) :=
    (coreBox ℓ σ k ∩ cubeSet (originCube d m)) \ corridorSet ℓ σ with hTdef
  have hTmeas : MeasurableSet T :=
    ((measurableSet_coreBox ℓ σ k).inter
      (measurableSet_cubeSet (originCube d m))).diff (measurableSet_corridorSet ℓ σ)
  have : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_volumeMeasureOn_coreWindow ℓ σ k m
  have hXV : MemBlockL2 V X.eval :=
    hX.mono_measure (Measure.restrict_mono coreWindow_subset_cubeSet le_rfl)
  -- the carrier L² realization on the good-event subtype
  set G : Set (RegCoeffField d) := coreGoodSet ℓ σ Θ k m with hGdef
  have hGmeas : MeasurableSet G := measurableSet_coreGoodSet ℓ σ Θ k m
  have hSlice : ∀ ω : ↥G,
      AEEQuantitativeEllipticSlice V (thetaSliceLevel Θ) ((ω : RegCoeffField d)).toFun :=
    fun ω => aeeSlice_coreWindow_of_mem_coreGoodSet ω.2
  have hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, IsProbeR φ →
      Function.support φ ⊆ V →
      Measurable (fun ω : ↥G => entryTestR i j φ (ω : RegCoeffField d)) :=
    fun i j φ hφ _ => (measurable_entryTestR i j hφ).comp measurable_subtype_coe
  have hEntrySmooth : ∀ (i j : Fin d) {φ : Vec d → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V →
      Measurable (fun ω : ↥G => entryTestR i j φ (ω : RegCoeffField d)) := by
    intro i j φ hcont hcompact htsupport
    exact hEntry i j (IsProbeR.of_smooth hcont hcompact)
      ((Function.support_subset_iff.2 (fun x hx => subset_tsupport φ hx)).trans htsupport)
  have hF := measurable_toHilbertMatrixL2_carrier
    (A := fun ω : ↥G => (ω : RegCoeffField d)) (hSlice := hSlice)
    (measurableSet_coreWindow ℓ σ k m) hEntrySmooth (isOpen_coreWindow ℓ σ k m)
    (by
      have := isFiniteMeasure_volumeMeasureOn_coreWindow ℓ σ k m
      have hlt : volume V < ⊤ :=
        lt_of_le_of_lt (measure_mono coreWindow_subset_cubeSet)
          (volume_cubeSet_lt_top (originCube d m))
      exact hlt.ne)
  -- the branch function on the subtype
  have hbranch : Measurable (fun ω : ↥G =>
      coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k ∩ cubeSet (originCube d m)) X
        ((ω : RegCoeffField d)).toFun) := by
    have hrw : (fun ω : ↥G =>
        coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k ∩ cubeSet (originCube d m)) X
          ((ω : RegCoeffField d)).toFun)
        = fun ω : ↥G =>
            (∫ x in (coreBox ℓ σ k ∩ cubeSet (originCube d m)) ∩ corridorSet ℓ σ,
                blockEnergyDensity (fun _ => (1 : Mat d)) X x ∂volume)
              + ∑ α, ∑ β,
                  ∫ x in V,
                    Set.indicator T (blockEnergyEntryWeight X α β) x
                      * toFullBlockMat (blockCoeffField ((ω : RegCoeffField d)).toFun x) α β
                    ∂volume := by
      funext ω
      exact coreLocalEnergy_eq_corridorPiece_add_sum hΘ X hX ω.2
    rw [hrw]
    refine measurable_const.add ?_
    refine Finset.measurable_sum _ (fun α _ => Finset.measurable_sum _ (fun β _ => ?_))
    exact measurable_integrableWeightedFullBlockCoeffEntry_carrier hF
      ((integrable_blockEnergyEntryWeight_of_memBlockL2 hXV α β).indicator hTmeas) α β
  -- assemble the dite
  have hrwR : coreLocalEnergyR ℓ σ Θ m X k
      = fun b : RegCoeffField d =>
          if h : b ∈ G then
            (fun ω : ↥G =>
              coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k ∩ cubeSet (originCube d m)) X
                ((ω : RegCoeffField d)).toFun) ⟨b, h⟩
          else (fun _ : ↥(Gᶜ) => (0 : ℝ)) ⟨b, h⟩ := by
    funext b
    by_cases hb : b ∈ G
    · simp [coreLocalEnergyR, hGdef]
    · simp [coreLocalEnergyR, hGdef]
  rw [hrwR]
  exact Measurable.dite hbranch measurable_const hGmeas

/-! ## The assembled carrier observables -/

/-- The carrier split observable: corridor constant plus totalized per-core
energies, normalized by the cube volume. -/
noncomputable def phaseSplitEnergyR (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (m : ℤ)
    (X : BlockState d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → RegCoeffField d) : ℝ :=
  (volume (cubeSet (originCube d m))).toReal⁻¹ *
    (corridorConst ℓ σ (cubeSet (originCube d m)) X
      + ∑ k : {k // k ∈ K}, coreLocalEnergyR ℓ σ Θ m X k.1 (y k))

theorem measurable_phaseSplitEnergyR {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} (X : BlockState d)
    (hX : MemBlockL2 (cubeSet (originCube d m)) X.eval) (K : Finset (Fin d → ℤ)) :
    Measurable
      (fun y : {k // k ∈ K} → RegCoeffField d => phaseSplitEnergyR ℓ σ Θ m X K y) := by
  unfold phaseSplitEnergyR
  refine measurable_const.mul (measurable_const.add ?_)
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact (measurable_coreLocalEnergyR hΘ X hX k.1).comp (measurable_pi_apply k)

/-- On tuples of good coordinates the carrier split observable agrees with the
raw split observable of the underlying fields. -/
theorem phaseSplitEnergyR_eq_of_good {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (X : BlockState d) {K : Finset (Fin d → ℤ)}
    {y : {k // k ∈ K} → RegCoeffField d}
    (hy : ∀ k : {k // k ∈ K}, y k ∈ coreGoodSet ℓ σ Θ k.1 m) :
    phaseSplitEnergyR ℓ σ Θ m X K y
      = phaseSplitEnergy ℓ σ Θ (cubeSet (originCube d m)) X K
          (fun k => (y k).toFun) := by
  unfold phaseSplitEnergyR phaseSplitEnergy
  have hsum : (∑ k : {k // k ∈ K}, coreLocalEnergyR ℓ σ Θ m X k.1 (y k))
      = ∑ k : {k // k ∈ K},
          coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k.1 ∩ cubeSet (originCube d m)) X
            (y k).toFun :=
    Finset.sum_congr rfl (fun k _ => coreLocalEnergyR_of_mem (hy k))
  rw [hsum]

/-- The carrier raw observable: twice the infimum over the canonical competitor
family of the carrier split energies. -/
noncomputable def rawPhaseObservableR (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (m : ℤ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → RegCoeffField d) : ℝ :=
  2 * ⨅ n : ℕ,
    phaseSplitEnergyR ℓ σ Θ m (phaseCompetitor (originCube d m) P n) K y

theorem measurable_rawPhaseObservableR {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} (P : BlockVec d) (K : Finset (Fin d → ℤ)) :
    Measurable
      (fun y : {k // k ∈ K} → RegCoeffField d => rawPhaseObservableR ℓ σ Θ m P K y) := by
  unfold rawPhaseObservableR
  refine measurable_const.mul (Measurable.iInf (fun n => ?_))
  exact measurable_phaseSplitEnergyR hΘ _
    (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet (originCube d m)) P _) K

/-- On tuples of good coordinates the carrier raw observable agrees with the raw
one. -/
theorem rawPhaseObservableR_eq_of_good {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (P : BlockVec d) {K : Finset (Fin d → ℤ)}
    {y : {k // k ∈ K} → RegCoeffField d}
    (hy : ∀ k : {k // k ∈ K}, y k ∈ coreGoodSet ℓ σ Θ k.1 m) :
    rawPhaseObservableR ℓ σ Θ m P K y
      = rawPhaseObservable ℓ σ Θ m P K (fun k => (y k).toFun) := by
  unfold rawPhaseObservableR rawPhaseObservable
  congr 1
  exact iInf_congr (fun n => phaseSplitEnergyR_eq_of_good _ hy)

/-- The carrier clamped observable. -/
noncomputable def clampedPhaseObservableR (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (m : ℤ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → RegCoeffField d) : ℝ :=
  max 0 (min (phaseBound Θ P) (rawPhaseObservableR ℓ σ Θ m P K y))

theorem measurable_clampedPhaseObservableR {ℓ : ℝ} {σ : Vec d} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) {m : ℤ} (P : BlockVec d) (K : Finset (Fin d → ℤ)) :
    Measurable
      (fun y : {k // k ∈ K} → RegCoeffField d =>
        clampedPhaseObservableR ℓ σ Θ m P K y) := by
  unfold clampedPhaseObservableR
  exact measurable_const.max
    (measurable_const.min (measurable_rawPhaseObservableR hΘ P K))

/-- The carrier clamped observable is globally bounded by `phaseBound Θ P`. -/
theorem abs_clampedPhaseObservableR_le {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (hΘ : 1 ≤ Θ) (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → RegCoeffField d) :
    |clampedPhaseObservableR ℓ σ Θ m P K y| ≤ phaseBound Θ P := by
  unfold clampedPhaseObservableR
  rw [abs_le]
  refine ⟨le_trans (by linarith [phaseBound_nonneg hΘ P]) (le_max_left _ _),
    max_le (phaseBound_nonneg hΘ P) (min_le_left _ _)⟩

/-- On tuples of good coordinates the carrier clamped observable agrees with the
raw clamped observable of the underlying fields. -/
theorem clampedPhaseObservableR_eq_of_good {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (P : BlockVec d) {K : Finset (Fin d → ℤ)}
    {y : {k // k ∈ K} → RegCoeffField d}
    (hy : ∀ k : {k // k ∈ K}, y k ∈ coreGoodSet ℓ σ Θ k.1 m) :
    clampedPhaseObservableR ℓ σ Θ m P K y
      = clampedPhaseObservable ℓ σ Θ m P K (fun k => (y k).toFun) := by
  unfold clampedPhaseObservableR clampedPhaseObservable
  rw [rawPhaseObservableR_eq_of_good P hy]

/-! ## The diagonal identity -/

/-- The `toFun` of the carrier restriction is the raw restriction of the
`toFun`. -/
theorem restrictReg_toFun_eq (U : Set (Vec d)) (hU : MeasurableSet U)
    (b : RegCoeffField d) :
    (restrictReg U hU b).toFun = restrictCoeffField U b.toFun := by
  funext x
  by_cases hx : x ∈ U
  · rw [restrictCoeffField_apply_of_mem hx]
    exact Set.indicator_of_mem hx _
  · rw [restrictCoeffField_apply_of_not_mem hx]
    exact Set.indicator_of_notMem hx _

/-- The carrier restriction of a globally a.e.-`(1,Θ)`-elliptic field to a core
box lies in the good event of that core. -/
theorem restrictReg_mem_coreGoodSet {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    {k : Fin d → ℤ} {b : RegCoeffField d}
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (b x)) :
    restrictReg (coreBox ℓ σ k) (measurableSet_coreBox ℓ σ k) b
      ∈ coreGoodSet ℓ σ Θ k m := by
  rw [mem_coreGoodSet_iff]
  filter_upwards [ae_restrict_of_ae hbell,
    ae_restrict_mem (measurableSet_coreWindow ℓ σ k m)] with x hxEll hxV
  have hxk : x ∈ coreBox ℓ σ k := coreWindow_subset_coreBox hxV
  have hval : restrictReg (coreBox ℓ σ k) (measurableSet_coreBox ℓ σ k) b x = b x := by
    rw [restrictReg_apply, Set.indicator_of_mem hxk]
  rw [hval]
  exact hxEll

/-- **The diagonal identity.**  On the carrier restriction tuple of a (globally)
a.e.-`(1,Θ)`-elliptic carrier field, the carrier clamped observable reproduces
the fixed-phase observable exactly. -/
theorem clampedPhaseObservableR_restrict_eq_of_field [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K)
    (b : RegCoeffField d)
    (hbell : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (b x)) :
    clampedPhaseObservableR ℓ σ Θ m P K
        (fun k : {k // k ∈ K} =>
          restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) b)
      = phaseObservable ℓ σ m P b.toFun := by
  have hy : ∀ k : {k // k ∈ K},
      restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) b
        ∈ coreGoodSet ℓ σ Θ k.1 m :=
    fun k => restrictReg_mem_coreGoodSet hbell
  have hraw : rawPhaseObservableR ℓ σ Θ m P K
      (fun k : {k // k ∈ K} =>
        restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) b)
      = rawPhaseObservable ℓ σ Θ m P K
          (fun k : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k.val) b.toFun) := by
    rw [rawPhaseObservableR_eq_of_good P hy,
      show (fun k : {k // k ∈ K} =>
            (restrictReg (coreBox ℓ σ k.val) (measurableSet_coreBox ℓ σ k.val) b).toFun)
          = fun k : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k.val) b.toFun from
        funext fun k => restrictReg_toFun_eq _ _ b]
  unfold clampedPhaseObservableR
  rw [hraw,
    rawPhaseObservable_restrict_eq_of_field hℓ hΘ P K hK b.toFun
      (fun i j => b.entry_measurable i j) hbell]
  obtain ⟨hlo, hhi⟩ := phaseObservable_mem_Icc hΘ P
    (fun i j => b.entry_measurable i j) hbell
  rw [min_eq_right (by simpa [phaseBound] using hhi), max_eq_right hlo]

end Homogenization
