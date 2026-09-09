/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData

/-!
# Signed physical families with label-dependent phase domains

Each active primary label retains its own phase domain, primary data, views,
and state. Homogeneous singleton views permit reuse of the existing per-label
constructors. Physical copies are then assembled before the locally finite
sum is estimated; no maximum over infinitely many per-label constants occurs.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.DependentSignedPhysicalFamily

open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds
open WeightedClasses
open scoped Topology ContDiff BigOperators

/-- Native label: an abbreviation for `ActualSignedPhysicalData.NativeLabel`. -/
abbrev NativeLabel := ActualSignedPhysicalData.NativeLabel

/-- Only active labels carry primary data, and their phase domains may differ. -/
structure Family where
  /-- Active of `Family`, of type `Set BandLabel`. -/
  active : Set BandLabel
  /-- Domain of `Family`, of type `NativeLabel active → PhaseJetBounds.Domain ℕ
  PhaseCalculus.Slow`. -/
  domain : NativeLabel active → PhaseJetBounds.Domain ℕ PhaseCalculus.Slow
  /-- Primary of `Family`, of type `(L : NativeLabel active) → PhysicalSignedWave.PrimaryData
  (domain L)`. -/
  primary : (L : NativeLabel active) → PhysicalSignedWave.PrimaryData (domain L)
  /-- View of `Family`, of type `(L : NativeLabel active) → (primary L).Views L.val.1`. -/
  view : (L : NativeLabel active) → (primary L).Views L.val.1
  /-- State of `Family`, of type `(L : NativeLabel active) → (view L).StateData`. -/
  state : (L : NativeLabel active) → (view L).StateData
  /-- Column of `Family`, of type `NativeLabel active → Fin 2`. -/
  column : NativeLabel active → Fin 2

namespace Family

variable (f : Family)

/-- Singleton label, given by `⟨L.val, L.property, Set.mem_singleton _⟩`. -/
noncomputable def singletonLabel (L : NativeLabel f.active) :
    NativeLabel ({(L : BandLabel)} : Set BandLabel) :=
  ⟨L.val, L.property, Set.mem_singleton _⟩

theorem singleton_label_val (L : NativeLabel f.active)
    (K : NativeLabel ({(L : BandLabel)} : Set BandLabel)) : K.val = L.val :=
  congrArg Subtype.val (Set.mem_singleton_iff.mp K.mem)

/-- Singleton payload as an element of `(f.primary L).Views K.val.1, V.StateData`. -/
noncomputable def singletonPayload (L : NativeLabel f.active)
    (K : NativeLabel ({(L : BandLabel)} : Set BandLabel)) :
    Σ V : (f.primary L).Views K.val.1, V.StateData := by
  have hband : K.val.1 = L.val.1 := congrArg Prod.fst (f.singleton_label_val L K)
  rw [hband]
  exact ⟨f.view L, f.state L⟩

/-- Reuse the old homogeneous interface for exactly one actual label.
There is no choice of data for an omitted label. -/
noncomputable def singleton (L : NativeLabel f.active) :
    ActualSignedPhysicalData.SignedFamily (f.domain L) where
  active := {(L : BandLabel)}
  primary _ := f.primary L
  view K := (f.singletonPayload L K).1
  state K := (f.singletonPayload L K).2
  column _ := f.column L

@[simp] theorem singleton_active (L : NativeLabel f.active) :
    (f.singleton L).active = {(L : BandLabel)} := rfl

@[simp] theorem singleton_primary (L : NativeLabel f.active)
    (K : NativeLabel (f.singleton L).active) :
    (f.singleton L).primary K = f.primary L := rfl

@[simp] theorem singleton_view (L : NativeLabel f.active) :
    (f.singleton L).view (f.singletonLabel L) = f.view L := by
  rfl

@[simp] theorem singleton_state (L : NativeLabel f.active) :
    (f.singleton L).state (f.singletonLabel L) = f.state L := by
  rfl

@[simp] theorem singleton_column (L : NativeLabel f.active)
    (K : NativeLabel (f.singleton L).active) :
    (f.singleton L).column K = f.column L := rfl

theorem singleton_referenceRequest (L : NativeLabel f.active) :
    ((f.singleton L).state (f.singletonLabel L)).referenceRequest =
      (f.state L).referenceRequest := by
  rfl

theorem singleton_request (L : NativeLabel f.active) :
    ((f.singleton L).state (f.singletonLabel L)).request = (f.state L).request := by
  rfl

/-- Extend actual values by zero without extending their primary data. -/
noncomputable def valueAt {V : Type*} [Zero V]
    (value : NativeLabel f.active → V) (L : BandLabel) : V := by
  classical
  exact if hL : L ∈ f.active then value ⟨L.val, L.property, hL⟩ else 0

@[simp] theorem valueAt_active {V : Type*} [Zero V]
    (value : NativeLabel f.active → V) (L : NativeLabel f.active) :
    f.valueAt value L = value L := by
  classical
  simp only [valueAt, dite_eq_left L.mem]

theorem valueAt_inactive {V : Type*} [Zero V]
    (value : NativeLabel f.active → V) {L : BandLabel} (hL : L ∉ f.active) :
    f.valueAt value L = 0 := by
  classical
  simp only [valueAt, dite_eq_right hL]

end Family

/-! ## One physical copy family, selected label by label -/

variable {H : ℕ} {K : Type*}

/-- Zero copies, bundling `gap`, `carrier`, `amplitude`. -/
noncomputable def zeroCopies : CopyFamily H K where
  gap _ := 0
  carrier _ _ := ⟨0, 0, 0, 0, 0, fun _ => 0, fun _ => 0⟩
  amplitude _ _ _ := 0

@[simp] theorem zeroCopies_term (a h r0 : ℝ) (I : WaveIndex H) (k : K) :
    (zeroCopies : CopyFamily H K).term a h r0 I k = 0 := by
  funext w
  exact globalWave_eq_zero rfl

/-- Zero cells, bundling `cells`, `carrier`, `closed`, `locallyFinite` and the required
compatibility proofs. -/
noncomputable def zeroCells : SupportCells (zeroCopies : CopyFamily H K) where
  cells _ := {
    carrier := fun _ _ => ∅
    closed := fun _ _ => isClosed_empty
    locallyFinite := fun _ _ => ⟨univ, univ_mem, by simp⟩
    unique := fun _ _ _ _ hx _ => hx.elim }
  support _ _ _ hx := (hx rfl).elim

theorem zeroSupport {a b h r0 Z : ℝ} {Δ : ℕ} :
    LocalPhysicalCopyBounds.SupportData (zeroCopies : CopyFamily H K) a b h r0 Z Δ where
  gap_le _ := Nat.zero_le _
  gap_native _ := Nat.zero_le _
  angular_integer _ _ := ⟨0, by simp [zeroCopies]⟩
  geometry_support _ _ _ hx := (hx rfl).elim
  mask_support _ _ _ _ hx := (hx rfl).elim

theorem zeroSmooth {a h r0 : ℝ} :
    LocalPhysicalCopyBounds.SmoothData (zeroCopies : CopyFamily H K) a h r0 where
  amplitude _ _ _ _ _ := ⟨univ, isOpen_univ, mem_univ _, contDiffOn_const⟩
  profiles _ _ _ _ _ _ _ :=
    ⟨⟨univ, isOpen_univ, mem_univ _, contDiffOn_const⟩,
      ⟨univ, isOpen_univ, mem_univ _, contDiffOn_const⟩⟩

/-- Diagonal, bundling `gap`, `carrier`, `amplitude`. -/
noncomputable def diagonal (f : BandLabel → CopyFamily H K) : CopyFamily H K where
  gap L := (f L).gap L
  carrier k L := (f L).carrier k L
  amplitude k I := (f I.1).amplitude k I

@[simp] theorem diagonal_gap (f : BandLabel → CopyFamily H K) (L : BandLabel) :
    (diagonal f).gap L = (f L).gap L := rfl

@[simp] theorem diagonal_carrier (f : BandLabel → CopyFamily H K) (k : K) (L : BandLabel) :
    (diagonal f).carrier k L = (f L).carrier k L := rfl

@[simp] theorem diagonal_amplitude (f : BandLabel → CopyFamily H K) (k : K) (I : WaveIndex H) :
    (diagonal f).amplitude k I = (f I.1).amplitude k I := rfl

@[simp] theorem diagonal_term (f : BandLabel → CopyFamily H K) (a h r0 : ℝ)
    (I : WaveIndex H) (k : K) :
    (diagonal f).term a h r0 I k = (f I.1).term a h r0 I k := rfl

@[simp] theorem diagonal_periodized (f : BandLabel → CopyFamily H K) (a h r0 : ℝ)
    (I : WaveIndex H) :
    (diagonal f).periodized a h r0 I = (f I.1).periodized a h r0 I := rfl

theorem diagonal_sum (f : BandLabel → CopyFamily H K) (a h r0 : ℝ) (w : SpaceTime) :
    (diagonal f).sum a h r0 w = ∑ᶠ I : WaveIndex H, (f I.1).periodized a h r0 I w := rfl

/-- Diagonal cells, bundling `cells`, `support`. -/
noncomputable def diagonalCells (f : BandLabel → CopyFamily H K)
    (c : ∀ L, SupportCells (f L)) : SupportCells (diagonal f) where
  cells L := (c L).cells L
  support I k := (c I.1).support I k

@[simp] theorem diagonalCells_cells (f : BandLabel → CopyFamily H K)
    (c : ∀ L, SupportCells (f L)) (L : BandLabel) :
    (diagonalCells f c).cells L = (c L).cells L := rfl

theorem diagonalSupport (f : BandLabel → CopyFamily H K) {a b h r0 Z : ℝ} {Δ : ℕ}
    (s : ∀ L, LocalPhysicalCopyBounds.SupportData (f L) a b h r0 Z Δ) :
    LocalPhysicalCopyBounds.SupportData (diagonal f) a b h r0 Z Δ where
  gap_le L := (s L).gap_le L
  gap_native L := (s L).gap_native L
  angular_integer k L := (s L).angular_integer k L
  geometry_support k I := (s I.1).geometry_support k I
  mask_support k I := (s I.1).mask_support k I

theorem diagonalSmooth (f : BandLabel → CopyFamily H K) {a h r0 : ℝ}
    (s : ∀ L, LocalPhysicalCopyBounds.SmoothData (f L) a h r0) :
    LocalPhysicalCopyBounds.SmoothData (diagonal f) a h r0 where
  amplitude k I := (s I.1).amplitude k I
  profiles k I := (s I.1).profiles k I

/-- The assembled infinite family retains the original uniform overlap
bound and has a genuine local finite-sum identity. -/
theorem diagonal_sum_locally_finite (f : BandLabel → CopyFamily H K)
    {a b h r0 Z : ℝ} {Δ : ℕ}
    (s : ∀ L, LocalPhysicalCopyBounds.SupportData (f L) a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {w : SpaceTime} (hw : w ∈ preterminal) :
    ∃ t : Finset (WaveIndex H), t.card ≤ 2250 * (2 * H + 1) ∧
      (diagonal f).sum a h r0 =ᶠ[𝓝 w]
        fun y => ∑ I ∈ t, (f I.1).periodized a h r0 I y := by
  simpa only [diagonal_periodized] using
    (diagonalSupport f s).sum_locally_finite hh hh1 hw

theorem diagonal_sum_smooth (f : BandLabel → CopyFamily H K)
    {a b h r0 Z : ℝ} {Δ : ℕ}
    (c : ∀ L, SupportCells (f L))
    (s : ∀ L, LocalPhysicalCopyBounds.SupportData (f L) a b h r0 Z Δ)
    (sm : ∀ L, LocalPhysicalCopyBounds.SmoothData (f L) a h r0)
    (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ ((diagonal f).sum a h r0) preterminal :=
  (diagonalSupport f s).sum_smooth (diagonalSmooth f sm) (diagonalCells f c) ha hh hh1

namespace Family

variable (f : Family)

/-- The missing labels receive zero copies, never invented primary data. -/
noncomputable def copyAt (copies : NativeLabel f.active → CopyFamily H K)
    (L : BandLabel) : CopyFamily H K := by
  classical
  exact if hL : L ∈ f.active then copies ⟨L.val, L.property, hL⟩ else zeroCopies

@[simp] theorem copyAt_active (copies : NativeLabel f.active → CopyFamily H K)
    (L : NativeLabel f.active) : f.copyAt copies L = copies L := by
  classical
  simp only [copyAt, dite_eq_left L.mem]

theorem copyAt_inactive (copies : NativeLabel f.active → CopyFamily H K)
    {L : BandLabel} (hL : L ∉ f.active) :
    f.copyAt copies L = zeroCopies := by
  classical
  simp only [copyAt, dite_eq_right hL]

/-- Assembled, given by `diagonal (f.copyAt copies)`. -/
noncomputable def assembled (copies : NativeLabel f.active → CopyFamily H K) :
    CopyFamily H K := diagonal (f.copyAt copies)

theorem assembled_term_active (copies : NativeLabel f.active → CopyFamily H K)
    (L : NativeLabel f.active) (j : Harmonic H) (a h r0 : ℝ) (k : K) :
    (f.assembled copies).term a h r0 ((L : BandLabel), j) k =
      (copies L).term a h r0 ((L : BandLabel), j) k := by
  rw [assembled, diagonal_term, copyAt_active]

theorem assembled_term_inactive (copies : NativeLabel f.active → CopyFamily H K)
    (I : WaveIndex H) (hI : I.1 ∉ f.active) (a h r0 : ℝ) (k : K) :
    (f.assembled copies).term a h r0 I k = 0 := by
  rw [assembled, diagonal_term, copyAt_inactive f copies hI, zeroCopies_term]

/-- Branch cells as an element of `SupportCells (f.copyAt copies L)`. -/
noncomputable def branchCells (copies : NativeLabel f.active → CopyFamily H K)
    (c : ∀ L, SupportCells (copies L)) (L : BandLabel) :
    SupportCells (f.copyAt copies L) := by
  classical
  by_cases hL : L ∈ f.active
  · simp only [copyAt, dite_eq_left hL]
    exact c ⟨L.val, L.property, hL⟩
  · rw [f.copyAt_inactive copies hL]
    exact zeroCells

theorem branchSupport (copies : NativeLabel f.active → CopyFamily H K)
    {a b h r0 Z : ℝ} {Δ : ℕ}
    (s : ∀ L, LocalPhysicalCopyBounds.SupportData (copies L) a b h r0 Z Δ)
    (L : BandLabel) :
    LocalPhysicalCopyBounds.SupportData (f.copyAt copies L) a b h r0 Z Δ := by
  classical
  by_cases hL : L ∈ f.active
  · simp only [copyAt, dite_eq_left hL]
    exact s ⟨L.val, L.property, hL⟩
  · rw [f.copyAt_inactive copies hL]
    exact zeroSupport

theorem branchSmooth (copies : NativeLabel f.active → CopyFamily H K)
    {a h r0 : ℝ}
    (s : ∀ L, LocalPhysicalCopyBounds.SmoothData (copies L) a h r0)
    (L : BandLabel) :
    LocalPhysicalCopyBounds.SmoothData (f.copyAt copies L) a h r0 := by
  classical
  by_cases hL : L ∈ f.active
  · simp only [copyAt, dite_eq_left hL]
    exact s ⟨L.val, L.property, hL⟩
  · rw [f.copyAt_inactive copies hL]
    exact zeroSmooth

section SignedCopies

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h
    ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h)

/-- The exact native source belonging to a primary label. Uniform bounds
must hold jointly over this label and the native source index. -/
noncomputable def potentialSource (L : BandLabel) :
    ActualSignedPhysicalData.SourceIndex → ℕ → ActualSignedPhysicalData.Native →
      HarmonicCalculus.ComplexVector :=
  f.valueAt (fun L => ActualSignedPhysicalData.nativePotentialSource sys hh (f.singleton L)) L

/-- Pressure source, given by `f.valueAt (fun L => ActualSignedPhysicalData.nativePressureSource
sys hh (f.singleton L)) L`. -/
noncomputable def pressureSource (L : BandLabel) :
    ActualSignedPhysicalData.SourceIndex → ℕ → ActualSignedPhysicalData.Native → ℂ :=
  f.valueAt (fun L => ActualSignedPhysicalData.nativePressureSource sys hh (f.singleton L)) L

@[simp] theorem potentialSource_active (L : NativeLabel f.active) :
    f.potentialSource sys hh L =
      ActualSignedPhysicalData.nativePotentialSource sys hh (f.singleton L) :=
  f.valueAt_active _ L

@[simp] theorem pressureSource_active (L : NativeLabel f.active) :
    f.pressureSource sys hh L =
      ActualSignedPhysicalData.nativePressureSource sys hh (f.singleton L) :=
  f.valueAt_active _ L

/-- Potential copies, given by `f.assembled (fun L => ActualSignedPhysicalData.potentialFamily
sys hh (f.singleton L) i)`. -/
noncomputable def potentialCopies (i : Fin 3) :
    CopyFamily 1 TorusInverse.Frequency :=
  f.assembled (fun L => ActualSignedPhysicalData.potentialFamily sys hh (f.singleton L) i)

/-- Pressure copies, given by `f.assembled (fun L => ActualSignedPhysicalData.pressureFamily sys
hh (f.singleton L))`. -/
noncomputable def pressureCopies : CopyFamily 1 TorusInverse.Frequency :=
  f.assembled (fun L => ActualSignedPhysicalData.pressureFamily sys hh (f.singleton L))

/-- Native Cartesian rotation and the physical factor are retained
exactly by the dependent assembly. -/
theorem potential_amplitude_eq_source (i : Fin 3) (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint) :
    (f.potentialCopies sys hh i).amplitude k I x =
      (ChartScales.Q I.1.val.1 ^ (-h) : ℝ) •
        CartesianCopySource.rotatedSource (f.potentialSource sys hh I.1)
          (I, k) I.1.val.1 x i := by
  classical
  change (f.copyAt (fun L => ActualSignedPhysicalData.potentialFamily sys hh
    (f.singleton L) i) I.1).amplitude k I x = _
  by_cases hL : I.1 ∈ f.active
  · simp only [copyAt, potentialSource, valueAt, dite_eq_left hL]
    exact ActualSignedPhysicalData.potential_amplitude_eq_source sys hh
      (f.singleton ⟨I.1.val, I.1.property, hL⟩) i k I x
  · simp [copyAt, potentialSource, valueAt, hL, zeroCopies,
      CartesianCopySource.rotatedSource]

theorem pressure_amplitude_eq_source (k : TorusInverse.Frequency)
    (I : WaveIndex 1) (x : PhysicalGraphBounds.LiftPoint) :
    (f.pressureCopies sys hh).amplitude k I x =
      (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)) : ℝ) •
        f.pressureSource sys hh I.1 (I, k) I.1.val.1 (PhysicalClassBounds.cylindricalMap x) := by
  classical
  change (f.copyAt (fun L => ActualSignedPhysicalData.pressureFamily sys hh
    (f.singleton L)) I.1).amplitude k I x = _
  by_cases hL : I.1 ∈ f.active
  · simp only [copyAt, pressureSource, valueAt, dite_eq_left hL]
    exact ActualSignedPhysicalData.pressure_amplitude_eq_source sys hh
      (f.singleton ⟨I.1.val, I.1.property, hL⟩) k I x
  · simp [copyAt, pressureSource, valueAt, hL, zeroCopies]

theorem potential_periodized_active (L : NativeLabel f.active) (i : Fin 3)
    (a r0 : ℝ) :
    (f.potentialCopies sys hh i).periodized a h r0
        (ActualSignedPhysicalData.positiveIndex L) =
      (ActualSignedPhysicalData.potentialFamily sys hh (f.singleton L) i).periodized
        a h r0 (ActualSignedPhysicalData.positiveIndex L) := by
  change (diagonal (f.copyAt _)).periodized _ _ _ _ = _
  rw [diagonal_periodized]
  simp only [ActualSignedPhysicalData.positiveIndex, copyAt_active]

theorem pressure_periodized_active (L : NativeLabel f.active) (a r0 : ℝ) :
    (f.pressureCopies sys hh).periodized a h r0 (ActualSignedPhysicalData.positiveIndex L) =
      (ActualSignedPhysicalData.pressureFamily sys hh (f.singleton L)).periodized
        a h r0 (ActualSignedPhysicalData.positiveIndex L) := by
  change (diagonal (f.copyAt _)).periodized _ _ _ _ = _
  rw [diagonal_periodized]
  simp only [ActualSignedPhysicalData.positiveIndex, copyAt_active]

end SignedCopies

end Family

/-! ## Sources retain their label in a dependent index -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : BandLabel → Type*}

/-- Joint source, defined pointwise by `source I.1 I.2`. -/
noncomputable def jointSource {V : Type*}
    (source : (L : BandLabel) → ι L → ℕ → E → V) :
    (Σ L, ι L) → ℕ → E → V := fun I => source I.1 I.2

theorem localSourceBounds_slice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : StripData E} {h α : ℝ}
    {w : (L : BandLabel) → ι L → ℕ → E → ℝ}
    {source : (L : BandLabel) → ι L → ℕ → E → V}
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds s h α (jointSource w) (jointSource source))
    (L : BandLabel) :
    LocalPhysicalCopyBounds.LocalSourceBounds s h α (w L) (source L) where
  uniform := hs.uniform.reindex (Sigma.mk L)
  flat_geometry := hs.flat_geometry
  weight_le := by
    obtain ⟨c, hc, hb⟩ := hs.weight_le
    exact ⟨c, hc, fun i => hb ⟨L, i⟩⟩
  epsilon_eq := hs.epsilon_eq
  slow_le := hs.slow_le

/-! ## Native chart and carrier bounds are uniform before label selection -/

/-- Diagonal chart, bundling `sourceIndex`, `map`, `domain`, `open_domain` and the required
compatibility proofs. -/
noncomputable def diagonalChart (f : BandLabel → CopyFamily H K)
    (c : ∀ L, SupportCells (f L)) {a b h r0 σ : ℝ}
    (source : (L : BandLabel) → ι L → ℕ → E → ℂ)
    (ch : ∀ L, LocalPhysicalCopyBounds.CommonChart (f L) (c L) a b h r0 σ (source L))
    (hj : ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
      ∀ k I x, x ∈ (ch I.1).domain k I → ∀ j, 1 ≤ j → j ≤ m →
        ‖iteratedFDeriv ℝ j ((ch I.1).map k I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q) :
    LocalPhysicalCopyBounds.CommonChart (diagonal f) (diagonalCells f c)
      a b h r0 σ (jointSource source) where
  sourceIndex k I := ⟨I.1, (ch I.1).sourceIndex k I⟩
  map k I := (ch I.1).map k I
  domain k I := (ch I.1).domain k I
  open_domain k I := (ch I.1).open_domain k I
  smooth k I := (ch I.1).smooth k I
  positive_jets := hj
  amplitude_eq k I := (ch I.1).amplitude_eq k I
  contains k I := (ch I.1).contains k I

/-- Diagonal carrier, bundling `region`, `open_region`, `jets`, `contains`. -/
noncomputable def diagonalCarrier (f : BandLabel → CopyFamily H K)
    (c : ∀ L, SupportCells (f L)) {a b h r0 : ℝ}
    (bc : ∀ L, CarrierBounds (f L) (c L) a b h r0)
    (hj : PhaseJetBounds.PolynomialJets
      (copyBandDomain (fun k L => (bc L).region k L) (fun k L => (bc L).open_region k L))
      (fun I x => (((f I.2).carrier I.1 I.2).F x, ((f I.2).carrier I.1 I.2).G x))) :
    CarrierBounds (diagonal f) (diagonalCells f c) a b h r0 where
  region k L := (bc L).region k L
  open_region k L := (bc L).open_region k L
  jets := hj
  contains k I := (bc I.1).contains k I

/-- No native region is required for an omitted label whose amplitude
vanishes identically. -/
noncomputable def zeroCarrier {a b h r0 : ℝ} :
    CarrierBounds (zeroCopies : CopyFamily H K) zeroCells a b h r0 where
  region _ _ := ∅
  open_region _ _ := isOpen_empty
  jets := PhaseJetBounds.PolynomialJets.const_fixed (0 : ℝ × ℝ)
  contains _ _ _ _ _ _ hx := hx.elim

/-- Zero chart, bundling `sourceIndex`, `map`, `domain`, `open_domain` and the required
compatibility proofs. -/
noncomputable def zeroChart {ν : Type*} {a b h r0 σ : ℝ}
    (source : ν → ℕ → E → ℂ) (index : K → WaveIndex H → ν) :
    LocalPhysicalCopyBounds.CommonChart (zeroCopies : CopyFamily H K) zeroCells
      a b h r0 σ source where
  sourceIndex := index
  map _ _ _ := 0
  domain _ _ := ∅
  open_domain _ _ := isOpen_empty
  smooth _ _ := contDiffOn_const
  positive_jets _ := ⟨1, le_rfl, 0, fun _ _ _ hx => hx.elim⟩
  amplitude_eq _ _ _ hx := hx.elim
  contains _ _ _ _ _ _ hx _ := hx.elim

/-- In the actual Cartesian source adapter every local map is the identity.
Its common positive-jet bound is exactly one, with polynomial degree zero. -/
theorem identity_chart_jets
    (f : BandLabel → CopyFamily H K) (c : ∀ L, SupportCells (f L))
    {a b h r0 σ : ℝ}
    (source : (L : BandLabel) → ι L → ℕ → PhysicalGraphBounds.LiftPoint → ℂ)
    (ch : ∀ L, LocalPhysicalCopyBounds.CommonChart (f L) (c L) a b h r0 σ (source L))
    (hid : ∀ k I, (ch I.1).map k I = fun x => x) :
    ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
      ∀ k I x, x ∈ (ch I.1).domain k I → ∀ j, 1 ≤ j → j ≤ m →
        ‖iteratedFDeriv ℝ j ((ch I.1).map k I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q := by
  intro m
  refine ⟨1, le_rfl, 0, ?_⟩
  intro k I x _ j hj _
  rw [hid k I]
  simp only [pow_zero, mul_one]
  exact (PhysicalGraphBounds.norm_positive_jet_linear_le
      (ContinuousLinearMap.id ℝ PhysicalGraphBounds.LiftPoint) x hj).trans (by simp)

/-- Empty inactive charts do not alter the common bound for identity
charts of active labels. -/
theorem identity_or_empty_chart_jets
    (f : BandLabel → CopyFamily H K) (c : ∀ L, SupportCells (f L))
    {a b h r0 σ : ℝ}
    (source : (L : BandLabel) → ι L → ℕ → PhysicalGraphBounds.LiftPoint → ℂ)
    (ch : ∀ L, LocalPhysicalCopyBounds.CommonChart (f L) (c L) a b h r0 σ (source L))
    (hid : ∀ k I, (ch I.1).domain k I = ∅ ∨ (ch I.1).map k I = fun x => x) :
    ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
      ∀ k I x, x ∈ (ch I.1).domain k I → ∀ j, 1 ≤ j → j ≤ m →
        ‖iteratedFDeriv ℝ j ((ch I.1).map k I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q := by
  intro m
  refine ⟨1, le_rfl, 0, ?_⟩
  intro k I x hx j hj _
  rcases hid k I with he | hi
  · rw [he] at hx
    exact hx.elim
  · rw [hi]
    simp only [pow_zero, mul_one]
    exact (PhysicalGraphBounds.norm_positive_jet_linear_le
        (ContinuousLinearMap.id ℝ PhysicalGraphBounds.LiftPoint) x hj).trans (by simp)

/-! ## One application of the physical-family estimate -/

section Assembly

variable {J : Type*} {a b h r0 Z P0 α σ : ℝ} {Δ : ℕ}
  (s : StripData E)
  (f : J → BandLabel → CopyFamily H K)
  (c : ∀ i L, SupportCells (f i L))
  (source : (L : BandLabel) → ι L → ℕ → E → ℂ)
  (weight : (L : BandLabel) → ι L → ℕ → E → ℝ)
  (hsource : LocalPhysicalCopyBounds.LocalSourceBounds s h α
    (jointSource weight) (jointSource source))
  (ch : ∀ i L, LocalPhysicalCopyBounds.CommonChart (f i L) (c i L)
    a b h r0 σ (source L))
  (hchart : ∀ i m, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
    ∀ k I x, x ∈ (ch i I.1).domain k I → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j ((ch i I.1).map k I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q)
  (hmap : ∀ i k I, MapsTo ((ch i I.1).map k I) ((ch i I.1).domain k I) s.domain)
  (bc : ∀ i L, CarrierBounds (f i L) (c i L) a b h r0)
  (hphase : ∀ i, PhaseJetBounds.PolynomialJets
    (copyBandDomain (fun k L => (bc i L).region k L)
      (fun k L => (bc i L).open_region k L))
    (fun I x => (((f i I.2).carrier I.1 I.2).F x, ((f i I.2).carrier I.1 I.2).G x)))
  (hsupport : ∀ i L, LocalPhysicalCopyBounds.SupportData (f i L) a b h r0 Z Δ)
  (hsmooth : ∀ i L, LocalPhysicalCopyBounds.SmoothData (f i L) a h r0)
  (ha : 0 < a) (hr0 : 0 ≤ r0) (hZ : 0 ≤ Z) (hP : 1 ≤ P0)
  (hfrequency : ∀ i k L, |((f i L).carrier k L).angular| ≤ P0 ∧
    |((f i L).carrier k L).axial| ≤ P0 ∧ |((f i L).carrier k L).radial| ≤ P0)

/-- The physical factory is applied once to all labels. Its source and
phase bounds are jointly quantified; individual physical bounds are not
inputs to this constructor. -/
noncomputable def waveData : PhysicalStageBounds.WaveData h E (Σ L, ι L) K J where
  lowerRadius := a
  upperRadius := b
  nativeWidth := r0
  slowBound := Z
  frequencyBound := P0
  alpha := α
  shift := σ
  harmonics := H
  gapBound := Δ
  lower_pos := ha
  width_nonneg := hr0
  slow_nonneg := hZ
  frequency_one_le := hP
  strip := s
  weight := jointSource weight
  source := jointSource source
  source_bounds := hsource
  copies i := diagonal (f i)
  cells i := diagonalCells (f i) (c i)
  chart i := diagonalChart (f i) (c i) source (ch i) (hchart i)
  chart_maps := hmap
  carrier i := diagonalCarrier (f i) (c i) (bc i) (hphase i)
  support i := diagonalSupport (f i) (hsupport i)
  smooth i := diagonalSmooth (f i) (hsmooth i)
  frequencies := hfrequency

theorem waveData_copies (i : J) :
    (waveData s f c source weight hsource ch hchart hmap bc hphase
      hsupport hsmooth ha hr0 hZ hP hfrequency).copies i = diagonal (f i) := rfl

theorem waveData_scalar (i : J) :
    (waveData s f c source weight hsource ch hchart hmap bc hphase
      hsupport hsmooth ha hr0 hZ hP hfrequency).scalar i =
      (diagonal (f i)).sum a h r0 := rfl

include s c source weight hsource ch hchart hmap bc hphase hsupport hsmooth
  ha hr0 hZ hP hfrequency in
theorem physical_scalar_bound (hh : 0 < h) (hh1 : h < 1 / 2) (i : J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m ((diagonal (f i)).sum a h r0) w‖ ≤
        C * physicalQ h w ^ (h * α - PhysicalClassBounds.physicalLoss h σ m) :=
  (waveData s f c source weight hsource ch hchart hmap bc hphase
    hsupport hsmooth ha hr0 hZ hP hfrequency).scalar_bound hh hh1 i m

end Assembly

end NavierStokes.DependentSignedPhysicalFamily
