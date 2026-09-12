/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds

/-!
# Assembly of the actual primary tangent field

The native vector pulse, its integer periodization and covering, and its
complex harmonic use the same `PairData` as the covariance calculation.
The exact curl correction remains a separate field.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PrimaryFieldAssembly

open Set Function PartitionedCovariance HarmonicCalculus
open scoped BigOperators Topology

/-- Vector: an abbreviation for `Fin 3 → ℝ`. -/
abbrev Vector := Fin 3 → ℝ
/-- Signed index: an abbreviation for `UnsignedLabel × Fin 2`. -/
abbrev SignedIndex := UnsignedLabel × Fin 2

/-- The three components of one literal native pulse. -/
noncomputable def pulseVector (P : Pulse) (r : ℝ) (z : Plane) : Vector :=
  Fin.cases (P.radialProfile r z) (fun i => P.tangentProfile r i z)

@[simp] theorem pulseVector_zero (P : Pulse) (r : ℝ) (z : Plane) :
    pulseVector P r z 0 = P.radialProfile r z := rfl

@[simp] theorem pulseVector_succ (P : Pulse) (r : ℝ) (z : Plane) (i : Fin 2) :
    pulseVector P r z i.succ = P.tangentProfile r i z := rfl

private theorem compact_vector {f : Plane → Vector}
    (hf : ∀ i, HasCompactSupport (fun z => f z i)) : HasCompactSupport f := by
  apply HasCompactSupport.intro (isCompact_iUnion (fun i => (hf i).isCompact))
  intro z hz
  funext i
  by_contra hi
  apply hz
  exact mem_iUnion.mpr ⟨i, subset_tsupport (fun z => f z i) hi⟩

variable {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}

/-- The vector is placed at the actual signed slot center, with exactly the
native chart and transverse stretch used in `PairData.rawRadial`. -/
noncomputable def nativeVector {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) : Plane → Vector :=
  TorusAverages.nativeField (TorusAverages.slotChart vr vt hdet)
    (slotCenter h (signedLabel U j))
    (TorusAverages.transverseStretch (P.ci j) sys.radius
      (pulseVector (P.pulses j) sys.radius))

@[simp] theorem nativeVector_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) :
    nativeVector P hdet j Y 0 = P.rawRadial hdet j Y := rfl

@[simp] theorem nativeVector_succ {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) (i : Fin 2) :
    nativeVector P hdet j Y i.succ = P.rawTangent hdet j i Y := rfl

theorem nativeVector_compact {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    HasCompactSupport (nativeVector P hdet j) := by
  apply compact_vector
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact P.rawRadial_compact hdet j
  · exact P.rawTangent_compact hdet j k

/-- Evaluation commutes with the actual lattice sum because its support is
finite at the evaluation point. -/
theorem periodize_apply {f : Plane → Vector} (hf : HasCompactSupport f)
    (Y : Plane) (i : Fin 3) :
    TorusAverages.periodize f Y i =
      TorusAverages.periodize (fun z => f z i) Y := by
  obtain ⟨s, hs⟩ := TorusAverages.finite_translates_on_ball hf ‖Y‖
  have hv : TorusAverages.periodize f Y =
      ∑ k ∈ s, f (TorusAverages.latticePoint k + Y) :=
    tsum_eq_sum (hs Y le_rfl)
  have hi : TorusAverages.periodize (fun z => f z i) Y =
      ∑ k ∈ s, f (TorusAverages.latticePoint k + Y) i := by
    apply tsum_eq_sum
    intro k hk
    change f (TorusAverages.latticePoint k + Y) i = 0
    rw [hs Y le_rfl k hk]
    rfl
  rw [hv, hi]
  simp only [Finset.sum_apply]

/-- The covering is the same integer linear map as the slot construction. -/
noncomputable def coveredVector {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) : Vector :=
  TorusAverages.periodize (nativeVector P hdet j)
    ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y)

@[simp] theorem coveredVector_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) :
    coveredVector P hdet j Y 0 =
      covered (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) Y := by
  unfold coveredVector covered
  rw [periodize_apply (nativeVector_compact P hdet j), cover_power_eq_iterate]
  rfl

@[simp] theorem coveredVector_succ {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) (i : Fin 2) :
    coveredVector P hdet j Y i.succ =
      covered (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) Y := by
  unfold coveredVector covered
  rw [periodize_apply (nativeVector_compact P hdet j), cover_power_eq_iterate]
  rfl

/-- The square roots, signed-label mask, and physical outer factor are
literal; no fresh choice of amplitudes is made when assembling the field. -/
noncomputable def slotAmplitude {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) : ComplexVector :=
  fun i => ((outer * amplitude ε (mask D U q x) P.matrix T j *
    coveredVector P hdet j Y i : ℝ) : ℂ)

/-- Slot phase, given by `(P.modes j : ℝ) * z.2 + P.phases j z.1`. -/
noncomputable def slotPhase {U : UnsignedLabel} (P : PairData sys U)
    (j : Fin 2) (z : Plane × ℝ) : ℝ := (P.modes j : ℝ) * z.2 + P.phases j z.1

/-- Real part of the actual complex harmonic carrying the periodized vector
pulse. Frequency one here records the full phase; `mode_identification`
below also accepts a frequency kept separately from its phase. -/
noncomputable def slotVelocity {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) : Vector :=
  fun i => (vectorMode 1 (slotPhase P j)
    (fun z => slotAmplitude P hdet outer ε T q x j z.1) (Y, θ) i).re

theorem real_vectorMode {X : Type*} (κ : ℝ) (Φ : X → ℝ) (a : X → Vector)
    (x : X) (i : Fin 3) :
    (vectorMode κ Φ (fun z j => (a z j : ℂ)) x i).re =
      a x i * Real.cos (κ * Φ x) := by
  simp [vectorMode, mode, carrier, phaseFactor, Complex.exp_re,
    Complex.mul_re, Complex.mul_im]

theorem slotVelocity_formula {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) (i : Fin 3) :
    slotVelocity P hdet outer ε T q x j Y θ i =
      outer * amplitude ε (mask D U q x) P.matrix T j *
        coveredVector P hdet j Y i * Real.cos ((P.modes j : ℝ) * θ + P.phases j Y) := by
  unfold slotVelocity slotAmplitude
  rw [real_vectorMode]
  simp only [one_mul, slotPhase]

@[simp] theorem slotVelocity_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) :
    slotVelocity P hdet outer ε T q x j Y θ 0 =
      P.radialWave hdet outer ε T q x j Y θ := by
  rw [slotVelocity_formula, coveredVector_zero]
  rfl

@[simp] theorem slotVelocity_succ {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) (i : Fin 2) :
    slotVelocity P hdet outer ε T q x j Y θ i.succ =
      P.tangentWave hdet outer ε T q x j i Y θ := by
  rw [slotVelocity_formula, coveredVector_succ]
  rfl

theorem slotVelocity_mask_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (hm : mask D U q x = 0)
    (j : Fin 2) (Y : Plane) (θ : ℝ) :
    slotVelocity P hdet outer ε T q x j Y θ = 0 := by
  funext i
  simp [slotVelocity_formula, amplitude, hm]

/-- The same finite set of signed labels works for all auxiliary points
and all angles at a positive physical point. -/
theorem finite_active_slots (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q)
    (x : SlotColoring.Position) :
    ∃ F : Finset SignedIndex, ∀ a : SignedIndex, a ∉ F →
      mask D (tailLabel N a.1) q x = 0 := by
  classical
  let hs := finite_active_masks D N hq x
  refine ⟨hs.toFinset.product Finset.univ, ?_⟩
  intro a ha
  by_contra hm
  exact ha (Finset.mem_product.mpr ⟨hs.mem_toFinset.mpr hm, Finset.mem_univ _⟩)

private theorem finsum_vector_apply {ι : Type*} (f : ι → Vector) (s : Finset ι)
    (hf : ∀ a, a ∉ s → f a = 0) (i : Fin 3) :
    (∑ᶠ a, f a) i = ∑ᶠ a, f a i := by
  classical
  have hv : (∑ᶠ a, f a) = ∑ a ∈ s, f a := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    by_contra hn
    exact ha (hf a hn)
  have hi : (∑ᶠ a, f a i) = ∑ a ∈ s, f a i := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    by_contra hn
    exact ha (by change f a i = 0; rw [hf a hn]; rfl)
  rw [hv, hi]
  simp only [Finset.sum_apply]

/-- Principal field, given by `∑ᶠ a : SignedIndex, slotVelocity (P a.1) hdet (outer a.1) (ε a.1)
(T a.1) q x a.2 Y θ`. -/
noncomputable def principalField {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) : Vector :=
  ∑ᶠ a : SignedIndex,
    slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ

theorem principalField_finite {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) :
    ∃ F : Finset SignedIndex, ∀ Y θ,
      principalField P hdet outer ε T q x Y θ =
        ∑ a ∈ F, slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ := by
  classical
  obtain ⟨F, hF⟩ := finite_active_slots D N hq x
  refine ⟨F, ?_⟩
  intro Y θ
  apply finsum_eq_sum_of_support_subset
  intro a ha
  by_contra hn
  exact ha (slotVelocity_mask_zero (P a.1) hdet _ _ _ q x (hF a hn) _ Y θ)

theorem principalField_apply {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) (i : Fin 3) :
    principalField P hdet outer ε T q x Y θ i =
      ∑ᶠ a : SignedIndex,
        slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ i := by
  obtain ⟨F, hF⟩ := finite_active_slots D N hq x
  exact finsum_vector_apply _ F
    (fun a ha => slotVelocity_mask_zero (P a.1) hdet _ _ _ q x (hF a ha) _ Y θ) i

theorem principalField_components {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) :
    principalField P hdet outer ε T q x Y θ 0 =
      assembledRadial P hdet outer ε T q x Y θ ∧
    ∀ i : Fin 2, principalField P hdet outer ε T q x Y θ i.succ =
      assembledTangent P hdet outer ε T q x i Y θ := by
  constructor
  · simp only [principalField_apply P hdet outer ε T hq x, slotVelocity_zero,
      assembledRadial]
  · intro i
    simp only [principalField_apply P hdet outer ε T hq x, slotVelocity_succ,
      assembledTangent]

/-- The angular integral and torus-square integral of this actual vector
field give the physical target, with the original inverse square roots. -/
theorem physical_principal_covariance (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (T0 : Vec2)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (P U).matrix (chartTarget h q N T0 U)) (i : Fin 2) :
    doubleAverage (fun Y θ =>
      principalField P hdet (physicalOuter h N) (physicalViscosity h N)
        (chartTarget h q N T0) q x Y θ 0 *
      principalField P hdet (physicalOuter h N) (physicalViscosity h N)
        (chartTarget h q N T0) q x Y θ i.succ) =
      q ^ (-velocityExponent h - 1 / 2) * T0 i := by
  simp_rw [(principalField_components P hdet _ _ _ hq x _ _).1,
    (principalField_components P hdet _ _ _ hq x _ _).2 i]
  exact physical_primary_covariance sys hdet N hN P hq hqN x T0 hcone i

/-! ## A single cutoff, before periodization -/

/-- Multiplication by a locally supported cutoff commutes with actual
periodization on an injective slot. No choice of a lattice copy is needed. -/
theorem periodize_smul_of_injective_support {S : Set Plane}
    (hS : InjOn TorusAverages.quotientPoint S) {ψ : Plane → ℝ} {a : Plane → Vector}
    (hψ : support ψ ⊆ S) (ha : support a ⊆ S) (Y : Plane) :
    TorusAverages.periodize ψ Y • TorusAverages.periodize a Y =
      TorusAverages.periodize (fun z => ψ z • a z) Y := by
  have hprod : support (fun z => ψ z • a z) ⊆ S := by
    intro z hz
    apply hψ
    intro he
    exact hz (by simp [he])
  by_cases hactive : ∃ k : TorusInverse.Frequency, ψ (TorusAverages.latticePoint k + Y) ≠ 0
  · obtain ⟨k, hk⟩ := hactive
    rw [TorusAverages.periodize_eq_native_copy hS hψ (hψ hk),
      TorusAverages.periodize_eq_native_copy hS ha (hψ hk),
      TorusAverages.periodize_eq_native_copy hS hprod (hψ hk)]
  · have hz : ∀ k : TorusInverse.Frequency, ψ (TorusAverages.latticePoint k + Y) = 0 := by
      simpa only [not_exists, not_not] using hactive
    simp [TorusAverages.periodize, hz]

/-- Primitive local factorization suffices to identify the coefficient
after applying its single cutoff. This is not an assumed covariance or
assembled-field identity. -/
theorem cutoff_periodized_coefficient {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2)
    (ψ : Plane → ℝ) (a : Plane → Vector)
    (hψ : support ψ ⊆ slotSet h sys.radius vr vt (signedLabel U j))
    (ha : support a ⊆ slotSet h sys.radius vr vt (signedLabel U j))
    (hlocal : ∀ z, ψ z • a z = nativeVector P hdet j z)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (Y : Plane) :
    TorusAverages.periodize ψ ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y) •
      (fun i => ((outer * amplitude ε (mask D U q x) P.matrix T j *
        TorusAverages.periodize a
          ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y) i : ℝ) : ℂ)) =
      slotAmplitude P hdet outer ε T q x j Y := by
  have hh := periodize_smul_of_injective_support (sys.injective (signedLabel U j)) hψ ha
    ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y)
  have he : (fun z => ψ z • a z) = nativeVector P hdet j := funext hlocal
  rw [he] at hh
  funext i
  have hi := congrFun hh i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  simp only [Pi.smul_apply, Complex.real_smul, slotAmplitude, coveredVector]
  rw [← hi]
  push_cast
  ring

/-- Identification with any actual frequency/phase presentation of the
same harmonic, including the frequency convention of `WaveCoefficients`. -/
theorem mode_identification {X : Type*} (κ : ℝ) (Φ : X → ℝ)
    (a : X → ComplexVector) (z : X) {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ)
    (ha : a z = slotAmplitude P hdet outer ε T q x j Y)
    (hphase : κ * Φ z = slotPhase P j (Y, θ)) :
    (fun i => (vectorMode κ Φ a z i).re) =
      slotVelocity P hdet outer ε T q x j Y θ := by
  funext i
  have ha' := congrFun ha i
  rw [slotVelocity_formula]
  unfold vectorMode mode
  dsimp only
  rw [ha']
  change (((outer * amplitude ε (mask D U q x) P.matrix T j *
    coveredVector P hdet j Y i : ℝ) : ℂ) * carrier κ Φ z).re = _
  have hr := real_vectorMode κ Φ
    (fun _ => fun k => outer * amplitude ε (mask D U q x) P.matrix T j *
      coveredVector P hdet j Y k) z i
  change (((outer * amplitude ε (mask D U q x) P.matrix T j *
    coveredVector P hdet j Y i : ℝ) : ℂ) * carrier κ Φ z).re = _ at hr
  rw [hr, hphase]
  rfl

/-- The phase in the manuscript gives precisely the recorded integer
angular mode and the recorded slow phase remainder. -/
theorem actual_phase_identification (k ε p pz x0 : ℝ)
    (F G : PhaseCalculus.Slow → ℝ) (s : PhaseCalculus.Slow)
    (v : Plane → ℝ) (m : ℤ) (hm : k * p = (m : ℝ)) (Y : Plane) (θ : ℝ) :
    k * PhaseCalculus.phase ε p pz x0 F G (s, θ, v Y) =
      (m : ℝ) * θ + k * ((pz / ε) * s.2.1 + x0 * s.1 -
        v Y * (p * F s + pz * G s)) := by
  unfold PhaseCalculus.phase
  rw [← hm]
  ring

/-- The rounded angular frequency is the exact same nonzero integer as in
the pair data; this identity does not use an approximate rounding bound. -/
theorem rounded_phase_identification (k ε target pz x0 : ℝ) (hk : k ≠ 0)
    (F G : PhaseCalculus.Slow → ℝ) (s : PhaseCalculus.Slow)
    (v : Plane → ℝ) (Y : Plane) (θ : ℝ) :
    k * PhaseCalculus.phase ε (PhaseEstimates.roundedFrequency k target) pz x0 F G
        (s, θ, v Y) =
      (PhaseEstimates.nonzeroRound (k * target) : ℝ) * θ +
        roundedPhaseRemainder k ε target pz x0 F G s v Y :=
  actual_phase_identification k ε _ pz x0 F G s v _
    (PhaseEstimates.roundedFrequency_integer hk target) Y θ

/-! ## The exact curl retains its covariance error -/

section CurlCorrection

open LinearWaveBounds WeightedClasses

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Cutoff velocity, defined pointwise by `(vectorMode (a.frequency n) (a.phase n)
((a.withCutoff ψ).amplitude n) x i).re`. -/
noncomputable def cutoffVelocity (a : WaveCoefficients X) (ψ : ℕ → X → ℝ)
    (n : ℕ) (x : X) : Vector :=
  fun i => (vectorMode (a.frequency n) (a.phase n)
    ((a.withCutoff ψ).amplitude n) x i).re

/-- Curl velocity, defined pointwise by `(vectorMode (a.frequency n) (a.phase n) ((a.withCutoff
ψ).curlCorrection s d n) x i).re`. -/
noncomputable def curlVelocity (a : WaveCoefficients X) (s : StripData X)
    (d : GraphDirections X) (ψ : ℕ → X → ℝ) (n : ℕ) (x : X) : Vector :=
  fun i => (vectorMode (a.frequency n) (a.phase n)
    ((a.withCutoff ψ).curlCorrection s d n) x i).re

/-- Corrected velocity, defined pointwise by `(vectorMode (a.frequency n) (a.phase n)
((a.corrected s d ψ).amplitude n) x i).re`. -/
noncomputable def correctedVelocity (a : WaveCoefficients X) (s : StripData X)
    (d : GraphDirections X) (ψ : ℕ → X → ℝ) (n : ℕ) (x : X) : Vector :=
  fun i => (vectorMode (a.frequency n) (a.phase n)
    ((a.corrected s d ψ).amplitude n) x i).re

theorem correctedVelocity_split (a : WaveCoefficients X) (s : StripData X)
    (d : GraphDirections X) (ψ : ℕ → X → ℝ) (n : ℕ) (x : X) :
    correctedVelocity a s d ψ n x = cutoffVelocity a ψ n x + curlVelocity a s d ψ n x := by
  funext i
  simp [correctedVelocity, cutoffVelocity, curlVelocity, WaveCoefficients.corrected,
    WaveCoefficients.addAmplitude, vectorMode, mode, add_mul]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem cutoffVelocity_identification (a : WaveCoefficients X) (ψ : ℕ → X → ℝ)
    (n : ℕ) (z : X) {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ)
    (ha : (a.withCutoff ψ).amplitude n z = slotAmplitude P hdet outer ε T q x j Y)
    (hphase : a.frequency n * a.phase n z = slotPhase P j (Y, θ)) :
    cutoffVelocity a ψ n z = slotVelocity P hdet outer ε T q x j Y θ :=
  mode_identification (a.frequency n) (a.phase n) ((a.withCutoff ψ).amplitude n) z
    P hdet outer ε T q x j Y θ ha hphase

end CurlCorrection

/-- Covariance error, given by `V Y θ 0 * R Y θ i.succ + R Y θ 0 * V Y θ i.succ + R Y θ 0 * R Y
θ i.succ`. -/
noncomputable def covarianceError (V R : Plane → ℝ → Vector) (i : Fin 2)
    (Y : Plane) (θ : ℝ) : ℝ :=
  V Y θ 0 * R Y θ i.succ + R Y θ 0 * V Y θ i.succ + R Y θ 0 * R Y θ i.succ

theorem covariance_expansion (V R : Plane → ℝ → Vector) (i : Fin 2) (Y : Plane) (θ : ℝ) :
    (V Y θ + R Y θ) 0 * (V Y θ + R Y θ) i.succ =
      V Y θ 0 * V Y θ i.succ + covarianceError V R i Y θ := by
  simp only [Pi.add_apply, covarianceError]
  ring

private theorem continuous_angularMean {f : Plane → ℝ → ℝ}
    (hf : Continuous f.uncurry) : Continuous (fun Y => SmoothLoop.angularMean (f Y)) :=
  (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf
    0 (2 * Real.pi)).div_const _

private theorem squareAverage_add {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g) :
    TorusAverages.squareAverage (fun Y => f Y + g Y) =
      TorusAverages.squareAverage f + TorusAverages.squareAverage g := by
  rw [TorusAverages.squareAverage_eq_setIntegral (hf.fun_add hg),
    TorusAverages.squareAverage_eq_setIntegral hf, TorusAverages.squareAverage_eq_setIntegral hg]
  apply MeasureTheory.integral_add
  · exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  · exact (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)

theorem doubleAverage_add {f g : Plane → ℝ → ℝ}
    (hf : Continuous f.uncurry) (hg : Continuous g.uncurry) :
    doubleAverage (fun Y θ => f Y θ + g Y θ) = doubleAverage f + doubleAverage g := by
  unfold doubleAverage
  have he : (fun Y => SmoothLoop.angularMean (fun θ => f Y θ + g Y θ)) =
      fun Y => SmoothLoop.angularMean (f Y) + SmoothLoop.angularMean (g Y) := by
    funext Y
    apply SmoothLoop.angularMean_add
    · exact hf.comp (continuous_const.prodMk continuous_id)
    · exact hg.comp (continuous_const.prodMk continuous_id)
  rw [he]
  exact squareAverage_add (continuous_angularMean hf) (continuous_angularMean hg)

/-- The covariance of the exact curl has three explicitly retained error
products, rather than being identified with the principal covariance. -/
theorem averaged_covariance_expansion (V R : Plane → ℝ → Vector)
    (hV : Continuous V.uncurry) (hR : Continuous R.uncurry) (i : Fin 2) :
    doubleAverage (fun Y θ => (V Y θ + R Y θ) 0 * (V Y θ + R Y θ) i.succ) =
      doubleAverage (fun Y θ => V Y θ 0 * V Y θ i.succ) +
        doubleAverage (covarianceError V R i) := by
  simp_rw [covariance_expansion]
  apply doubleAverage_add
  · exact ((continuous_apply 0).comp hV).mul ((continuous_apply i.succ).comp hV)
  · exact ((((continuous_apply 0).comp hV).mul ((continuous_apply i.succ).comp hR)).add
      (((continuous_apply 0).comp hR).mul ((continuous_apply i.succ).comp hV))).add
        (((continuous_apply 0).comp hR).mul ((continuous_apply i.succ).comp hR))

/-! ## Canonical source data: actual ODE pulses and the same matrix -/

section Source

open PrimaryPulseBounds

variable {Q : Type} [NormedAddCommGroup Q]

/-- Primitive data for a signed pair of actual ODE pulses. No local field,
matrix, or covariance identity is a field of this structure. -/
structure SourcePair (Q : Type) [NormedAddCommGroup Q]
    {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt) (U : UnsignedLabel) where
  /-- Domain of `SourcePair`, of type `Set Q`. -/
  domain : Set Q
  /-- Point of `SourcePair`, of type `Q`. -/
  point : Q
  point_mem : point ∈ domain
  /-- Frame of `SourcePair`, of type `Fin 2 → PrimaryODE.FrameData Q`. -/
  frame : Fin 2 → PrimaryODE.FrameData Q
  /-- Lam of `SourcePair`, of type `Fin 2 → ℝ`. -/
  lam : Fin 2 → ℝ
  /-- Rate of `SourcePair`, of type `Fin 2 → ℝ`. -/
  rate : Fin 2 → ℝ
  /-- Length of `SourcePair`, of type `Fin 2 → ℝ`. -/
  length : Fin 2 → ℝ
  length_pos : ∀ j, 0 < length j
  coefficient_continuous : ∀ j,
    ContinuousOn ((frame j).coefficient 1) (domain ×ˢ Icc 0 (length j))
  kinematics : ∀ j, (frame j).Kinematics point (Icc 0 (length j))
  /-- Stretch of `SourcePair`, of type `Vec2`. -/
  stretch : Vec2
  stretch_pos : ∀ j, 0 < stretch j
  fits : ∀ j, length j ≤ 2 * sys.radius / stretch j
  /-- Mode of `SourcePair`, of type `Fin 2 → ℤ`. -/
  mode : Fin 2 → ℤ
  mode_ne : ∀ j, mode j ≠ 0
  /-- Phase of `SourcePair`, of type `Fin 2 → Plane → ℝ`. -/
  phase : Fin 2 → Plane → ℝ

namespace SourcePair

variable {U : UnsignedLabel} (A : SourcePair Q sys U)

/-- Pair data, bundling `pulses`, `ci`, `ci_pos`, `fits` and the required compatibility proofs. -/
noncomputable def pairData : PairData sys U where
  pulses := fun j => canonicalPrimaryPulse (A.frame j) (A.lam j) (A.rate j)
    (A.length_pos j) A.domain (A.coefficient_continuous j) A.point A.point_mem (A.kinematics j)
  ci := A.stretch
  ci_pos := A.stretch_pos
  fits := by
    intro j t ht
    have hmem : t ∈ Icc 0 (A.length j) := by
      by_contra hn
      exact ht (slotCutoff_zero_of_not_mem_Icc (A.length_pos j) hn)
    exact ⟨hmem.1, hmem.2.trans (A.fits j)⟩
  modes := A.mode
  modes_ne := A.mode_ne
  phases := A.phase

/-- The matrix is computed directly from the normalized ODE fundamentals,
with the exact determinant, transverse scale, and slot-length prefactor. -/
noncomputable def sourceMatrix : Mat2 :=
  primaryCovariance
    (fun j (_ : Unit) => nativePrefactor vr vt sys.radius * A.stretch j * A.length j)
    (fun j _ => A.frame j) (fun j _ => A.lam j) (fun j _ => A.rate j)
    (fun j _ => A.length j) () A.point

theorem sourceMatrix_eq : A.sourceMatrix = A.pairData.matrix := by
  exact primaryCovariance_eq_canonicalPairMatrix _ _ _ _ _ () A.domain A.point A.point_mem
    A.length_pos A.coefficient_continuous A.kinematics vr vt sys.radius A.stretch
    (fun _ => rfl)

theorem pulseVector_eq (j : Fin 2) (z : Plane) :
    pulseVector (A.pairData.pulses j) sys.radius z =
      fun i => localPrimaryProfile (A.frame j) (A.lam j) (A.rate j)
        (A.length j) sys.radius A.point z i := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact canonicalPrimaryPulse_radialProfile (A.frame j) (A.lam j) (A.rate j) sys.radius
      (A.length_pos j) A.domain (A.coefficient_continuous j) A.point A.point_mem (A.kinematics j) z
  · exact canonicalPrimaryPulse_tangentProfile (A.frame j) (A.lam j) (A.rate j) sys.radius
      (A.length_pos j) A.domain (A.coefficient_continuous j) A.point A.point_mem (A.kinematics j) z
          k

/-- The source vector is evaluated from `cutoffPulse`, rather than from
arbitrarily supplied radial and tangent component functions. -/
noncomputable def nativeSource (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (j : Fin 2) : Plane → Vector :=
  TorusAverages.nativeField (TorusAverages.slotChart vr vt hdet)
    (slotCenter h (signedLabel U j))
    (TorusAverages.transverseStretch (A.stretch j) sys.radius
      (fun z i => localPrimaryProfile (A.frame j) (A.lam j) (A.rate j)
        (A.length j) sys.radius A.point z i))

theorem nativeSource_eq (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    A.nativeSource hdet j = nativeVector A.pairData hdet j := by
  funext Y
  symm
  exact A.pulseVector_eq j _

/-- The native complex coefficient has the literal inverse-square-root
amplitude and a single local Gaussian cutoff. -/
noncomputable def nativeCoefficient (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) : ComplexVector :=
  fun i => ((outer * amplitude ε (mask D U q x) A.sourceMatrix T j *
    A.nativeSource hdet j Y i : ℝ) : ℂ)

/-- Actual amplitude, given by `TorusAverages.periodize (A.nativeCoefficient hdet outer ε T q x
j) ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y)`. -/
noncomputable def actualAmplitude (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) : ComplexVector :=
  TorusAverages.periodize (A.nativeCoefficient hdet outer ε T q x j)
    ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y)

end SourcePair

private theorem periodize_scaled_real_vector {f : Plane → Vector}
    (hf : HasCompactSupport f) (c : ℝ) (Y : Plane) (i : Fin 3) :
    TorusAverages.periodize (fun z => fun j => ((c * f z j : ℝ) : ℂ)) Y i =
      ((c * TorusAverages.periodize f Y i : ℝ) : ℂ) := by
  obtain ⟨s, hs⟩ := TorusAverages.finite_translates_on_ball hf ‖Y‖
  have hreal : TorusAverages.periodize f Y =
      ∑ k ∈ s, f (TorusAverages.latticePoint k + Y) := tsum_eq_sum (hs Y le_rfl)
  have hcomplex : TorusAverages.periodize (fun z => fun j => ((c * f z j : ℝ) : ℂ)) Y =
      ∑ k ∈ s, fun j => ((c * f (TorusAverages.latticePoint k + Y) j : ℝ) : ℂ) := by
    apply tsum_eq_sum
    intro k hk
    funext j
    simp [hs Y le_rfl k hk]
  rw [hreal, hcomplex]
  simp [Finset.sum_apply, Finset.mul_sum]

namespace SourcePair

variable {U : UnsignedLabel} (A : SourcePair Q sys U)

/-- The actual periodized complex coefficient equals the coefficient used
in the radial/tangent covariance assembly. -/
theorem actualAmplitude_eq (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) :
    A.actualAmplitude hdet outer ε T q x j Y =
      slotAmplitude A.pairData hdet outer ε T q x j Y := by
  unfold actualAmplitude nativeCoefficient
  rw [A.sourceMatrix_eq, A.nativeSource_eq]
  funext i
  exact periodize_scaled_real_vector (nativeVector_compact A.pairData hdet j) _ _ i

/-- Actual velocity, defined pointwise by `(vectorMode 1 (slotPhase A.pairData j) (fun z =>
A.actualAmplitude hdet outer ε T q x j z.1) (Y, θ) i).re`. -/
noncomputable def actualVelocity (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) (θ : ℝ) : Vector :=
  fun i => (vectorMode 1 (slotPhase A.pairData j)
    (fun z => A.actualAmplitude hdet outer ε T q x j z.1) (Y, θ) i).re

theorem actualVelocity_eq (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) (θ : ℝ) :
    A.actualVelocity hdet outer ε T q x j Y θ =
      slotVelocity A.pairData hdet outer ε T q x j Y θ := by
  apply mode_identification 1 (slotPhase A.pairData j)
    (fun z => A.actualAmplitude hdet outer ε T q x j z.1) (Y, θ)
  · exact A.actualAmplitude_eq hdet outer ε T q x j Y
  · simp

end SourcePair

/-- Source field, given by `∑ᶠ a : SignedIndex, (A a.1).actualVelocity hdet (outer a.1) (ε a.1)
(T a.1) q x a.2 Y θ`. -/
noncomputable def sourceField {N : ℕ}
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) : Vector :=
  ∑ᶠ a : SignedIndex,
    (A a.1).actualVelocity hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ

theorem sourceField_eq {N : ℕ}
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) :
    sourceField A hdet outer ε T q x Y θ =
      principalField (fun U => (A U).pairData) hdet outer ε T q x Y θ := by
  unfold sourceField principalField
  apply finsum_congr
  intro a
  exact (A a.1).actualVelocity_eq hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ

/-- End-to-end principal covariance for the actual ODE/source coefficient.
The assumed cone concerns its actual normalized ODE integral matrix. -/
theorem physical_source_covariance (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (T0 : Vec2)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (A U).sourceMatrix (chartTarget h q N T0 U)) (i : Fin 2) :
    doubleAverage (fun Y θ =>
      sourceField A hdet (physicalOuter h N) (physicalViscosity h N)
        (chartTarget h q N T0) q x Y θ 0 *
      sourceField A hdet (physicalOuter h N) (physicalViscosity h N)
        (chartTarget h q N T0) q x Y θ i.succ) =
      q ^ (-velocityExponent h - 1 / 2) * T0 i := by
  simp_rw [sourceField_eq]
  apply physical_principal_covariance sys hdet N hN _ hq hqN x T0 _ i
  intro U hU
  rw [← (A U).sourceMatrix_eq]
  exact hcone U hU

end Source

/-! ## Adapter to the actual `WaveCoefficients.withCutoff` field -/

section CoefficientAssembly

open LinearWaveBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Q : Type} [NormedAddCommGroup Q]

/-- Cutoff mode field, given by `∑ᶠ b : SignedIndex, cutoffVelocity (a b) (ψ b) (band b) (point
b Y θ)`. -/
noncomputable def cutoffModeField (a : SignedIndex → WaveCoefficients X)
    (ψ : SignedIndex → ℕ → X → ℝ) (band : SignedIndex → ℕ)
    (point : SignedIndex → Plane → ℝ → X) (Y : Plane) (θ : ℝ) : Vector :=
  ∑ᶠ b : SignedIndex, cutoffVelocity (a b) (ψ b) (band b) (point b Y θ)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The only bindings are the constructed coefficient and phase. The field
and its assembled covariance are conclusions of this adapter. -/
theorem cutoffModeField_eq_source {N : ℕ}
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (a : SignedIndex → WaveCoefficients X) (ψ : SignedIndex → ℕ → X → ℝ)
    (band : SignedIndex → ℕ) (point : SignedIndex → Plane → ℝ → X)
    (hcoeff : ∀ b Y θ, ((a b).withCutoff (ψ b)).amplitude (band b) (point b Y θ) =
      (A b.1).actualAmplitude hdet (outer b.1) (ε b.1) (T b.1) q x b.2 Y)
    (hphase : ∀ b Y θ, (a b).frequency (band b) * (a b).phase (band b) (point b Y θ) =
      slotPhase (A b.1).pairData b.2 (Y, θ)) (Y : Plane) (θ : ℝ) :
    cutoffModeField a ψ band point Y θ = sourceField A hdet outer ε T q x Y θ := by
  unfold cutoffModeField sourceField
  apply finsum_congr
  intro b
  rw [(A b.1).actualVelocity_eq]
  exact cutoffVelocity_identification (a b) (ψ b) (band b) (point b Y θ)
    (A b.1).pairData hdet (outer b.1) (ε b.1) (T b.1) q x b.2 Y θ
    ((hcoeff b Y θ).trans ((A b.1).actualAmplitude_eq hdet _ _ _ q x b.2 Y))
    (hphase b Y θ)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem cutoffModeField_physical_covariance (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (T0 : Vec2)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (A U).sourceMatrix (chartTarget h q N T0 U))
    (a : SignedIndex → WaveCoefficients X) (ψ : SignedIndex → ℕ → X → ℝ)
    (band : SignedIndex → ℕ) (point : SignedIndex → Plane → ℝ → X)
    (hcoeff : ∀ b Y θ, ((a b).withCutoff (ψ b)).amplitude (band b) (point b Y θ) =
      (A b.1).actualAmplitude hdet (physicalOuter h N b.1) (physicalViscosity h N b.1)
        (chartTarget h q N T0 b.1) q x b.2 Y)
    (hphase : ∀ b Y θ, (a b).frequency (band b) * (a b).phase (band b) (point b Y θ) =
      slotPhase (A b.1).pairData b.2 (Y, θ)) (i : Fin 2) :
    doubleAverage (fun Y θ => cutoffModeField a ψ band point Y θ 0 *
      cutoffModeField a ψ band point Y θ i.succ) =
      q ^ (-velocityExponent h - 1 / 2) * T0 i := by
  simp_rw [cutoffModeField_eq_source A hdet _ _ _ q x a ψ band point hcoeff hphase]
  exact physical_source_covariance sys hdet N hN A hq hqN x T0 hcone i

/-- A finite exact-curl assembly retains the sum of its actual curl
corrections. This applies before any covariance estimate is made. -/
theorem finite_corrected_field_split {ι : Type*} (F : Finset ι)
    (a : ι → WaveCoefficients X) (s : ι → WeightedClasses.StripData X)
    (d : ι → GraphDirections X) (ψ : ι → ℕ → X → ℝ)
    (band : ι → ℕ) (point : ι → X) :
    (∑ b ∈ F, correctedVelocity (a b) (s b) (d b) (ψ b) (band b) (point b)) =
      (∑ b ∈ F, cutoffVelocity (a b) (ψ b) (band b) (point b)) +
        ∑ b ∈ F, curlVelocity (a b) (s b) (d b) (ψ b) (band b) (point b) := by
  simp_rw [correctedVelocity_split]
  exact Finset.sum_add_distrib

end CoefficientAssembly

/-! ## The angular covariance is a genuine function on the auxiliary torus -/

private noncomputable def latticeCover (k : TorusInverse.Frequency) : TorusInverse.Frequency :=
  (3 * k.1 + k.2, k.1 + 5 * k.2)

private theorem covering_add_lattice (Y : Plane) (k : TorusInverse.Frequency) :
    TorusAverages.covering (Y + TorusAverages.latticePoint k) =
      TorusAverages.covering Y + TorusAverages.latticePoint (latticeCover k) := by
  ext <;> simp [TorusAverages.covering, TorusAverages.latticePoint, latticeCover] <;> ring

private theorem covering_iterate_add_lattice (n : ℕ) (Y : Plane) (k : TorusInverse.Frequency) :
    TorusAverages.covering^[n] (Y + TorusAverages.latticePoint k) =
      TorusAverages.covering^[n] Y + TorusAverages.latticePoint (latticeCover^[n] k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, covering_add_lattice,
        Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem covered_periodic (n : ℕ) (f : Plane → ℝ) (Y : Plane) (k : TorusInverse.Frequency) :
    covered n f (Y + TorusAverages.latticePoint k) = covered n f Y := by
  unfold covered
  rw [covering_iterate_add_lattice, TorusAverages.periodize_periodic]

theorem slot_cross_zero {N : ℕ} (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    {a b : SignedIndex} (hab : a ≠ b) (Y : Plane) (θ : ℝ) (i : Fin 2) :
    slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ 0 *
      slotVelocity (P b.1) hdet (outer b.1) (ε b.1) (T b.1) q x b.2 Y θ i.succ = 0 := by
  have hlevel (c : SignedIndex) : 1 ≤ (signedTailLabel N c).1 := by
    change 1 ≤ c.1.1 + N
    omega
  have hne : signedTailLabel N a ≠ signedTailLabel N b :=
    fun he => hab ((signedTailLabel_injective N) he)
  have hz := sys.wave_cross_zero (hlevel a) (hlevel b) hne
    ((P a.1).rawRadial_support hdet a.2) ((P b.1).rawTangent_support hdet b.2 i) hq x Y θ
    (outer a.1 * Real.sqrt (ε a.1) * SmoothCovariance.amplitudes (P a.1).matrix (T a.1) a.2)
    (outer b.1 * Real.sqrt (ε b.1) * SmoothCovariance.amplitudes (P b.1).matrix (T b.1) b.2)
    ((P a.1).modes a.2) ((P b.1).modes b.2) ((P a.1).phases a.2) ((P b.1).phases b.2)
  simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave, PairData.tangentWave,
    signedTailLabel, physicalMask_signedLabel, amplitude, mul_assoc] at hz ⊢
  exact hz

/-- Diagonal covariance as an element of `ℝ`. -/
noncomputable def diagonalCovariance {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (a : SignedIndex) (i : Fin 2) (Y : Plane) : ℝ :=
  (outer a.1 * amplitude (ε a.1) (mask D (tailLabel N a.1) q x) (P a.1).matrix (T a.1) a.2) ^ 2 *
    covered (SlotColoring.nativeIndex h (tailLabel N a.1).1) ((P a.1).rawRadial hdet a.2) Y *
      covered (SlotColoring.nativeIndex h (tailLabel N a.1).1) ((P a.1).rawTangent hdet a.2 i) Y *
          (1 / 2)

/-- Both off-diagonal elimination and angular integration are performed
on the actual finite active family, before descending to the torus. -/
theorem angular_principal_finite {N : ℕ} (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (i : Fin 2) :
    ∃ F : Finset SignedIndex, ∀ Y,
      SmoothLoop.angularMean (fun θ => principalField P hdet outer ε T q x Y θ 0 *
        principalField P hdet outer ε T q x Y θ i.succ) =
      ∑ a ∈ F, diagonalCovariance P hdet outer ε T q x a i Y := by
  classical
  obtain ⟨F, hF⟩ := principalField_finite P hdet outer ε T hq x
  refine ⟨F, ?_⟩
  intro Y
  have hprod (θ : ℝ) : principalField P hdet outer ε T q x Y θ 0 *
      principalField P hdet outer ε T q x Y θ i.succ =
      ∑ a ∈ F, slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ 0 *
        slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ i.succ := by
    simp only [hF Y θ, Finset.sum_apply]
    apply sum_product_diagonal
    intro a _ b _ hab
    exact slot_cross_zero hN P hdet outer ε T hq x hab Y θ i
  simp_rw [hprod]
  rw [angularMean_sum F]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave, PairData.tangentWave]
    exact angularMean_wave_product _ _ _ _ _ ((P a.1).modes_ne a.2) _ _
  · intro a _
    simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave, PairData.tangentWave]
    exact (wave_continuous_theta _ _ _ _ _ _).mul (wave_continuous_theta _ _ _ _ _ _)

theorem angular_principal_regular {N : ℕ} (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (i : Fin 2) :
    let f := fun Y => SmoothLoop.angularMean (fun θ =>
      principalField P hdet outer ε T q x Y θ 0 * principalField P hdet outer ε T q x Y θ i.succ)
    Continuous f ∧ ∀ Y k, f (Y + TorusAverages.latticePoint k) = f Y := by
  dsimp only
  obtain ⟨F, hF⟩ := angular_principal_finite hN P hdet outer ε T hq x i
  constructor
  · simp_rw [hF]
    apply continuous_finsetSum
    intro a _
    exact ((continuous_const.mul
      (covered_continuous ((P a.1).rawRadial_continuous hdet a.2)
        ((P a.1).rawRadial_compact hdet a.2) _)).mul
          (covered_continuous ((P a.1).rawTangent_continuous hdet a.2 i)
            ((P a.1).rawTangent_compact hdet a.2 i) _)).mul continuous_const
  · intro Y k
    rw [hF, hF]
    apply Finset.sum_congr rfl
    intro a _
    unfold diagonalCovariance
    rw [covered_periodic, covered_periodic]

/-- The square average is exactly the Haar integral of the angular
covariance's continuous descent to the auxiliary torus. -/
theorem principal_torus_average {N : ℕ} (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (i : Fin 2) :
    ∃ g : C(TorusInverse.Torus, ℂ),
      (∀ Y, g (TorusAverages.quotientPoint Y) =
        ((SmoothLoop.angularMean (fun θ => principalField P hdet outer ε T q x Y θ 0 *
          principalField P hdet outer ε T q x Y θ i.succ) : ℝ) : ℂ)) ∧
      (∫ z, g z ∂TorusInverse.torusMeasure) =
        ((doubleAverage (fun Y θ => principalField P hdet outer ε T q x Y θ 0 *
          principalField P hdet outer ε T q x Y θ i.succ) : ℝ) : ℂ) := by
  obtain ⟨hc, hp⟩ := angular_principal_regular hN P hdet outer ε T hq x i
  let f : Plane → ℝ := fun Y => SmoothLoop.angularMean (fun θ =>
    principalField P hdet outer ε T q x Y θ 0 * principalField P hdet outer ε T q x Y θ i.succ)
  have hcc : Continuous (fun Y => (f Y : ℂ)) := Complex.continuous_ofReal.comp hc
  have hpc : SmoothFourierData.UnitPeriodic (fun Y => (f Y : ℂ)) := by
    intro Y k
    exact congrArg Complex.ofReal (hp Y k)
  let g := SmoothFourierData.descendContinuous (fun Y => (f Y : ℂ)) hcc hpc
  refine ⟨g, fun _ => rfl, ?_⟩
  rw [← TorusAverages.squareAverage_torusLift g]
  change TorusAverages.squareAverage (fun Y => (f Y : ℂ)) =
    ((TorusAverages.squareAverage f : ℝ) : ℂ)
  simp only [TorusAverages.squareAverage, ← intervalIntegral.integral_ofReal]

theorem physical_source_torus_covariance {Q : Type} [NormedAddCommGroup Q]
    (sys : SlotSystem D h vr vt) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (N : ℕ) (hN : 1 ≤ N) (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (T0 : Vec2)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (A U).sourceMatrix (chartTarget h q N T0 U)) (i : Fin 2) :
    ∃ g : C(TorusInverse.Torus, ℂ),
      (∀ Y, g (TorusAverages.quotientPoint Y) =
        ((SmoothLoop.angularMean (fun θ =>
          sourceField A hdet (physicalOuter h N) (physicalViscosity h N)
            (chartTarget h q N T0) q x Y θ 0 *
          sourceField A hdet (physicalOuter h N) (physicalViscosity h N)
            (chartTarget h q N T0) q x Y θ i.succ) : ℝ) : ℂ)) ∧
      (∫ z, g z ∂TorusInverse.torusMeasure) =
        ((q ^ (-velocityExponent h - 1 / 2) * T0 i : ℝ) : ℂ) := by
  obtain ⟨g, hg, hint⟩ := principal_torus_average hN (fun U => (A U).pairData) hdet
    (physicalOuter h N) (physicalViscosity h N) (chartTarget h q N T0) hq x i
  refine ⟨g, ?_, ?_⟩
  · simpa only [sourceField_eq] using hg
  · have hphys := physical_source_covariance sys hdet N hN A hq hqN x T0 hcone i
    simp only [sourceField_eq] at hphys
    rw [hphys] at hint
    exact hint

theorem nativeVector_continuous {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    Continuous (nativeVector P hdet j) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact P.rawRadial_continuous hdet j
  · exact P.rawTangent_continuous hdet j k

theorem slotVelocity_continuous {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (hphase : Continuous (P.phases j)) :
    Continuous (fun z : Plane × ℝ => slotVelocity P hdet outer ε T q x j z.1 z.2) := by
  have hcov : Continuous (coveredVector P hdet j) :=
    (TorusAverages.periodize_continuous (nativeVector_continuous P hdet j)
      (nativeVector_compact P hdet j)).comp (SlotGeometry.cover ^ SlotColoring.nativeIndex h
          U.1).continuous
  apply continuous_pi
  intro i
  simp only [slotVelocity_formula]
  exact (continuous_const.mul (((continuous_apply i).comp hcov).comp continuous_fst)).mul
    (Real.continuous_cos.comp ((continuous_const.mul continuous_snd).add (hphase.comp
        continuous_fst)))

theorem principalField_continuous {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (hphase : ∀ U j, Continuous ((P U).phases j)) :
    Continuous (fun z : Plane × ℝ => principalField P hdet outer ε T q x z.1 z.2) := by
  obtain ⟨F, hF⟩ := principalField_finite P hdet outer ε T hq x
  have he : (fun z : Plane × ℝ => principalField P hdet outer ε T q x z.1 z.2) =
      fun z => ∑ a ∈ F, slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 z.1 z.2 := by
    funext z
    exact hF z.1 z.2
  rw [he]
  exact continuous_finsetSum F (fun a _ =>
    slotVelocity_continuous (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 (hphase a.1 a.2))

/-- The physical covariance target belongs to the principal field. Adding
the actual curl remainder preserves all three covariance error terms. -/
theorem physical_source_plus_remainder {Q : Type} [NormedAddCommGroup Q]
    (sys : SlotSystem D h vr vt) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (N : ℕ) (hN : 1 ≤ N) (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (T0 : Vec2)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (A U).sourceMatrix (chartTarget h q N T0 U))
    (hphase : ∀ U j, Continuous ((A U).phase j))
    (R : Plane → ℝ → Vector) (hR : Continuous R.uncurry) (i : Fin 2) :
    let V := sourceField A hdet (physicalOuter h N) (physicalViscosity h N) (chartTarget h q N T0)
        q x
    doubleAverage (fun Y θ => (V Y θ + R Y θ) 0 * (V Y θ + R Y θ) i.succ) =
      q ^ (-velocityExponent h - 1 / 2) * T0 i + doubleAverage (covarianceError V R i) := by
  dsimp only
  have hV : Continuous (sourceField A hdet (physicalOuter h N) (physicalViscosity h N)
      (chartTarget h q N T0) q x).uncurry := by
    change Continuous (fun z : Plane × ℝ => sourceField A hdet (physicalOuter h N)
      (physicalViscosity h N) (chartTarget h q N T0) q x z.1 z.2)
    simp_rw [sourceField_eq]
    exact principalField_continuous (fun U => (A U).pairData) hdet _ _ _ hq x hphase
  rw [averaged_covariance_expansion _ R hV hR i,
    physical_source_covariance sys hdet N hN A hq hqN x T0 hcone i]

/-- Integer angular modes give actual full-turn periodicity. -/
theorem slotVelocity_angular_periodic {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) :
    slotVelocity P hdet outer ε T q x j Y (θ + 2 * Real.pi) =
      slotVelocity P hdet outer ε T q x j Y θ := by
  funext i
  simp only [slotVelocity_formula]
  congr 1
  rw [show (P.modes j : ℝ) * (θ + 2 * Real.pi) + P.phases j Y =
    ((P.modes j : ℝ) * θ + P.phases j Y) + (P.modes j : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_add_int_mul_two_pi _ _

theorem principalField_angular_periodic {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (Y : Plane) (θ : ℝ) :
    principalField P hdet outer ε T q x Y (θ + 2 * Real.pi) =
      principalField P hdet outer ε T q x Y θ := by
  unfold principalField
  apply finsum_congr
  intro a
  exact slotVelocity_angular_periodic (P a.1) hdet _ _ _ q x a.2 Y θ

/-- Full-field auxiliary periodicity uses the source phase convention.
The angular covariance's periodicity above needed no such hypothesis. -/
theorem principalField_auxiliary_periodic {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (hphase : ∀ U j Y k, (P U).phases j (Y + TorusAverages.latticePoint k) = (P U).phases j Y)
    (Y : Plane) (θ : ℝ) (k : TorusInverse.Frequency) :
    principalField P hdet outer ε T q x (Y + TorusAverages.latticePoint k) θ =
      principalField P hdet outer ε T q x Y θ := by
  unfold principalField
  apply finsum_congr
  intro a
  have hcov : coveredVector (P a.1) hdet a.2 (Y + TorusAverages.latticePoint k) =
      coveredVector (P a.1) hdet a.2 Y := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · simp only [coveredVector_zero, covered_periodic]
    · simp only [coveredVector_succ, covered_periodic]
  funext i
  simp only [slotVelocity_formula, hcov, hphase]

/-! ## Explicit conversion from chart velocity to physical velocity -/

theorem slotVelocity_outer_scale {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) :
    slotVelocity P hdet outer ε T q x j Y θ = outer • slotVelocity P hdet 1 ε T q x j Y θ := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, slotVelocity_formula]
  ring

theorem SourcePair.actualVelocity_outer_scale {Q : Type} [NormedAddCommGroup Q]
    {U : UnsignedLabel} (A : SourcePair Q sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) :
    A.actualVelocity hdet outer ε T q x j Y θ = outer • A.actualVelocity hdet 1 ε T q x j Y θ := by
  rw [A.actualVelocity_eq, A.actualVelocity_eq]
  exact slotVelocity_outer_scale A.pairData hdet outer ε T q x j Y θ

section PhysicalCoefficientAssembly

open LinearWaveBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Q : Type} [NormedAddCommGroup Q]

/-- Chart velocity is converted to physical velocity outside the chart
coefficient. The weighted class of the original coefficient is unchanged. -/
noncomputable def scaledCutoffModeField (outer : UnsignedLabel → ℝ)
    (a : SignedIndex → WaveCoefficients X) (ψ : SignedIndex → ℕ → X → ℝ)
    (band : SignedIndex → ℕ) (point : SignedIndex → Plane → ℝ → X)
    (Y : Plane) (θ : ℝ) : Vector :=
  ∑ᶠ b : SignedIndex, outer b.1 • cutoffVelocity (a b) (ψ b) (band b) (point b Y θ)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem scaledCutoffModeField_eq_source {N : ℕ}
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (a : SignedIndex → WaveCoefficients X) (ψ : SignedIndex → ℕ → X → ℝ)
    (band : SignedIndex → ℕ) (point : SignedIndex → Plane → ℝ → X)
    (hcoeff : ∀ b Y θ, ((a b).withCutoff (ψ b)).amplitude (band b) (point b Y θ) =
      (A b.1).actualAmplitude hdet 1 (ε b.1) (T b.1) q x b.2 Y)
    (hphase : ∀ b Y θ, (a b).frequency (band b) * (a b).phase (band b) (point b Y θ) =
      slotPhase (A b.1).pairData b.2 (Y, θ)) (Y : Plane) (θ : ℝ) :
    scaledCutoffModeField outer a ψ band point Y θ = sourceField A hdet outer ε T q x Y θ := by
  unfold scaledCutoffModeField sourceField
  apply finsum_congr
  intro b
  rw [(A b.1).actualVelocity_outer_scale]
  congr 1
  rw [(A b.1).actualVelocity_eq]
  exact cutoffVelocity_identification (a b) (ψ b) (band b) (point b Y θ)
    (A b.1).pairData hdet 1 (ε b.1) (T b.1) q x b.2 Y θ
    ((hcoeff b Y θ).trans ((A b.1).actualAmplitude_eq hdet 1 _ _ q x b.2 Y))
    (hphase b Y θ)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The physical factor is exactly `Q^(-A)` applied to each chart field.
It is not inserted into the coefficient before the chart wave estimates. -/
theorem scaledCutoffModeField_physical_covariance (sys : SlotSystem D h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) (T0 : Vec2)
    (hcone : ∀ U, mask D (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (A U).sourceMatrix (chartTarget h q N T0 U))
    (a : SignedIndex → WaveCoefficients X) (ψ : SignedIndex → ℕ → X → ℝ)
    (band : SignedIndex → ℕ) (point : SignedIndex → Plane → ℝ → X)
    (hcoeff : ∀ b Y θ, ((a b).withCutoff (ψ b)).amplitude (band b) (point b Y θ) =
      (A b.1).actualAmplitude hdet 1 (physicalViscosity h N b.1)
        (chartTarget h q N T0 b.1) q x b.2 Y)
    (hphase : ∀ b Y θ, (a b).frequency (band b) * (a b).phase (band b) (point b Y θ) =
      slotPhase (A b.1).pairData b.2 (Y, θ)) (i : Fin 2) :
    doubleAverage (fun Y θ => scaledCutoffModeField (physicalOuter h N) a ψ band point Y θ 0 *
      scaledCutoffModeField (physicalOuter h N) a ψ band point Y θ i.succ) =
      q ^ (-velocityExponent h - 1 / 2) * T0 i := by
  simp_rw [scaledCutoffModeField_eq_source A hdet _ _ _ q x a ψ band point hcoeff hphase]
  exact physical_source_covariance sys hdet N hN A hq hqN x T0 hcone i

theorem finite_scaled_corrected_field_split {ι : Type*} (F : Finset ι) (outer : ι → ℝ)
    (a : ι → WaveCoefficients X) (s : ι → WeightedClasses.StripData X)
    (d : ι → GraphDirections X) (ψ : ι → ℕ → X → ℝ)
    (band : ι → ℕ) (point : ι → X) :
    (∑ b ∈ F, outer b • correctedVelocity (a b) (s b) (d b) (ψ b) (band b) (point b)) =
      (∑ b ∈ F, outer b • cutoffVelocity (a b) (ψ b) (band b) (point b)) +
        ∑ b ∈ F, outer b • curlVelocity (a b) (s b) (d b) (ψ b) (band b) (point b) := by
  simp_rw [correctedVelocity_split, smul_add]
  exact Finset.sum_add_distrib

end PhysicalCoefficientAssembly

end NavierStokes.PrimaryFieldAssembly
