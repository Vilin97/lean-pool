/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalSignedWave

@[expose] public section

/-!
# Controls from the actual shared primary construction

The reference matrix, target, unit pulse, normal motion and action below
are computed from the same prepared primary family. Their native-copy
estimates have constants before all labels, bands and copies.
-/

noncomputable section

namespace NavierStokes.ActualSignedControl

open Set Function Filter PhaseJetBounds PrimaryPulseBounds PrimaryCopyBounds
open WeightedClasses PeriodizedWaveBounds
open scoped ContDiff Topology InnerProductSpace BigOperators

abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2
abbrev Space := ProblemStatement.Space

variable {ι Λ I D X E : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def phaseNormal {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ) : ι → D → Space :=
  fun i x => F.phase.normal i (PrimaryCopyBounds.phasePoint F χ i x)

noncomputable def phaseMotion {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ) : ι → D → Space :=
  fun i x => F.phase.velocity i (PrimaryCopyBounds.phasePoint F χ i x)

noncomputable def phaseAction {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ) :
    ι → D → Space →L[ℝ] Space :=
  fun i x => PrimaryCopyBridge.baseOperator (F.phase.F i (χ i x).1)
    (F.phase.shear i (PrimaryCopyBounds.phasePoint F χ i x))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem pulseMatrix_eq_phaseMatrix {U : Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) :
    pulseMatrix F pref χ = SignedWaveUpdate.phaseMatrix F pref χ := rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem pulseVector_eq_phaseFundamental {U : Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PhaseConstruction U) (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) :
    pulseVector F χ j = SignedWaveUpdate.phaseFundamental F χ j := rfl

/-- The three geometric jet estimates are obtained from the actual phase
construction, rather than being supplied for the pressure output. -/
theorem phase_geometry_jets {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i) (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1) :
    PolynomialJets V.toDomain (phaseNormal F χ) ∧
    PolynomialJets V.toDomain (phaseMotion F χ) ∧
    PolynomialJets V.toDomain (phaseAction F χ) ∧
    (∀ i x, x ∈ V.carrier i → F.b ≤ ‖phaseNormal F χ i x‖) ∧
    (∀ i x, x ∈ V.carrier i → ‖phaseNormal F χ i x‖ ≤ F.M ^ 2 + 3 * F.M) := by
  have hp := PrimaryCopyBounds.phasePoint_jets F χ hscale hχ
  have hm := PrimaryCopyBounds.phasePoint_maps F χ hmap
  have hb := F.phase.polynomial_jets U F.V F.openV F.baseF F.baseG
    F.r_pos F.one_le_M F.constants F.epsilon_ne F.radius F.slot
  have hN := ((EnvelopeJets.of_polynomial hb.1).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hNd := ((EnvelopeJets.of_polynomial hb.2.1).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hshear := ((EnvelopeJets.of_polynomial hb.2.2).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hF := ((EnvelopeJets.of_polynomial F.baseF).comp
    (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) hscale
    (fun i x hx => (hmap i x hx).1)).to_polynomial (fun _ _ _ => le_rfl)
  exact ⟨hN, hNd, (hF.pair hshear).clm PrimaryCopyBridge.baseOperatorFamily,
    fun i x hx => F.normal_range.1 i _ (hm i x hx),
    fun i x hx => F.normal_range.2 i _ (hm i x hx)⟩

/-- A proved reference certificate. The prepared-family constructor below
derives its target and mask estimates and all three scalar margins. -/
structure ReferenceBounds (V : JetDomain ι D) (U : Domain ι PhaseCalculus.Slow)
    (F : Fin 2 → PhaseConstruction U) (pref : Fin 2 → ι → ℝ)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) (T : ι → D → Vec2)
    (mask ζ : ι → D → ℝ) where
  scale : ∀ i, U.scale i = V.scale i
  coordinate_jets : PolynomialJets V.toDomain χ
  coordinate_mem : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1
  prefactor_jets : ∀ j, PolynomialJets U (fun i _ => pref j i)
  target_jets : ∀ q, NativeJets V ζ (fun i x => T i x q)
  mask_jets : PolynomialJets V.toDomain mask
  weight_pos : ∀ i x, x ∈ V.carrier i → 0 < ζ i x
  determinantGap : ℝ
  entryBound : ℝ
  primaryLower : ℝ
  gap_pos : 0 < determinantGap
  entry_one : 1 ≤ entryBound
  lower_pos : 0 < primaryLower
  zero_order : ∀ i x, x ∈ V.carrier i →
    PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (V.scale i))
      determinantGap entryBound primaryLower (ζ i x)
      (pulseMatrix F pref χ i x) (T i x)

namespace ReferenceBounds

variable {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
  {F : Fin 2 → PhaseConstruction U} {pref : Fin 2 → ι → ℝ}
  {χ : ι → D → PhaseCalculus.Slow × ℝ} {T : ι → D → Vec2} {mask ζ : ι → D → ℝ}
  (h : ReferenceBounds V U F pref χ T mask ζ)

include h

theorem matrix_jets (j k : Fin 2) :
    PolynomialJets V.toDomain (fun i x => pulseMatrix F pref χ i x j k) :=
  pulseMatrix_jets F pref χ h.scale h.coordinate_jets
    (fun i x hx => (h.coordinate_mem i x hx).1) h.prefactor_jets j k

theorem unit_jets (j : Fin 2) : NativeJets V (pulseEnvelope F χ j) (pulseVector F χ j) :=
  pulseVector_jets F χ h.scale h.coordinate_jets h.coordinate_mem j

theorem geometry_jets (j : Fin 2) :
    PolynomialJets V.toDomain (phaseNormal (F j) χ) ∧
    PolynomialJets V.toDomain (phaseMotion (F j) χ) ∧
    PolynomialJets V.toDomain (phaseAction (F j) χ) ∧
    (∀ i x, x ∈ V.carrier i → (F j).b ≤ ‖phaseNormal (F j) χ i x‖) ∧
    (∀ i x, x ∈ V.carrier i → ‖phaseNormal (F j) χ i x‖ ≤ (F j).M ^ 2 + 3 * (F j).M) :=
  phase_geometry_jets (F j) χ h.scale h.coordinate_jets h.coordinate_mem

theorem cutoff_jets : PolynomialJets V.toDomain
    (fun i x => GaussianTailFlat.profile (χ i x).2) := by
  apply (h.coordinate_jets.clm (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow ℝ)).compact_comp
    isOpen_univ GaussianTailFlat.profile_contDiff.contDiffOn isCompact_Icc (subset_univ _)
  intro i x hx
  exact ⟨(h.coordinate_mem i x hx).2.1.le, (h.coordinate_mem i x hx).2.2.le⟩

end ReferenceBounds

/-- Only affine coordinate geometry and weight/scale comparisons are
stored here. No copied field or copied derivative bound is an input. -/
structure CopyChart (s : StripData X) (V : JetDomain ι D) (ζ : ι → D → ℝ)
    (K : Λ → ℕ → I → Set X) where
  index : Λ → ℕ → ι
  linear : Λ → ℕ → I → X →L[ℝ] D
  shift : Λ → ℕ → I → D
  maps : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
    linear l n i x + shift l n i ∈ V.carrier (index l n)
  growthConstant : ℝ
  linearConstant : ℝ
  growth_one : 1 ≤ growthConstant
  linear_one : 1 ≤ linearConstant
  growthDegree : ℕ
  linearDegree : ℕ
  growth_bound : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
    V.growth (index l n) (linear l n i x + shift l n i) ≤
      growthConstant * s.growth n x ^ growthDegree
  linear_bound : ∀ l n i, ‖linear l n i‖ ≤ linearConstant * s.slow n ^ linearDegree
  weight_eq : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
    ζ (index l n) (linear l n i x + shift l n i) = s.zeta x
  ratioLower : ℝ
  ratioUpper : ℝ
  ratio_pos : 0 < ratioLower
  ratio_one : 1 ≤ ratioUpper
  scale_ratio : ∀ l n, ratioLower ≤ Real.sqrt (s.slow n) / Real.sqrt (V.scale (index l n)) ∧
    Real.sqrt (s.slow n) / Real.sqrt (V.scale (index l n)) ≤ ratioUpper

namespace CopyChart

variable {s : StripData X} {V : JetDomain ι D} {ζ : ι → D → ℝ}
  {K : Λ → ℕ → I → Set X} (c : CopyChart s V ζ K)

noncomputable def pull (f : ι → D → E) : Λ → ℕ → I → X → E :=
  affineCopy f c.index c.linear c.shift

theorem unweighted {f : ι → D → E} (hf : PolynomialJets V.toDomain f) :
    UniformLocalJets s (fun _ _ _ => 1) 0 K (c.pull f) := by
  apply (NativeJets.of_polynomial hf).copy_localJets s (fun _ _ _ => 1) 0
    c.index c.linear c.shift K (fun _ _ _ _ => zero_le_one) c.maps c.growth_one c.linear_one
    c.growthDegree c.linearDegree c.growth_bound c.linear_bound
  intro l n i x hx hi
  simp

theorem weighted {f : ι → D → E} (hf : NativeJets V ζ f) :
    UniformLocalJets s (fun _ _ x => s.zeta x) 0 K (c.pull f) := by
  apply hf.copy_localJets s (fun _ _ x => s.zeta x) 0 c.index c.linear c.shift K
    (fun _ _ x hx => s.zeta_nonneg x hx) c.maps c.growth_one c.linear_one
    c.growthDegree c.linearDegree c.growth_bound c.linear_bound
  intro l n i x hx hi
  simp only [Real.rpow_zero, one_mul, c.weight_eq l n i x hx hi, le_refl]

theorem envelope {w : ι → D → ℝ} {f : ι → D → E} (hf : NativeJets V w f)
    {W : Λ → ℕ → X → ℝ} (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hw : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      w (c.index l n) (c.linear l n i x + c.shift l n i) ≤ W l n x) :
    UniformLocalJets s W 0 K (c.pull f) := by
  apply hf.copy_localJets s W 0 c.index c.linear c.shift K hW c.maps c.growth_one c.linear_one
    c.growthDegree c.linearDegree c.growth_bound c.linear_bound
  simpa only [Real.rpow_zero, one_mul] using hw

end CopyChart

/-! ## The reference certificate is produced from the same actual profile -/

section Prepared

variable {F₀ : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F₀}
  (H₀ : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v₀ : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}

/-- Primitive local chart geometry for a selected prepared family.
The target, matrix, mask and pulse jets are not fields of this record. -/
structure PreparedChart (a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0)
    (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  native : JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) D
  slow : JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) PhaseCalculus.Slow
  coordinate : PrimaryGeometryAssembly.Index W₀ a.N → D → PhaseCalculus.Slow × ℝ
  scale : ∀ L, (PrimaryGeometryAssembly.domain W₀ a.N).scale L = native.scale L
  coordinate_jets : PolynomialJets native.toDomain coordinate
  maps : ∀ L x, x ∈ native.carrier L →
    coordinate L x ∈ (PrimaryGeometryAssembly.domain W₀ a.N).carrier L ×ˢ Ioo (0 : ℝ) 1
  positive : ∀ L x, x ∈ native.carrier L → (coordinate L x).1 ∈
    PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W₀)
  slow_maps : ∀ L x, x ∈ native.carrier L → (coordinate L x).1 ∈ slow.carrier L
  slow_growth : ∀ L x, x ∈ native.carrier L → slow.growth L (coordinate L x).1 ≤ native.growth L x
  radiusLower : ℝ
  normUpper : ℝ
  qLower : ℝ
  qUpper : ℝ
  radius_pos : 0 < radiusLower
  q_pos : 0 < qLower
  geometry : BaseChartJets.GeometryBounds slow.toDomain F₀.data.h radiusLower normUpper qLower
    qUpper
    (NominalConeAssembly.activeLeft W₀) (NominalConeAssembly.activeRight W₀)
  inverse_edge : ∀ L p, p ∈ slow.carrier L →
    (FinalSlowBase.edgeDistance W₀ (BaseChartJets.normalizedCoordinates F₀.data.h p).2)⁻¹ ≤
      slow.growth L p

namespace PreparedChart

variable {H₀ v₀}
  {a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0}
  (c : PreparedChart H₀ v₀ a D)

noncomputable def target : PrimaryGeometryAssembly.Index W₀ a.N → D → Vec2 :=
  fun L x k => PrimaryTargetBounds.actualTarget v₀ (c.coordinate L x).1 k

noncomputable def weight : PrimaryGeometryAssembly.Index W₀ a.N → D → ℝ :=
  fun L x => PrimaryTargetBounds.movingWeight W₀ (c.coordinate L x).1

noncomputable def mask : PrimaryGeometryAssembly.Index W₀ a.N → D → ℝ :=
  fun L x => PrimaryRepresentatives.nativeMask (PrimaryGeometryAssembly.label W₀ L).1
    (PrimaryGeometryAssembly.label W₀ L).2 (c.coordinate L x).1

theorem target_jets (hcone : LeadingStressWeights.FullTrueCone v₀) (k : Fin 2) :
    NativeJets c.native c.weight (fun L x => c.target L x k) := by
  have ht := (PrimaryCopyBounds.actualTarget_jets v₀ hcone c.slow
    c.radius_pos c.q_pos c.geometry c.inverse_edge).comp
    (c.coordinate_jets.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) c.slow_maps
      c.slow_growth
  exact ht.map (PiLp.proj 2 (fun _ : Fin 2 => ℝ) k)

theorem mask_jets : PolynomialJets c.native.toDomain c.mask := by
  apply nativeMask_comp_jets c.native.toDomain
    (fun L x => (c.coordinate L x).1)
    (c.coordinate_jets.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ))
    (fun L => (PrimaryGeometryAssembly.label W₀ L).1)
    (fun L => (PrimaryGeometryAssembly.label W₀ L).2)
    (fun L => L.val.property.1)
  intro L
  rw [← c.scale L]
  rfl

theorem weight_pos (L : PrimaryGeometryAssembly.Index W₀ a.N) {x : D}
    (hx : x ∈ c.native.carrier L) : 0 < c.weight L x := by
  have hs := c.slow_maps L x hx
  rw [weight, PrimaryTargetBounds.movingWeight_eq W₀ (c.geometry.time L _ hs)
    (c.radius_pos.trans_le (c.geometry.radius L _ hs))]
  apply ActiveAnnulusWeight.radialWeight_pos
  simp only [FinalSlowBase.logLeft, FinalSlowBase.logRight,
    Real.exp_log (NominalConeAssembly.activeLeft_pos W₀),
    Real.exp_log (FinalSlowBase.terminal_pos W₀)]
  exact c.geometry.x_range L _ hs

/-- Every jet field in this reference certificate is derived from the
actual prepared phase, actual leading target and actual grid mask. -/
noncomputable def referenceBounds (hcone : LeadingStressWeights.FullTrueCone v₀)
    (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)
    (dg eb il : ℝ) (hdg : 0 < dg) (heb : 1 ≤ eb) (hil : 0 < il)
    (hz : ∀ (L : PrimaryGeometryAssembly.Index W₀ a.N) (p : PhaseCalculus.Slow),
      p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W₀) →
      p ∈ (PrimaryGeometryAssembly.domain W₀ a.N).carrier L →
      PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
        dg eb il (PrimaryTargetBounds.movingWeight W₀ p)
        (PrimaryTargetBounds.preparedCovariance H₀ v₀ a vr vt L p)
        (fun k => PrimaryTargetBounds.actualTarget v₀ p k)) :
    ReferenceBounds c.native (PrimaryGeometryAssembly.domain W₀ a.N)
      (PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
      (preparedPrefactor r0 vr vt) c.coordinate c.target c.mask c.weight where
  scale := c.scale
  coordinate_jets := c.coordinate_jets
  coordinate_mem := c.maps
  prefactor_jets := fun j => preparedPrefactor_jets r0 vr vt a.N j
  target_jets := c.target_jets hcone
  mask_jets := c.mask_jets
  weight_pos := fun L _ hx => c.weight_pos L hx
  determinantGap := dg
  entryBound := eb
  primaryLower := il
  gap_pos := hdg
  entry_one := heb
  lower_pos := hil
  zero_order := by
    intro L x hx
    have h := hz L (c.coordinate L x).1 (c.positive L x hx) (c.maps L x hx).1
    have hscale : c.native.scale L = ChartScales.S (BaseChartJets.cellBand L) := (c.scale L).symm
    simp only [hscale, pulseMatrix, weight] at h ⊢
    exact h

end PreparedChart

/-- A supplied prepared family is only restricted to a later tail.
Every surviving phase and representative is the same one used by the
primary construction. No determinant or final control record is assumed. -/
theorem exists_referenceBounds (a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0)
    (hcone : LeadingStressWeights.FullTrueCone v₀) (hr0 : 0 < r0)
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    ∃ N : ℕ, ∃ hN : a.N ≤ N,
      ∀ c : PreparedChart H₀ v₀ (a.restrict N hN) D,
        Nonempty (ReferenceBounds c.native (PrimaryGeometryAssembly.domain W₀ N)
          (PrimaryGeometryAssembly.construction H₀ v₀ (a.restrict N hN) hr0)
          (preparedPrefactor r0 vr vt) c.coordinate c.target c.mask c.weight) := by
  obtain ⟨N, hN, dg, eb, il, hdg, heb, hil, hz⟩ :=
    PrimaryTargetBounds.exists_restricted_actual_bounds H₀ v₀ a hcone vr vt hdet hr0
  exact ⟨N, hN, fun c => ⟨c.referenceBounds hcone hr0 vr vt dg eb il hdg heb hil hz⟩⟩

end Prepared

/-! ## Transport through the actual affine views -/

/-- Positive band scalars with uniform primitive zeroth-order margins. -/
structure PositiveScale (Λ : Type) where
  value : Λ → ℕ → ℝ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_one : 1 ≤ upper
  bounds : ∀ l n, lower ≤ value l n ∧ value l n ≤ upper

namespace PositiveScale

variable (a b : PositiveScale Λ)

theorem value_pos (l : Λ) (n : ℕ) : 0 < a.value l n := a.lower_pos.trans_le (a.bounds l n).1

theorem bandBound (s : StripData X) : UniformPrimaryWeights.UniformBandBound s 0 a.value := by
  refine ⟨a.upper, zero_le_one.trans a.upper_one, 0, ?_⟩
  intro l n
  simpa only [Real.norm_eq_abs, abs_of_pos (a.value_pos l n), Real.rpow_zero,
    pow_zero, mul_one] using (a.bounds l n).2

theorem square_bandBound (s : StripData X) :
    UniformPrimaryWeights.UniformBandBound s 0 (fun l n => a.value l n ^ 2) := by
  refine ⟨a.upper ^ 2, sq_nonneg _, 0, ?_⟩
  intro l n
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a.value l n)), Real.rpow_zero,
    pow_zero, mul_one] using pow_le_pow_left₀ (a.value_pos l n).le (a.bounds l n).2 2

noncomputable def mul : PositiveScale Λ where
  value l n := a.value l n * b.value l n
  lower := a.lower * b.lower
  upper := a.upper * b.upper
  lower_pos := mul_pos a.lower_pos b.lower_pos
  upper_one := one_le_mul_of_one_le_of_one_le a.upper_one b.upper_one
  bounds l n := ⟨mul_le_mul (a.bounds l n).1 (b.bounds l n).1 b.lower_pos.le (a.value_pos l n).le,
    mul_le_mul (a.bounds l n).2 (b.bounds l n).2 (b.value_pos l n).le (zero_le_one.trans
      a.upper_one)⟩

end PositiveScale

theorem uniform_band_smul [Countable Λ] [Nonempty Λ]
    {s : StripData X} {K : Λ → ℕ → I → Set X} {w : Λ → ℕ → X → ℝ} {α β : ℝ}
    {f : Λ → ℕ → I → X → E} {r : Λ → ℕ → ℝ}
    (hf : UniformLocalJets s w α K f) (hr : UniformPrimaryWeights.UniformBandBound s β r)
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x) :
    UniformLocalJets s w (α + β) K (fun l n i x => r l n • f l n i x) := by
  let e := UniformPrimaryWeights.enumeration Λ
  apply SignedCopyBounds.uniform_local_of_pull (UniformPrimaryWeights.enumeration_surjective Λ)
  have hr' : UniformPrimaryWeights.UniformBandBound (UniformPrimaryWeights.reindexedStrip s e) β
      (fun (_ : I) k => r (e k).2 (e k).1) := by
    obtain ⟨C, hC, p, hb⟩ := hr
    exact ⟨C, hC, p, fun _ k => hb (e k).2 (e k).1⟩
  exact SignedCopyBounds.local_indexed_band_smul (SignedCopyBounds.local_pull hf e) hr'
    (fun k => hw (e k).2 (e k).1)

theorem uniform_local_congr {s : StripData X} {K : Λ → ℕ → I → Set X}
    {w : Λ → ℕ → X → ℝ} {α : ℝ} {f g : Λ → ℕ → I → X → E}
    (hf : UniformLocalJets s w α K f)
    (he : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → f l n i =ᶠ[𝓝 x] g l n i) :
    UniformLocalJets s w α K g := by
  refine ⟨fun l n i x hx hi => (hf.smooth l n i x hx hi).congr_of_eventuallyEq
    (he l n i x hx hi).symm, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro l n i x hx hi j hj
  rw [← PeriodizedWaveBounds.jets_eq_of_germ (he l n i x hx hi) j]
  exact hb l n i x hx hi j hj

/-- Changing the band's normalization and scaling the actual target
preserves quantitative Cramer margins with explicit constants. -/
theorem rescale_margins {r R dg eb il ζ c clo rlo rhi : ℝ} {H : Mat2} {T : Vec2}
    (h : PrimaryCovarianceBounds.ZeroOrderBounds r dg eb il ζ H T)
    (hr : 1 ≤ r) (hdg : 0 ≤ dg) (hil : 0 ≤ il) (hζ : 0 ≤ ζ) (hclo : 0 < clo) (hc : clo ≤ c)
    (hrlo : 0 < rlo) (hlo : rlo ≤ R / r) (hhi : R / r ≤ rhi) :
    rlo ^ 2 * dg ≤ |(normalizedMatrix R H).det| ∧
    (∀ i j, |R * H i j| ≤ rhi * eb) ∧
    (∀ j, (clo ^ 2 * il) * ζ ≤ SmoothCovariance.weights H (c ^ 2 • T) j) := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hratio : 0 < R / r := hrlo.trans_le hlo
  have he : normalizedMatrix R H = normalizedMatrix (R / r) (normalizedMatrix r H) := by
    ext i j
    simp only [normalizedMatrix]
    field_simp
  have hdet : |(normalizedMatrix R H).det| = (R / r) ^ 2 * |(normalizedMatrix r H).det| := by
    rw [he, normalizedMatrix_det, abs_mul, abs_of_nonneg (sq_nonneg _)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdet]
    exact mul_le_mul (pow_le_pow_left₀ hrlo.le hlo 2) h.determinant
      hdg (sq_nonneg _)
  · intro i j
    have hentry : R * H i j = (R / r) * (r * H i j) := by field_simp
    rw [hentry, abs_mul, abs_of_pos hratio]
    exact mul_le_mul hhi (h.entries i j) (abs_nonneg _) (by linarith [hratio, hhi])
  · intro j
    rw [PhysicalSignedWave.weights_smul_target, Pi.smul_apply, smul_eq_mul]
    have hbase : il * ζ ≤ SmoothCovariance.weights H T j := by
      apply le_trans _ (h.weights j)
      nlinarith [mul_nonneg hil hζ]
    have hh := mul_le_mul (pow_le_pow_left₀ hclo.le hc 2) hbase
      (mul_nonneg hil hζ) (sq_nonneg c)
    simpa only [mul_assoc] using hh

namespace ReferenceBounds

variable [Countable Λ] [Nonempty Λ]
  {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
  {F : Fin 2 → PhaseConstruction U} {pref : Fin 2 → ι → ℝ}
  {χ : ι → D → PhaseCalculus.Slow × ℝ} {T : ι → D → Vec2} {mask ζ : ι → D → ℝ}
  (h : ReferenceBounds V U F pref χ T mask ζ)
  {s : StripData X} {K : Λ → ℕ → I → Set X}
  (c : CopyChart s V ζ K) (scale : PositiveScale Λ)

/-- Construct the actual uniform native covariance record from the
derived reference jets and the primitive view geometry. -/
noncomputable def nativeCovariance (hzeta : ∀ x ∈ s.domain, 0 < s.zeta x) :
    SignedCopyBounds.UniformNativeCovariance s K
      (fun l i n => c.pull (pulseMatrix F pref χ) l n i)
      (fun l i n x => scale.value l n ^ 2 • c.pull T l n i x) where
  matrix_jets j k := c.unweighted (h.matrix_jets j k)
  target_jets q := by
    have ht := uniform_band_smul (c.weighted (h.target_jets q)) (scale.square_bandBound s)
      (fun _ _ x hx => s.zeta_nonneg x hx)
    simp only [zero_add] at ht
    exact ht
  zeta_pos := hzeta
  determinantGap := c.ratioLower ^ 2 * h.determinantGap
  entryBound := c.ratioUpper * h.entryBound
  primaryLower := scale.lower ^ 2 * h.primaryLower
  gap_pos := mul_pos (sq_pos_of_pos c.ratio_pos) h.gap_pos
  entry_one := one_le_mul_of_one_le_of_one_le c.ratio_one h.entry_one
  lower_pos := mul_pos (sq_pos_of_pos scale.lower_pos) h.lower_pos
  determinant := by
    intro l n i x hx hi
    have hz := h.zero_order (c.index l n) _ (c.maps l n i x hx hi)
    rw [c.weight_eq l n i x hx hi] at hz
    exact (rescale_margins hz (Real.one_le_sqrt.mpr (V.one_le_scale _)) h.gap_pos.le h.lower_pos.le
      (s.zeta_nonneg x hx) scale.lower_pos (scale.bounds l n).1 c.ratio_pos
      (c.scale_ratio l n).1 (c.scale_ratio l n).2).1
  entries := by
    intro l n i x hx hi
    have hz := h.zero_order (c.index l n) _ (c.maps l n i x hx hi)
    rw [c.weight_eq l n i x hx hi] at hz
    exact (rescale_margins hz (Real.one_le_sqrt.mpr (V.one_le_scale _)) h.gap_pos.le h.lower_pos.le
      (s.zeta_nonneg x hx) scale.lower_pos (scale.bounds l n).1 c.ratio_pos
      (c.scale_ratio l n).1 (c.scale_ratio l n).2).2.1
  lower := by
    intro l n i x hx hi
    have hz := h.zero_order (c.index l n) _ (c.maps l n i x hx hi)
    rw [c.weight_eq l n i x hx hi] at hz
    exact (rescale_margins hz (Real.one_le_sqrt.mpr (V.one_le_scale _)) h.gap_pos.le h.lower_pos.le
      (s.zeta_nonneg x hx) scale.lower_pos (scale.bounds l n).1 c.ratio_pos
      (c.scale_ratio l n).1 (c.scale_ratio l n).2).2.2

/-- The requested copy-level `NativeCovariance` is a projection of the
jointly proved record, retaining the same numerical margins. -/
noncomputable def nativeCovarianceAt (hzeta : ∀ x ∈ s.domain, 0 < s.zeta x) (l : Λ) :
    SignedCopyBounds.NativeCovariance s (K l)
      (fun i n => c.pull (pulseMatrix F pref χ) l n i)
      (fun i n x => scale.value l n ^ 2 • c.pull T l n i x) := by
  let hc := h.nativeCovariance c scale hzeta
  exact {
    matrix_jets := fun j k => (hc.matrix_jets j k).each l
    target_jets := fun j => (hc.target_jets j).each l
    zeta_pos := hc.zeta_pos
    determinantGap := hc.determinantGap
    entryBound := hc.entryBound
    primaryLower := hc.primaryLower
    gap_pos := hc.gap_pos
    entry_one := hc.entry_one
    lower_pos := hc.lower_pos
    determinant := hc.determinant l
    entries := hc.entries l
    lower := hc.lower l }

include h

omit [Countable Λ] [Nonempty Λ] in
theorem copied_unit_jets (j : Fin 2) {W : Λ → ℕ → X → ℝ}
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (henv : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      c.pull (pulseEnvelope F χ j) l n i x ≤ W l n x) :
    UniformLocalJets s W 0 K (c.pull (pulseVector F χ j)) :=
  c.envelope (h.unit_jets j) hW henv

/-- The modeled normal, normal motion and action are the transported
ones from the selected primary phase, with its actual clock factors. -/
theorem copied_geometry_jets (normal clock : PositiveScale Λ) (j : Fin 2) :
    UniformLocalJets s (fun _ _ _ => 1) 0 K
      (fun l n i x => normal.value l n • c.pull (phaseNormal (F j) χ) l n i x) ∧
    UniformLocalJets s (fun _ _ _ => 1) 0 K
      (fun l n i x => (normal.value l n * clock.value l n) • c.pull (phaseMotion (F j) χ) l n i x) ∧
    UniformLocalJets s (fun _ _ _ => 1) 0 K
      (fun l n i x => clock.value l n • c.pull (phaseAction (F j) χ) l n i x) := by
  have hg := h.geometry_jets j
  refine ⟨?_, ?_, ?_⟩
  · simpa only [zero_add] using uniform_band_smul (c.unweighted hg.1) (normal.bandBound s)
      (fun _ _ _ _ => zero_le_one)
  · simpa only [zero_add, PositiveScale.mul] using
      uniform_band_smul (c.unweighted hg.2.1) ((normal.mul clock).bandBound s)
        (fun _ _ _ _ => zero_le_one)
  · simpa only [zero_add] using uniform_band_smul (c.unweighted hg.2.2.1) (clock.bandBound s)
      (fun _ _ _ _ => zero_le_one)

omit [Countable Λ] [Nonempty Λ] in
theorem copied_normal_bounds (normal : PositiveScale Λ) (j : Fin 2)
    (l : Λ) (n : ℕ) (i : I) {x : X} (hx : x ∈ s.domain) (hi : x ∈ K l n i) :
    normal.lower * (F j).b ≤ ‖normal.value l n • c.pull (phaseNormal (F j) χ) l n i x‖ ∧
    ‖normal.value l n • c.pull (phaseNormal (F j) χ) l n i x‖ ≤
      normal.upper * ((F j).M ^ 2 + 3 * (F j).M) := by
  have hg := h.geometry_jets j
  have hlo := hg.2.2.2.1 (c.index l n) _ (c.maps l n i x hx hi)
  have hhi := hg.2.2.2.2 (c.index l n) _ (c.maps l n i x hx hi)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (normal.value_pos l n)]
  exact ⟨mul_le_mul (normal.bounds l n).1 hlo (F j).b_pos.le (normal.value_pos l n).le,
    mul_le_mul (normal.bounds l n).2 hhi (norm_nonneg _) (zero_le_one.trans normal.upper_one)⟩

end ReferenceBounds

/-- The carrier bound is derived for any nonzero integral harmonic, with
one constant before both the label and the copy. -/
theorem harmonic_frequency_bound (s : StripData X)
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (harmonic : Λ → ℕ → ℤ) (hn : ∀ l n, harmonic l n ≠ 0)
    (hf : ∀ l i n, (base l i).frequency n = CurlClassBounds.carrierFrequency s n * (harmonic l n :
      ℝ)) :
    UniformPrimaryWeights.UniformBandBound s (1 / 2)
      (fun li : Λ × I => fun n => 1 / (base li.1 li.2).frequency n) := by
  obtain ⟨C, hC, p, hb⟩ := UniformPrimaryWeights.harmonic_inverse_bandBound s harmonic hn
  exact ⟨C, hC, p, fun li n => by dsimp only; rw [hf]; exact hb li.1 n⟩

namespace ReferenceBounds

variable [Countable Λ] [Nonempty Λ]
  {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
  {F : Fin 2 → PhaseConstruction U} {pref : Fin 2 → ι → ℝ}
  {χ : ι → D → PhaseCalculus.Slow × ℝ} {T : ι → D → Vec2} {mask ζ : ι → D → ℝ}
  (h : ReferenceBounds V U F pref χ T mask ζ)
  {s : StripData X} {K : Λ → ℕ → I → Set X}
  (c : CopyChart s V ζ K) (scale normal clock : PositiveScale Λ)

/-- Exact functional form of the transported shared-reference signed
constructor, including the target square and the pressure clock factors. -/
noncomputable def copiedCoefficients
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (dirs : Λ → I → LinearWaveBounds.GraphDirections X)
    (request : ℕ → X → Vec2) (j : Fin 2) (l : Λ) (i : I) :
    LinearWaveBounds.WaveCoefficients X :=
  SignedWaveUpdate.coefficients (base l i) s (dirs l i)
    (fun n => c.pull (pulseMatrix F pref χ) l n i)
    (fun n x => scale.value l n ^ 2 • c.pull T l n i x) request
    (fun n => c.pull mask l n i) (fun n => c.pull (pulseVector F χ j) l n i)
    (fun n x => (normal.value l n * clock.value l n) • c.pull (phaseMotion (F j) χ) l n i x)
    (fun n x => clock.value l n • c.pull (phaseAction (F j) χ) l n i x) j

include h

/-- The native signed estimates are obtained from the constructed
reference, without accepting a completed native covariance record. -/
theorem copied_coefficients_jets
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (dirs : Λ → I → LinearWaveBounds.GraphDirections X)
    (request : ℕ → X → Vec2) {β : ℝ} {W : Λ → ℕ → X → ℝ}
    (hzeta : ∀ x ∈ s.domain, 0 < s.zeta x)
    (hR : ∀ q, UniformLocalJets s (fun _ _ x => s.zeta x) β K (fun _ n _ x => request n x q))
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (j : Fin 2)
    (henv : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      c.pull (pulseEnvelope F χ j) l n i x ≤ W l n x)
    (hnormal : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      (fun y => normal.value l n • c.pull (phaseNormal (F j) χ) l n i y) =ᶠ[𝓝 x]
        (base l i).normal s (dirs l i) n)
    (hfrequency : UniformPrimaryWeights.UniformBandBound s (1 / 2)
      (fun li : Λ × I => fun n => 1 / (base li.1 li.2).frequency n)) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1 / 2) K
      (fun l n i => (copiedCoefficients (F := F) (pref := pref) (χ := χ) (T := T) (mask := mask)
        c scale normal clock base dirs request j l i).amplitude n) ∧
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1) K
      (fun l n i => (copiedCoefficients (F := F) (pref := pref) (χ := χ) (T := T) (mask := mask)
        c scale normal clock base dirs request j l i).pressure n) := by
  have hg := h.copied_geometry_jets c normal clock j
  have hN := uniform_local_congr hg.1 hnormal
  apply SignedCopyBounds.uniform_coefficients_jets (M := normal.upper * ((F j).M ^ 2 + 3 * (F j).M))
    (h.nativeCovariance c scale hzeta) hR
    (c.unweighted h.mask_jets) (h.copied_unit_jets c j hW henv) hW hN hg.2.1 hg.2.2
    (mul_pos normal.lower_pos (F j).b_pos) _ _ hfrequency j
  · intro l n i x hx hi
    rw [← Filter.EventuallyEq.eq_of_nhds (hnormal l n i x hx hi)]
    exact (h.copied_normal_bounds c normal j l n i hx hi).1
  · intro l n i x hx hi
    rw [← Filter.EventuallyEq.eq_of_nhds (hnormal l n i x hx hi)]
    exact (h.copied_normal_bounds c normal j l n i hx hi).2

end ReferenceBounds

/-! ## The signed request is the measured current-state request -/

theorem uniformLocalJets_of_memClass {s : StripData X} {w : ℕ → X → ℝ} {α : ℝ}
    {f : ℕ → X → E} (hf : MemClass s w α f) (K : Λ → ℕ → I → Set X) :
    UniformLocalJets s (fun _ => w) α K (fun _ n _ => f n) := by
  refine ⟨fun _ n _ x hx _ => (hf.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun _ n _ x hx _ j hj => hb n x hx j hj⟩

theorem fullRequest_localJets (s : StripData LocalSignedRequest.Point)
    (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (ctx : CorrectionState.Context LocalSignedRequest.Point)
    (u : CorrectionState.State LocalSignedRequest.Point) {β : ℝ}
    (h : ∀ q, MeanClass s β (fun n x => LocalSignedRequest.normalizedRequest s P coord ctx u n x q))
    (K : Λ → ℕ → I → Set (LocalSignedRequest.Point × ℝ)) :
    ∀ q, UniformLocalJets (HarmonicWaveInteraction.productStrip s)
      (fun _ _ x => s.zeta x.1) β K
      (fun _ n _ x => LocalSignedRequest.fullRequest s P coord ctx u n x q) :=
  fun q => uniformLocalJets_of_memClass (LocalSignedRequest.fullRequest_class s P coord ctx u h q) K

/-- The actual residuals, their support, and their incoming mean classes
give the complete copy-uniform request estimate. No request jet is assumed. -/
theorem physical_fullRequest_localJets {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (ctx : CorrectionState.Context LocalSignedRequest.Point)
    (u : CorrectionState.State LocalSignedRequest.Point) (α : ℝ)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual ctx n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual ctx n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hsθ : ∀ n, LocalSignedRequest.MovingSupport P.a P.b coord U.carrier (u.thetaResidual ctx n))
    (hsz : ∀ n, LocalSignedRequest.MovingSupport P.a P.b coord U.carrier (u.axialResidual ctx n))
    (hcθ : MeanClass (LocalSignedRequest.movingStripData U P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL) α (u.thetaResidual ctx))
    (hcz : MeanClass (LocalSignedRequest.movingStripData U P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL) α (u.axialResidual ctx))
    (K : Λ → ℕ → I → Set (LocalSignedRequest.Point × ℝ)) :
    let s := LocalSignedRequest.movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL
    ∀ q, UniformLocalJets (HarmonicWaveInteraction.productStrip s)
      (fun _ _ x => s.zeta x.1) (α - 1) K
      (fun _ n _ x => LocalSignedRequest.fullRequest s P coord ctx u n x q) := by
  dsimp only
  exact fullRequest_localJets _ P coord ctx u
    (LocalSignedRequest.normalizedRequest_class U P hcL hcR ε L hε hεone hL ctx u α
      hθ hz hsθ hsz hcθ hcz) K

/-! ## One selected reference family supplies the complete signed input -/

section Combined

variable [Countable Λ] [Nonempty Λ]
  {F₀ : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F₀}
  {H₀ : NominalConeAssembly.Certificate W₀} {ld : ModulatedProfileAssembly.LoopData W₀}
  {v₀ : ModulatedProfileAssembly.Witness ld}
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}

namespace PreparedChart

variable {a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0}
  (C : PreparedChart H₀ v₀ a D) (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)
  {s : StripData X} {K : Λ → ℕ → I → Set X}
  (copy : CopyChart s C.native C.weight K)

noncomputable def copiedMatrix : Λ → I → ℕ → X → Mat2 :=
  fun l i n => copy.pull (pulseMatrix (PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
    (preparedPrefactor r0 vr vt) C.coordinate) l n i

noncomputable def copiedTarget (scale : PositiveScale Λ) : Λ → I → ℕ → X → Vec2 :=
  fun l i n x => scale.value l n ^ 2 • copy.pull C.target l n i x

noncomputable def copiedCoefficients (scale normal clock : PositiveScale Λ)
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (dirs : Λ → I → LinearWaveBounds.GraphDirections X) (request : ℕ → X → Vec2) (j : Fin 2) :
    Λ → I → LinearWaveBounds.WaveCoefficients X :=
  ReferenceBounds.copiedCoefficients
    (F := PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
    (pref := preparedPrefactor r0 vr vt) (χ := C.coordinate) (T := C.target) (mask := C.mask)
    copy scale normal clock base dirs request j

end PreparedChart

/-- Starting with an already selected prepared primary, a common tail
restriction gives actual uniform native covariance, request-driven signed
amplitude/pressure bounds, and the actual cutoff jets. No finished control
record, target jet, fundamental jet, or copied request jet is an input. -/
theorem exists_actual_signed_control
    (a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0)
    (hcone : LeadingStressWeights.FullTrueCone v₀) (hr0 : 0 < r0)
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    ∃ N : ℕ, ∃ hN : a.N ≤ N,
      ∀ (C : PreparedChart H₀ v₀ (a.restrict N hN) D)
        (s : StripData LocalSignedRequest.Point)
        (K : Λ → ℕ → I → Set (LocalSignedRequest.Point × ℝ))
        (copy : CopyChart (HarmonicWaveInteraction.productStrip s) C.native C.weight K)
        (scale normal clock : PositiveScale Λ)
        (base : Λ → I → LinearWaveBounds.WaveCoefficients (LocalSignedRequest.Point × ℝ))
        (dirs : Λ → I → LinearWaveBounds.GraphDirections (LocalSignedRequest.Point × ℝ))
        (P : SignedStressPrimitive.Patch) (coord : ℝ)
        (ctx : CorrectionState.Context LocalSignedRequest.Point)
        (u : CorrectionState.State LocalSignedRequest.Point) (β : ℝ)
        (W : Λ → ℕ → LocalSignedRequest.Point × ℝ → ℝ)
        (j : Fin 2),
      (∀ x ∈ s.domain, 0 < s.zeta x) →
      (∀ q, MeanClass s β (fun n x => LocalSignedRequest.normalizedRequest s P coord ctx u n x q)) →
      (∀ l n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → 0 ≤ W l n x) →
      (∀ l n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ K l n i →
        copy.pull (pulseEnvelope (PrimaryGeometryAssembly.construction H₀ v₀ (a.restrict N hN) hr0)
          C.coordinate j) l n i x ≤ W l n x) →
      (∀ l n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ K l n i →
        (fun y => normal.value l n • copy.pull
          (phaseNormal (PrimaryGeometryAssembly.construction H₀ v₀ (a.restrict N hN) hr0 j)
            C.coordinate)
          l n i y) =ᶠ[𝓝 x] (base l i).normal (HarmonicWaveInteraction.productStrip s) (dirs l i) n)
            →
      UniformPrimaryWeights.UniformBandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
        (fun li : Λ × I => fun n => 1 / (base li.1 li.2).frequency n) →
      Nonempty (SignedCopyBounds.UniformNativeCovariance (HarmonicWaveInteraction.productStrip s) K
        (C.copiedMatrix hr0 vr vt copy) (C.copiedTarget copy scale)) ∧
      UniformLocalJets (HarmonicWaveInteraction.productStrip s)
        (fun l n x => Real.sqrt (s.zeta x.1) * W l n x) (β + 1 / 2) K
        (fun l n i => (C.copiedCoefficients hr0 vr vt copy scale normal clock base dirs
          (LocalSignedRequest.fullRequest s P coord ctx u) j l i).amplitude n) ∧
      UniformLocalJets (HarmonicWaveInteraction.productStrip s)
        (fun l n x => Real.sqrt (s.zeta x.1) * W l n x) (β + 1) K
        (fun l n i => (C.copiedCoefficients hr0 vr vt copy scale normal clock base dirs
          (LocalSignedRequest.fullRequest s P coord ctx u) j l i).pressure n) ∧
      UniformLocalJets (HarmonicWaveInteraction.productStrip s) (fun _ _ _ => 1) 0 K
        (copy.pull (fun L x => GaussianTailFlat.profile (C.coordinate L x).2)) := by
  obtain ⟨N, hN, hc⟩ := exists_referenceBounds (D := D) H₀ v₀ a hcone hr0 vr vt hdet
  refine ⟨N, hN, ?_⟩
  intro C s K copy scale normal clock base dirs P coord ctx u β W j hzeta hrequest hW henv hnormal
    hfrequency
  obtain ⟨hr⟩ := hc C
  have hζ : ∀ x ∈ (HarmonicWaveInteraction.productStrip s).domain,
      0 < (HarmonicWaveInteraction.productStrip s).zeta x := fun x hx => hzeta x.1 hx
  have hb := hr.copied_coefficients_jets copy scale normal clock base dirs
    (LocalSignedRequest.fullRequest s P coord ctx u) hζ
    (fullRequest_localJets s P coord ctx u hrequest K) hW j henv hnormal hfrequency
  exact ⟨⟨hr.nativeCovariance copy scale hζ⟩, hb.1, hb.2, copy.unweighted hr.cutoff_jets⟩

end Combined

end NavierStokes.ActualSignedControl
