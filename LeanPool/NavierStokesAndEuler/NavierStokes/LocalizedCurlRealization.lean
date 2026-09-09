/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularCopyBounds

/-!
# Curl realization on native phase patches

The geometric and tangency hypotheses are imposed only where the raw
wave is used. The cutoff coefficient has a zero germ elsewhere in its
copy cell. The actual common potential and corrected wave inherit the
local curl and divergence identities through those germs.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.LocalizedCurlRealization

open Set Function Filter WeightedClasses HarmonicCalculus LinearWaveBounds
open PeriodizedWaveBounds CurlClassBounds
open scoped Topology ContDiff InnerProductSpace


variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem geometry_restrict {U V : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) (hV : IsOpen V) (hVU : V ⊆ U) :
    CylindricalGeometry V R Vr Vθ Vz :=
  { isOpen := hV
    radius_smooth := G.radius_smooth.mono hVU
    radius_ne := fun x hx => G.radius_ne x (hVU hx)
    radial_smooth := G.radial_smooth.mono hVU
    angular_smooth := G.angular_smooth.mono hVU
    axial_smooth := G.axial_smooth.mono hVU
    radial_radius := fun x hx => G.radial_radius x (hVU hx)
    angular_radius := fun x hx => G.angular_radius x (hVU hx)
    axial_radius := fun x hx => G.axial_radius x (hVU hx)
    radial_angular := fun x hx => G.radial_angular x (hVU hx)
    radial_axial := fun x hx => G.radial_axial x (hVU hx)
    angular_axial := fun x hx => G.angular_axial x (hVU hx) }

theorem normalDot_real_smul (N : ProblemStatement.Space) (r : ℝ)
    (a : HarmonicCalculus.ComplexVector) :
    normalDot N (r • a) = (r : ℂ) * normalDot N a := by
  simp only [normalDot, Pi.smul_apply, Complex.real_smul]
  ring

/-- Primitive smoothness, cylindrical geometry, and raw tangency on the
genuine native phase patch. No corrected-wave equation is an input. -/
structure RawData (a : CopyData D I) (s : StripData D) (d : GraphDirections D)
    (C : ℕ → I → Set D) : Prop where
  geometry : ∀ n i, CylindricalGeometry (s.domain ∩ C n i) (a.background.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  phase : ∀ n i, ContDiffOn ℝ ∞ (a.background.phase n) (s.domain ∩ C n i)
  amplitude : ∀ n i, ContDiffOn ℝ ∞ (a.amplitude n i) (s.domain ∩ C n i)
  cutoff : ∀ n i, ContDiffOn ℝ ∞ (a.cutoff n i) (s.domain ∩ C n i)
  frequency : ∀ n, a.background.frequency n ≠ 0
  normal : ∀ n i x, x ∈ s.domain ∩ C n i → a.background.normal s d n x ≠ 0
  tangent : ∀ n i x, x ∈ s.domain ∩ C n i →
    normalDot (a.background.normal s d n x) (a.amplitude n i x) = 0

namespace RawData

variable {a : CopyData D I} {s : StripData D} {d : GraphDirections D}
  {C : ℕ → I → Set D}

theorem of_localClasses {wa wψ : ℕ → I → D → ℝ} {α β : ℝ}
    (hG : ∀ n i, CylindricalGeometry (s.domain ∩ C n i) (a.background.radius n)
      (d.radialField n) (fun _ => d.angular) (d.axialField s n))
    (hΦ : ∀ n i, ContDiffOn ℝ ∞ (a.background.phase n) (s.domain ∩ C n i))
    (ha : LocalizedWaveBounds.LocalClass s C wa α a.amplitude)
    (hψ : LocalizedWaveBounds.LocalClass s C wψ β a.cutoff)
    (hK : ∀ n, a.background.frequency n ≠ 0)
    (hn : ∀ n i x, x ∈ s.domain ∩ C n i → a.background.normal s d n x ≠ 0)
    (ht : ∀ n i x, x ∈ s.domain ∩ C n i →
      normalDot (a.background.normal s d n x) (a.amplitude n i x) = 0) :
    RawData a s d C :=
  ⟨hG, hΦ, fun n i x hx => (ha.smooth n i x hx.1 hx.2).contDiffWithinAt,
    fun n i x hx => (hψ.smooth n i x hx.1 hx.2).contDiffWithinAt, hK, hn, ht⟩

variable (h : RawData a s d C)

include h

theorem localized_smooth (n : ℕ) (i : I) :
    ContDiffOn ℝ ∞ ((a.localized i).amplitude n) (s.domain ∩ C n i) :=
  (h.cutoff n i).smul (h.amplitude n i)

theorem localized_tangent (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain ∩ C n i) :
    normalDot (a.background.normal s d n x) ((a.localized i).amplitude n x) = 0 := by
  change normalDot (a.background.normal s d n x) (a.cutoff n i x • a.amplitude n i x) = 0
  rw [normalDot_real_smul, h.tangent n i x hx, mul_zero]

theorem native_potential_smooth (n : ℕ) (i : I) :
    ContDiffOn ℝ ∞ ((a.localized i).curlPotential s d n) (s.domain ∩ C n i) :=
  vectorPotential_contDiffOn (h.geometry n i) (a.background.frequency n)
    (h.phase n i) (h.localized_smooth n i) (h.normal n i)

theorem native_realizes_curl (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain ∩ C n i) :
    cylindricalCurl (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) ((a.localized i).curlPotential s d n) x =
    vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.corrected s d i).amplitude n) x :=
  cylindricalCurl_vectorPotential (h.geometry n i) (h.frequency n)
    (h.phase n i) (h.localized_smooth n i) (h.normal n i)
    (fun _ hx => h.localized_tangent n i hx) hx

theorem native_divergence_zero (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain ∩ C n i) :
    cylindricalDivergence (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.corrected s d i).amplitude n)) x = 0 :=
  realizedCoefficient_divergence (h.geometry n i) (h.frequency n)
    (h.phase n i) (h.localized_smooth n i) (h.normal n i)
    (fun _ hx => h.localized_tangent n i hx) hx

theorem native_velocity_smooth (n : ℕ) (i : I) :
    ContDiffOn ℝ ∞ (vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.corrected s d i).amplitude n)) (s.domain ∩ C n i) := by
  have G := h.geometry n i
  have hc := cylindricalCurl_contDiffOn G.isOpen (G.radius_smooth.inv G.radius_ne)
    G.radial_smooth G.angular_smooth G.axial_smooth (h.native_potential_smooth n i)
  exact hc.congr (fun x hx => (h.native_realizes_curl n i hx).symm)

end RawData

/-- The whole native corrected field and its potential vanish as germs
whenever the cutoff amplitude does. No background regularity is needed. -/
theorem native_zero_germs (a : CopyData D I) (s : StripData D) (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D}
    (ha : (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) :
    ((a.localized i).curlPotential s d n =ᶠ[𝓝 x] fun _ => 0) ∧
    ((a.corrected s d i).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.corrected s d i).amplitude n) =ᶠ[𝓝 x] fun _ => 0) := by
  have hp := potential_germ ha (a.background.frequency n) (a.background.radius n)
    (a.background.phase n) (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  have hpot : (a.localized i).curlPotential s d n =ᶠ[𝓝 x] fun _ => 0 := by
    simp only [vectorPotential_zero] at hp
    exact hp
  have hc := ParticularWaveAssembly.realizedCoefficient_germ ha (a.background.frequency n)
    (a.background.radius n) (d.radialField n) (fun _ => d.angular)
    (d.axialField s n) (a.background.phase n)
  have hcor : (a.corrected s d i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
    simp only [realizedCoefficient_zero] at hc
    exact hc
  refine ⟨hpot, hcor, ?_⟩
  filter_upwards [hcor] with y hy
  ext j
  simp only [vectorMode, mode, hy, Pi.zero_apply, zero_mul]

theorem native_identities_of_zero_germ (a : CopyData D I) (s : StripData D)
    (d : GraphDirections D) {n : ℕ} {i : I} {x : D}
    (ha : (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) :
    (cylindricalCurl (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) ((a.localized i).curlPotential s d n) x =
      vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.corrected s d i).amplitude n) x) ∧
    cylindricalDivergence (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.corrected s d i).amplitude n)) x = 0 := by
  obtain ⟨hpot, _, hv⟩ := native_zero_germs a s d ha
  have hc := ParticularWaveAssembly.curl_germ hpot (a.background.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  have hd := divergence_germ hv (a.background.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  constructor
  · rw [hv.self_of_nhds]
    simpa only [cylindricalCurl_zero] using hc.self_of_nhds
  · simpa only [cylindricalDivergence_zero] using hd.self_of_nhds

namespace RawData

variable {a : CopyData D I} {s : StripData D} {d : GraphDirections D}
  {C : ℕ → I → Set D} (h : RawData a s d C)
  (K : Cells D I) (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
  (hcover : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → x ∈ C n i ∨
    (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0)

include h K hs hcover

theorem common_realizes_curl (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    cylindricalCurl (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (a.common.curlPotential s d n) x =
    vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.commonCorrected s d).amplitude n) x := by
  apply a.common_realizes_curl K hs s d _ n hx
  intro m i y hy hi
  rcases hcover m i y hy hi with hC | hz
  · exact h.native_realizes_curl m i ⟨hy, hC⟩
  · exact (native_identities_of_zero_germ a s d hz).1

theorem common_divergence_zero (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    cylindricalDivergence (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.commonCorrected s d).amplitude n)) x = 0 := by
  apply a.common_divergence_zero K hs s d _ n hx
  intro m i y hy hi
  rcases hcover m i y hy hi with hC | hz
  · exact h.native_divergence_zero m i ⟨hy, hC⟩
  · exact (native_identities_of_zero_germ a s d hz).2

theorem common_potential_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (a.common.curlPotential s d n) s.domain := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  classical
  by_cases hi : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := hi
    have hg := a.common_potential_germ K hs s d n hi
    rcases hcover n i x hx hi with hC | hz
    · exact ((h.native_potential_smooth n i).contDiffAt
        ((h.geometry n i).isOpen.mem_nhds ⟨hx, hC⟩)).congr_of_eventuallyEq hg
    · exact contDiffAt_const.congr_of_eventuallyEq
        (hg.trans (native_zero_germs a s d hz).1)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (a.common_potential_zero_germ K hs s d (not_exists.mp hi))

theorem common_velocity_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (vectorMode (a.background.frequency n) (a.background.phase n)
      ((a.commonCorrected s d).amplitude n)) s.domain := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  classical
  by_cases hi : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := hi
    have hg := ParticularWaveAssembly.vectorMode_germ
      (a.commonCorrected_amplitude_germ K hs s d n hi)
      (a.background.frequency n) (a.background.phase n)
    rcases hcover n i x hx hi with hC | hz
    · exact ((h.native_velocity_smooth n i).contDiffAt
        ((h.geometry n i).isOpen.mem_nhds ⟨hx, hC⟩)).congr_of_eventuallyEq hg
    · exact contDiffAt_const.congr_of_eventuallyEq
        (hg.trans (native_zero_germs a s d hz).2.2)
  · have hz := a.commonCorrected_zero_germ K hs s d (not_exists.mp hi)
    have hm : vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.commonCorrected s d).amplitude n) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hz] with y hy
      ext j
      simp only [vectorMode, mode, hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hm

end RawData

/-! ## Tangency of the actual raw coefficients -/

theorem signed_coefficients_tangent_at {s : StripData D} {d : GraphDirections D}
    (a : WaveCoefficients D)
    (H : ℕ → D → SignedWaveUpdate.Mat2)
    (T R : ℕ → D → SignedWaveUpdate.Vec2) (mask : ℕ → D → ℝ)
    (v Ndot : ℕ → D → ProblemStatement.Space)
    (A : ℕ → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space)
    (j : Fin 2) (n : ℕ) {x : D}
    (ht : ⟪a.normal s d n x, v n x⟫_ℝ = 0) :
    normalDot ((SignedWaveUpdate.coefficients a s d H T R mask v Ndot A j).normal s d n x)
      ((SignedWaveUpdate.coefficients a s d H T R mask v Ndot A j).amplitude n x) = 0 := by
  change normalDot (a.normal s d n x) (CurlClassBounds.complexify
    (SignedWaveUpdate.signedScalar s H T R mask j n x • v n x)) = 0
  rw [SignedWaveUpdate.normalDot_complexify, inner_smul_right, ht, mul_zero]
  rfl

section Particular

open CommonCoverSolve TorusInverse ParticularWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {s : StripData (P × Plane)} {α : ℝ}
  {dirs : GraphDirections (P × Plane)}
  {frame : ℕ → PrimaryODE.FrameData (P × ℝ)}
  {t : ℕ → TangentData P ProblemStatement.Space}
  {source : ℕ → P × Plane → HarmonicCalculus.ComplexVector}
  {harmonic : ℤ} {g : ℕ → Geometry} {L : ℕ → ℝ} {envelope : ℕ → ℝ → ℝ}
  {C : ℕ → Frequency → Set (P × Plane)}

/-- The particular coefficient is tangent because each actual finite-path
modal solve reconstructs into the tangent plane. Its two modal
neighborhoods need not coincide, and no global modal control is used. -/
theorem complexCopyCoefficients_tangent_at
    (base : WaveCoefficients (P × Plane)) (hL : ∀ n, 0 < L n)
    (hr : ParticularCopyBounds.ModalControl s α frame
      (fun n => realData (t n) (source n)) harmonic g L envelope C)
    (hi : ParticularCopyBounds.ModalControl s α frame
      (fun n => imagData (t n) (source n)) harmonic g L envelope C)
    (n : ℕ) (k : Frequency) {x : P × Plane} (hx : x ∈ s.domain) (hk : x ∈ C n k)
    (hN : base.normal s dirs n x = (t n).normal (nativePoint (g n) k x)) :
    normalDot (base.normal s dirs n x)
      ((complexCopyCoefficients base t source g (fun _ => k) L hL).amplitude n x) = 0 := by
  have hxR := hr.contains n k x hx hk
  have hxI := hi.contains n k x hx hk
  have htR := copyVelocity_tangent_of_modal (frame n) (realData (t n) (source n)) harmonic
    (g n) k (hL n).le (hr.bridge n k) hxR
    ⟨(hr.current_slot n k x hxR).1.le, (hr.current_slot n k x hxR).2.le⟩
  have htI := copyVelocity_tangent_of_modal (frame n) (imagData (t n) (source n)) harmonic
    (g n) k (hL n).le (hi.bridge n k) hxI
    ⟨(hi.current_slot n k x hxI).1.le, (hi.current_slot n k x hxI).2.le⟩
  rw [hN]
  change normalDot ((t n).normal (nativePoint (g n) k x))
    (copyVelocity (realData (t n) (source n)) (g n) (hL n).le k x +
      Complex.I • copyVelocity (imagData (t n) (source n)) (g n) (hL n).le k x) = 0
  have hadd (N : ProblemStatement.Space) (u v : HarmonicCalculus.ComplexVector) :
      normalDot N (u + Complex.I • v) = normalDot N u + Complex.I * normalDot N v := by
    simp only [normalDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change normalDot ((t n).normal (nativePoint (g n) k x))
    (copyVelocity (realData (t n) (source n)) (g n) (hL n).le k x) = 0 at htR
  change normalDot ((t n).normal (nativePoint (g n) k x))
    (copyVelocity (imagData (t n) (source n)) (g n) (hL n).le k x) = 0 at htI
  rw [hadd, htR, htI, mul_zero, add_zero]

end Particular

end NavierStokes.LocalizedCurlRealization
