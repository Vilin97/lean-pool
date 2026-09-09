/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularCopyBounds

@[expose] public section

/-!
# Principal equations on actual native cells

The signed coefficient uses the literal covariance quotient, and the
particular coefficient uses the literal finite-path modal solve. All
regularity needed in these equations is obtained on the selected native
cell. No global covariance-control or solved-output class is required.
-/

noncomputable section

namespace NavierStokes.NativePrincipalEquations

open Set Function Filter WeightedClasses PeriodizedWaveBounds HarmonicCalculus
open scoped ContDiff Topology

section Signed

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {K : ℕ → I → Set D}
  {a : I → LinearWaveBounds.WaveCoefficients D}
  {dirs : I → LinearWaveBounds.GraphDirections D}
  {H : I → ℕ → D → SignedWaveUpdate.Mat2}
  {T R : I → ℕ → D → SignedWaveUpdate.Vec2}
  {mask : I → ℕ → D → ℝ}
  {v Ndot : I → ℕ → D → ProblemStatement.Space}
  {A : I → ℕ → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space}
  {W : ℕ → D → ℝ} {β : ℝ}

/-- The homogeneous principal equation for the actual signed quotient at
a native-cell point. The only equation supplied as input is the primitive
unit fundamental's projected equation; the signed equation is derived. -/
theorem signed_coefficients_principal_at
    (hcov : SignedCopyBounds.NativeCovariance s K H T)
    (hR : ∀ q, LocalJets s (fun _ x => s.zeta x) β K (fun n i x => R i n x q))
    (hm : LocalJets s (fun _ _ => 1) 0 K (fun n i => mask i n))
    (hv : LocalJets s W 0 K (fun n i => v i n))
    (j : Fin 2) (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain) (hi : x ∈ K n i)
    (hHf : SignedWaveUpdate.FrozenAlong (dirs i).fast (H i))
    (hTf : SignedWaveUpdate.FrozenAlong (dirs i).fast (T i))
    (hRf : SignedWaveUpdate.FrozenAlong (dirs i).fast (R i))
    (hmf : SignedWaveUpdate.FrozenAlong (dirs i).fast (mask i))
    (hfrequency : (a i).frequency n ≠ 0)
    (hode : along ((dirs i).fastField n) (v i n) x =
      TangentProjection.projectedRhs ((a i).normal s (dirs i) n x) (Ndot i n x) (v i n x)
        (A i n x (v i n x)) 0
        (s.epsilon n * (a i).frequency n ^ 2 * ‖(a i).normal s (dirs i) n x‖ ^ 2))
    (haction : CurlClassBounds.complexify (A i n x (v i n x)) =
      LinearWaveResidual.shear ((a i).radius n) ((a i).frequencyBase n) ((a i).axialBase n)
        ((dirs i).radialField n) (fun y => CurlClassBounds.complexify (v i n y)) x) :
    (SignedWaveUpdate.coefficients (a i) s (dirs i) (H i) (T i) (R i) (mask i)
      (v i) (Ndot i) (A i) j).principal s (dirs i) n x = 0 := by
  have hsD := ((SignedCopyBounds.signedScalar_jets hcov hR hm j).smooth n i x hx
    hi).differentiableAt (by simp)
  have hvD := (hv.smooth n i x hx hi).differentiableAt (by simp)
  have hfreeze := (SignedWaveUpdate.signedScalar_frozen hHf hTf hRf hmf j).derivative n hsD
  have hfast : along ((dirs i).fastField n)
      (SignedWaveUpdate.signedScalar s (H i) (T i) (R i) (mask i) j n) x = 0 := by
    simp only [along, LinearWaveBounds.GraphDirections.fastField, map_smul, hfreeze, smul_zero]
  have hd : along ((dirs i).fastField n)
      (SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n) x =
      TangentProjection.projectedRhs ((a i).normal s (dirs i) n x) (Ndot i n x)
        (SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n x)
        (A i n x (SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n x))
        0 (s.epsilon n * (a i).frequency n ^ 2 * ‖(a i).normal s (dirs i) n x‖ ^ 2) := by
    change along ((dirs i).fastField n)
      (fun y => SignedWaveUpdate.signedScalar s (H i) (T i) (R i) (mask i) j n y • v i n y) x = _
    rw [SignedWaveUpdate.along_smul _ hsD hvD, hfast, zero_smul, zero_add, hode]
    simp only [SignedWaveUpdate.signedVector, map_smul, SignedWaveUpdate.projectedRhs_smul]
  have hact : CurlClassBounds.complexify
      (A i n x (SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n x)) =
      LinearWaveResidual.shear ((a i).radius n) ((a i).frequencyBase n) ((a i).axialBase n)
        ((dirs i).radialField n) (fun y => CurlClassBounds.complexify
          (SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n y)) x := by
    simp only [SignedWaveUpdate.signedVector, map_smul]
    rw [SignedWaveUpdate.shear_smul, haction]
  have hh := ParticularWaveBounds.principal_eq_neg_source_of_projected
    (s.epsilon n) ((a i).frequency n) hfrequency ((a i).radius n) ((a i).frequencyBase n)
    ((a i).axialBase n) ((a i).phase n) ((dirs i).radialField n) (fun _ => (dirs i).angular)
    ((dirs i).axialField s n) ((dirs i).fastField n)
    (SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n) (Ndot i n)
    (fun y => A i n y (SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n y))
    (fun _ => 0) (hsD.smul hvD) hd hact
  simpa only [SignedWaveUpdate.coefficients, SignedWaveUpdate.homogeneousCoefficients,
    LinearWaveBounds.WaveCoefficients.principal, LinearWaveBounds.WaveCoefficients.normal,
    map_zero, neg_zero] using hh

end Signed

section Particular

open CommonCoverSolve TorusInverse ParticularWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {s : StripData (P × Plane)} {α : ℝ}
  {dirs : LinearWaveBounds.GraphDirections (P × Plane)}
  {frame : ℕ → PrimaryODE.FrameData (P × ℝ)}
  {t : ℕ → TangentData P ProblemStatement.Space}
  {source : ℕ → P × Plane → CurlClassBounds.ComplexVector}
  {harmonic : ℤ} {g : ℕ → Geometry} {L : ℕ → ℝ} {envelope : ℕ → ℝ → ℝ}
  {K : ℕ → Frequency → Set (P × Plane)}

/-- The complex finite-path solve satisfies its inhomogeneous principal
equation at each native-cell point. Real and imaginary modal neighborhoods
may differ: their intersection supplies the required common path domain. -/
theorem complexCopyCoefficients_principal_at
    (base : LinearWaveBounds.WaveCoefficients (P × Plane)) (hL : ∀ n, 0 < L n)
    (hr : ParticularCopyBounds.ModalControl s α frame
      (fun n => realData (t n) (source n)) harmonic g L envelope K)
    (hi : ParticularCopyBounds.ModalControl s α frame
      (fun n => imagData (t n) (source n)) harmonic g L envelope K)
    (n : ℕ) (k : Frequency) {x : P × Plane} (hx : x ∈ s.domain) (hk : x ∈ K n k)
    (hfrequency : base.frequency n ≠ 0)
    (hN : base.normal s dirs n x = (t n).normal (nativePoint (g n) k x))
    (hδ : (t n).damping (nativePoint (g n) k x) =
      s.epsilon n * base.frequency n ^ 2 * ‖base.normal s dirs n x‖ ^ 2)
    (hfast : dirs.fastScale n • dirs.fast = ((0 : P), slotDirection (g n)))
    (hA : ∀ z : ProblemStatement.Space,
      CurlClassBounds.complexify ((t n).action (nativePoint (g n) k x) z) =
        LinearWaveResidual.shear (base.radius n) (base.frequencyBase n) (base.axialBase n)
          (dirs.radialField n) (fun _ => CurlClassBounds.complexify z) x) :
    (complexCopyCoefficients base t source g (fun _ => k) L hL).principal s dirs n x =
      -source n x := by
  let Ω := hr.neighborhood n k ∩ hi.neighborhood n k
  have hxR := hr.contains n k x hx hk
  have hxI := hi.contains n k x hx hk
  have hxΩ : x ∈ Ω := ⟨hxR, hxI⟩
  have hAc : ContinuousOn ((t n).linearData.coefficientAlong (g n) k) (Ω ×ˢ Icc 0 (L n)) :=
    (hr.bridge n k).ambient_coefficient.mono (fun _ h => ⟨h.1.1, h.2⟩)
  have hfr : ContinuousOn ((realData (t n) (source n)).linearData.forcingAlong (g n) k)
      (Ω ×ˢ Icc 0 (L n)) :=
    (hr.bridge n k).ambient_forcing.mono (fun _ h => ⟨h.1.1, h.2⟩)
  have hfi : ContinuousOn ((imagData (t n) (source n)).linearData.forcingAlong (g n) k)
      (Ω ×ˢ Icc 0 (L n)) :=
    (hi.bridge n k).ambient_forcing.mono (fun _ h => ⟨h.1.2, h.2⟩)
  have hur := (hr.smooth_at hL hx hk).differentiableAt (by simp)
  have hui := (hi.smooth_at hL hx hk).differentiableAt (by simp)
  have hslot := hr.current_slot n k x hxR
  have hh := complexCopy_principal_of_path (t n) (source n) (g n) (hL n).le k
    hAc hfr hfi (s.epsilon n) (base.frequency n) hfrequency
    (base.radius n) (base.frequencyBase n) (base.axialBase n) (base.phase n)
    (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField s n)
    x.1 x.2 hxΩ ⟨hslot.1.le, hslot.2.le⟩ hur hui hN hδ hA
  have hfast' : dirs.fastField n = fun _ => ((0 : P), slotDirection (g n)) := by
    funext y
    exact hfast
  simpa only [LinearWaveBounds.WaveCoefficients.principal, complexCopyCoefficients,
    hfast', Prod.mk.eta] using hh

end Particular

end NavierStokes.NativePrincipalEquations
