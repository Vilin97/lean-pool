/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedCurlRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopyAngularInvariance

@[expose] public section

/-!
# Actual wave identities at closed native-cell points

All derivatives below are ambient derivatives at the selected point.  No
openness of a quantitative control cell, nor a zero germ at its flat boundary,
is required.
-/

namespace NavierStokes.ClosedNativeWaveIdentities

noncomputable section

open Set Function Filter HarmonicCalculus LinearWaveBounds WeightedClasses
open scoped Topology ContDiff BigOperators


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem along_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : D → D) {f g : D → E} {x : D} (h : f =ᶠ[𝓝 x] g) :
    along V f x = along V g x :=
  congrArg (fun L : D →L[ℝ] E => L (V x)) h.fderiv_eq

theorem contDiffAt_along {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : D → D} {f : D → E} {x : D}
    (hV : ContDiffAt ℝ ∞ V x) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (along V f) x :=
  (hf.fderiv_right (by simp)).clm_apply hV

theorem eventually_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : D → E} {x : D} (hf : ContDiffAt ℝ ∞ f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  exact (h1.eventually (by simp)).mono (fun _ hy => hy.differentiableAt (by norm_num))

theorem along_along_mode_at {V : D → D} (κ : ℝ)
    {Φ : D → ℝ} {a : D → ℂ} {x : D}
    (hV : ContDiffAt ℝ ∞ V x) (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x) :
    along V (along V (mode κ Φ a)) x =
      (along V (along V a) x +
        2 * phaseFactor κ * Complex.ofReal (along V Φ x) * along V a x +
        (phaseFactor κ * Complex.ofReal (along V (along V Φ) x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (along V Φ x) ^ 2) * a x) * carrier κ Φ x := by
  let b : D → ℂ := fun y =>
    along V a y + phaseFactor κ * Complex.ofReal (along V Φ y) * a y
  have hDa := contDiffAt_along hV ha
  have hDΦ := contDiffAt_along hV hΦ
  have hDc : ContDiffAt ℝ ∞ (fun y => Complex.ofReal (along V Φ y)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hDΦ
  have hb : ContDiffAt ℝ ∞ b x := hDa.add ((contDiffAt_const.mul hDc).mul ha)
  have hfirst : along V (mode κ Φ a) =ᶠ[𝓝 x] mode κ Φ b := by
    filter_upwards [eventually_differentiableAt hΦ, eventually_differentiableAt ha] with y hpy hay
    exact along_mode V κ hpy hay
  have da := ha.differentiableAt (by simp)
  have dDa := hDa.differentiableAt (by simp)
  have dΦ := hΦ.differentiableAt (by simp)
  have dDΦ := hDΦ.differentiableAt (by simp)
  have dDc := hDc.differentiableAt (by simp)
  have db := hb.differentiableAt (by simp)
  rw [along_germ V hfirst, along_mode V κ dΦ db]
  have hDb : along V b x = along V (along V a) x +
      phaseFactor κ * Complex.ofReal (along V (along V Φ) x) * a x +
      phaseFactor κ * Complex.ofReal (along V Φ x) * along V a x := by
    dsimp only [b]
    rw [along_add V dDa ((differentiableAt_const _).fun_mul dDc |>.fun_mul da),
      along_mul V ((differentiableAt_const _).fun_mul dDc) da,
      along_const_mul V (phaseFactor κ) dDc, along_ofReal V dDΦ]
    ring
  rw [hDb]
  dsimp only [b]
  have hs := phaseFactor_sq κ
  ring_nf at hs ⊢
  rw [hs]
  ring

theorem cylindricalLaplacian_mode_at (R : D → ℝ) {Vr Vθ Vz : D → D} (κ : ℝ)
    {Φ : D → ℝ} {a : D → ℂ} {x : D}
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x) :
    cylindricalLaplacian R Vr Vθ Vz (mode κ Φ a) x =
      (cylindricalLaplacian R Vr Vθ Vz a x +
        2 * phaseFactor κ * phaseCross R Vr Vθ Vz Φ a x +
        (phaseFactor κ * Complex.ofReal (cylindricalLaplacian R Vr Vθ Vz Φ x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2)) * a x) *
        carrier κ Φ x := by
  rw [← phaseSquare_eq_norm_sq]
  unfold cylindricalLaplacian
  rw [along_along_mode_at κ hr hΦ ha, along_along_mode_at κ hθ hΦ ha,
    along_along_mode_at κ hz hΦ ha,
    along_mode Vr κ (hΦ.differentiableAt (by simp)) (ha.differentiableAt (by simp))]
  simp only [phaseCross, phaseSquare, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem along_along_const_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : D → D} {f : D → E} {c : E} {x : D}
    (hf : along V f =ᶠ[𝓝 x] fun _ => c) : along V (along V f) x = 0 := by
  rw [along_germ V hf]
  simp [along]

theorem cylindricalLaplacian_angular_independent_at {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : D → ℝ) (Vr Vθ Vz : D → D) {f : D → E} {x : D}
    (hf : along Vθ f =ᶠ[𝓝 x] fun _ => 0) :
    cylindricalLaplacian R Vr Vθ Vz f x =
      along Vr (along Vr f) x + (R x)⁻¹ • along Vr f x + along Vz (along Vz f) x := by
  simp only [cylindricalLaplacian, along_along_const_germ hf, smul_zero, add_zero]

theorem cylindricalLaplacian_phase_at (R : D → ℝ) (Vr Vθ Vz : D → D)
    {Φ : D → ℝ} {p : ℝ} {x : D} (hΦθ : along Vθ Φ =ᶠ[𝓝 x] fun _ => p) :
    cylindricalLaplacian R Vr Vθ Vz Φ x =
      along Vr (fun y => phaseNormal R Vr Vθ Vz Φ y 0) x +
        phaseNormal R Vr Vθ Vz Φ x 0 / R x +
        along Vz (fun y => phaseNormal R Vr Vθ Vz Φ y 2) x := by
  simp [cylindricalLaplacian, along_along_const_germ hΦθ, phaseNormal, smul_eq_mul, div_eq_mul_inv]
  ring

theorem cylindricalVectorLaplacian_mode_at (R : D → ℝ) {Vr Vθ Vz : D → D} (κ : ℝ)
    {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ∀ i, ContDiffAt ℝ ∞ (fun y => a y i) x) :
    cylindricalVectorLaplacian R Vr Vθ Vz (vectorMode κ Φ a) x = fun i =>
      (cylindricalVectorLaplacian R Vr Vθ Vz a x i +
        2 * phaseFactor κ * phaseCross R Vr Vθ Vz Φ (fun y => a y i) x +
        (phaseFactor κ * Complex.ofReal (cylindricalLaplacian R Vr Vθ Vz Φ x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2)) * a x i +
        2 * phaseFactor κ * Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x 1 / R x) *
          angularGenerator (a x) i) * carrier κ Φ x := by
  have dΦ := hΦ.differentiableAt (by simp)
  have da i := (ha i).differentiableAt (by simp)
  have hL i := cylindricalLaplacian_mode_at R κ hr hθ hz hΦ (ha i)
  have hD (i : Fin 3) : along Vθ (fun y => a y i * carrier κ Φ y) x =
      (along Vθ (fun y => a y i) x +
        phaseFactor κ * Complex.ofReal (along Vθ Φ x) * a x i) * carrier κ Φ x :=
    along_mode Vθ κ dΦ (da i)
  funext i
  change cylindricalLaplacian R Vr Vθ Vz (mode κ Φ (fun y => a y i)) x + _ = _
  rw [hL i]
  fin_cases i <;>
    simp [cylindricalVectorLaplacian, angularGenerator, vectorMode, hD 0, hD 1,
      mode, phaseNormal, Complex.real_smul, div_eq_mul_inv, pow_two] <;> ring

theorem cylindricalVectorLaplacian_angular_independent_at (R : D → ℝ) (Vr Vθ Vz : D → D)
    {a : D → ComplexVector} {x : D}
    (haθ : ∀ i, along Vθ (fun y => a y i) =ᶠ[𝓝 x] fun _ => 0) :
    cylindricalVectorLaplacian R Vr Vθ Vz a x = fun i =>
      along Vr (along Vr (fun y => a y i)) x + (R x)⁻¹ • along Vr (fun y => a y i) x +
        along Vz (along Vz (fun y => a y i)) x +
        ((R x) ^ 2)⁻¹ • angularGenerator (angularGenerator (a x)) i := by
  funext i
  unfold cylindricalVectorLaplacian
  rw [cylindricalLaplacian_angular_independent_at R Vr Vθ Vz (haθ i)]
  have he : (fun j => along Vθ (fun y => a y j) x) = 0 := by
    funext j
    exact (haθ j).self_of_nhds
  rw [he]
  have hzero : angularGenerator 0 = 0 := by
    funext j
    fin_cases j <;> simp [angularGenerator]
  simp only [hzero, Pi.zero_apply, mul_zero, zero_add]

theorem vectorLaplacian_mode_split_at (R : D → ℝ) {Vr Vθ Vz : D → D} (κ : ℝ)
    {Φ : D → ℝ} {a : D → ComplexVector} {pθ : ℝ} {x : D}
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ∀ i, ContDiffAt ℝ ∞ (fun y => a y i) x)
    (haθ : ∀ i, along Vθ (fun y => a y i) =ᶠ[𝓝 x] fun _ => 0)
    (hΦθ : along Vθ Φ =ᶠ[𝓝 x] fun _ => pθ) :
    cylindricalVectorLaplacian R Vr Vθ Vz (vectorMode κ Φ a) x = fun i =>
      (LinearWaveResidual.viscousRemainder R Vr Vθ Vz κ Φ a x i -
        (κ : ℂ) ^ 2 * Complex.ofReal (‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2) * a x i) *
        carrier κ Φ x := by
  rw [cylindricalVectorLaplacian_mode_at R κ hr hθ hz hΦ ha,
    cylindricalVectorLaplacian_angular_independent_at R Vr Vθ Vz haθ,
    cylindricalLaplacian_phase_at R Vr Vθ Vz hΦθ]
  ext i
  simp [LinearWaveResidual.viscousRemainder, phaseCross, (haθ i).self_of_nhds, phaseNormal]
  ring

theorem linearResidual_mode_split_at (ε κ : ℝ) (R b F G : D → ℝ)
    {Vr Vθ Vz : D → D} (Vf Vs : D → D) {Φ : D → ℝ} {a : D → ComplexVector}
    {p : D → ℂ} {pθ : ℝ} {x : D}
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ∀ i, ContDiffAt ℝ ∞ (fun y => a y i) x)
    (hR : DifferentiableAt ℝ R x) (hb : DifferentiableAt ℝ b x)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (hRx : R x ≠ 0) (hDr : along Vr R x = 1)
    (hBθ : ∀ i, along Vθ (fun y => LinearWaveResidual.base R b F G y i) x = 0)
    (haθ : ∀ i, along Vθ (fun y => a y i) =ᶠ[𝓝 x] fun _ => 0)
    (hΦθ : along Vθ Φ =ᶠ[𝓝 x] fun _ => pθ)
    (hp : DifferentiableAt ℝ p x) (hpθ : along Vθ p x = 0) :
    LinearWaveResidual.linearResidual ε R Vr Vθ Vz (LinearWaveResidual.timeDirection ε Vf Vs)
      (LinearWaveResidual.complexBase R b F G) (vectorMode κ Φ a) (mode κ Φ p) x = fun i =>
      (LinearWaveResidual.principal ε κ R F G Vr Vθ Vz Vf Φ a p x i +
        LinearWaveResidual.remainder ε κ R b F G Vr Vθ Vz Vf Vs Φ a p x i) * carrier κ Φ x := by
  have dΦ := hΦ.differentiableAt (by simp)
  have da i := (ha i).differentiableAt (by simp)
  have hadv := LinearWaveResidual.linearAdvection_mode R b F G Vr Vθ Vz κ hR hb hF hG hRx hDr
    hBθ dΦ da (fun i => (haθ i).self_of_nhds)
  have hlap := vectorLaplacian_mode_split_at R κ hr hθ hz hΦ ha haθ hΦθ
  have hg := LinearWaveResidual.gradient_mode R Vr Vθ Vz κ dΦ hp hpθ
  ext i
  have hadvi := congrFun hadv i
  have hlapi := congrFun hlap i
  have hgi := congrFun hg i
  unfold LinearWaveResidual.linearResidual
  rw [show along (LinearWaveResidual.timeDirection ε Vf Vs) (fun y => vectorMode κ Φ a y i) x =
      (along (LinearWaveResidual.timeDirection ε Vf Vs) (fun y => a y i) x +
        phaseFactor κ * Complex.ofReal (along (LinearWaveResidual.timeDirection ε Vf Vs) Φ x) * a x
          i) *
          carrier κ Φ x from along_mode _ κ dΦ (da i)]
  rw [add_assoc _ (LinearWaveResidual.transport R Vr Vθ Vz (LinearWaveResidual.complexBase R b F G)
    (vectorMode κ Φ a) x i) (LinearWaveResidual.transport R Vr Vθ Vz (vectorMode κ Φ a)
      (LinearWaveResidual.complexBase R b F G) x i)]
  rw [hadvi, hlapi, hgi]
  simp only [LinearWaveResidual.principal, LinearWaveResidual.remainder,
    LinearWaveResidual.slowTransport, LinearWaveResidual.materialPhaseDefect,
    LinearWaveResidual.along_timeDirection, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_pow]
  ring

section Curl

open CurlClassBounds hiding ComplexVector

theorem phaseNormal_contDiffAt {R : D → ℝ} {Vr Vθ Vz : D → D} {Φ : D → ℝ} {x : D}
    (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) : ContDiffAt ℝ ∞ (phaseNormal R Vr Vθ Vz Φ) x := by
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiffAt_along hr hΦ
  · exact (contDiffAt_along hθ hΦ).div hR hRn
  · exact contDiffAt_along hz hΦ

theorem normalCoefficient_contDiffAt {N : D → RealVector} {a : D → ComplexVector} {x : D}
    (hN : ContDiffAt ℝ ∞ N x) (ha : ContDiffAt ℝ ∞ a x) (hne : N x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => normalCoefficient (N y) (a y)) x := by
  have hnorm := (contDiff_norm_sq ℝ).contDiffAt.comp x hN
  exact (hnorm.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).smul
    ((complexCrossLinear.contDiff.contDiffAt.comp x
      (complexify.contDiff.contDiffAt.comp x hN)).clm_apply ha)

theorem cylindricalCurl_contDiffAt {R : D → ℝ} {Vr Vθ Vz : D → D} {B : D → ComplexVector}
    {x : D} (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (cylindricalCurl R Vr Vθ Vz B) x := by
  have hb := contDiffAt_pi.mp hB
  have hDr i := contDiffAt_along hr (hb i)
  have hDθ i := contDiffAt_along hθ (hb i)
  have hDz i := contDiffAt_along hz (hb i)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact ((hR.inv hRn).smul (hDθ 2)).sub (hDz 1)
  · exact (hDz 0).sub (hDr 2)
  · exact ((hDr 1).add ((hR.inv hRn).smul (hb 1))).sub ((hR.inv hRn).smul (hDθ 0))

theorem carrier_contDiffAt (K : ℝ) {Φ : D → ℝ} {x : D} (hΦ : ContDiffAt ℝ ∞ Φ x) :
    ContDiffAt ℝ ∞ (carrier K Φ) x :=
  (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hΦ)).cexp

theorem vectorMode_contDiffAt (K : ℝ) {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x) :
    ContDiffAt ℝ ∞ (vectorMode K Φ a) x :=
  contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp ha i).mul (carrier_contDiffAt K hΦ))

theorem vectorPotential_contDiffAt (K : ℝ) {R : D → ℝ} {Vr Vθ Vz : D → D}
    {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x)
    (hn : phaseNormal R Vr Vθ Vz Φ x ≠ 0) :
    ContDiffAt ℝ ∞ (vectorPotential K R Vr Vθ Vz Φ a) x := by
  have hB := normalCoefficient_contDiffAt (phaseNormal_contDiffAt hR hRn hr hθ hz hΦ) ha hn
  exact vectorMode_contDiffAt K hΦ (hB.const_smul (inverseCarrier K))

theorem curlRemainder_contDiffAt (K : ℝ) {R : D → ℝ} {Vr Vθ Vz : D → D}
    {B : D → ComplexVector} {x : D}
    (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (curlRemainder K R Vr Vθ Vz B) x := by
  have he : curlRemainder K R Vr Vθ Vz B =
      fun y => inverseCarrier K • cylindricalCurl R Vr Vθ Vz B y :=
    funext (curlRemainder_eq K R Vr Vθ Vz B)
  rw [he]
  exact (cylindricalCurl_contDiffAt hR hRn hr hθ hz hB).const_smul (inverseCarrier K)

theorem realizedCoefficient_contDiffAt (K : ℝ) {R : D → ℝ} {Vr Vθ Vz : D → D}
    {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x)
    (hn : phaseNormal R Vr Vθ Vz Φ x ≠ 0) :
    ContDiffAt ℝ ∞ (realizedCoefficient K R Vr Vθ Vz Φ a) x :=
  ha.add (curlRemainder_contDiffAt K hR hRn hr hθ hz
    (normalCoefficient_contDiffAt (phaseNormal_contDiffAt hR hRn hr hθ hz hΦ) ha hn))

/-- Curl realization itself uses the first coefficient derivatives and
tangency at the selected point, with no surrounding geometric identities. -/
theorem cylindricalCurl_vectorPotential_of_differentiable
    (R : D → ℝ) (Vr Vθ Vz : D → D) {K : ℝ} (hK : K ≠ 0)
    {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x)
    (hB : ∀ i, DifferentiableAt ℝ (fun y => coefficient R Vr Vθ Vz Φ a y i) x)
    (hn : phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) = 0) :
    cylindricalCurl R Vr Vθ Vz (vectorPotential K R Vr Vθ Vz Φ a) x =
      vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a) x := by
  have hcross := normalCross_normalCoefficient hn ht
  rw [vectorPotential, cylindricalCurl_vectorMode R Vr Vθ Vz K
    (B := fun y => inverseCarrier K • coefficient R Vr Vθ Vz Φ a y) hΦ
    (fun i => (hB i).const_smul (inverseCarrier K)),
    cylindricalCurl_const_smul R Vr Vθ Vz (inverseCarrier K) hB, normalCross_smul]
  change (fun i => ((inverseCarrier K • cylindricalCurl R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x)
    i +
      phaseFactor K * (inverseCarrier K • normalCross (phaseNormal R Vr Vθ Vz Φ x)
        (normalCoefficient (phaseNormal R Vr Vθ Vz Φ x) (a x))) i) * carrier K Φ x) = _
  rw [hcross]
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, vectorMode, mode,
    realizedCoefficient, Pi.add_apply, curlRemainder_eq]
  have hc : phaseFactor K * inverseCarrier K = -1 := by
    rw [mul_comm, inverseCarrier_phaseFactor hK]
  calc
    _ = (inverseCarrier K * cylindricalCurl R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x i -
        (phaseFactor K * inverseCarrier K) * a x i) * carrier K Φ x := by ring
    _ = _ := by rw [hc]; ring

theorem cylindricalCurl_vectorPotential_at {K : ℝ} (hK : K ≠ 0)
    {R : D → ℝ} {Vr Vθ Vz : D → D} {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x)
    (hn : phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) = 0) :
    cylindricalCurl R Vr Vθ Vz (vectorPotential K R Vr Vθ Vz Φ a) x =
      vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a) x := by
  have hB := normalCoefficient_contDiffAt (phaseNormal_contDiffAt hR hRn hr hθ hz hΦ) ha hn
  exact cylindricalCurl_vectorPotential_of_differentiable R Vr Vθ Vz hK
    (hΦ.differentiableAt (by simp)) (fun i => (contDiffAt_pi.mp hB i).differentiableAt (by simp))
      hn ht

theorem cylindricalCurl_vectorPotential_germ {K : ℝ} (hK : K ≠ 0)
    {R : D → ℝ} {Vr Vθ Vz : D → D} {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x)
    (hn : phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : (fun y => normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y)) =ᶠ[𝓝 x] fun _ => 0) :
    cylindricalCurl R Vr Vθ Vz (vectorPotential K R Vr Vθ Vz Φ a) =ᶠ[𝓝 x]
      vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a) := by
  have hN := phaseNormal_contDiffAt hR hRn hr hθ hz hΦ
  have hB := normalCoefficient_contDiffAt hN ha hn
  filter_upwards [eventually_differentiableAt hΦ, eventually_differentiableAt hB,
    hN.continuousAt.eventually_ne hn, ht] with y hpy hby hny hty
  exact cylindricalCurl_vectorPotential_of_differentiable R Vr Vθ Vz hK hpy
    (fun i => differentiableAt_pi.mp hby i) hny hty

/-- The actual cylindrical frame identities at one ambient point. -/
structure GeometryAt (R : D → ℝ) (Vr Vθ Vz : D → D) (x : D) : Prop where
  radius_smooth : ContDiffAt ℝ ∞ R x
  radius_ne : R x ≠ 0
  radial_smooth : ContDiffAt ℝ ∞ Vr x
  angular_smooth : ContDiffAt ℝ ∞ Vθ x
  axial_smooth : ContDiffAt ℝ ∞ Vz x
  radial_radius : along Vr R x = 1
  angular_radius : along Vθ R x = 0
  axial_radius : along Vz R x = 0
  radial_angular : fderiv ℝ Vθ x (Vr x) = fderiv ℝ Vr x (Vθ x)
  radial_axial : fderiv ℝ Vz x (Vr x) = fderiv ℝ Vr x (Vz x)
  angular_axial : fderiv ℝ Vz x (Vθ x) = fderiv ℝ Vθ x (Vz x)

theorem divergence_curl_zero_at {R : D → ℝ} {Vr Vθ Vz : D → D} {x : D}
    (G : GeometryAt R Vr Vθ Vz x) {B : D → ComplexVector} (hB : ContDiffAt ℝ ∞ B x) :
    cylindricalDivergence R Vr Vθ Vz (cylindricalCurl R Vr Vθ Vz B) x = 0 := by
  have hBi := contDiffAt_pi.mp hB
  have db i := (hBi i).differentiableAt (by simp)
  have dr i := (contDiffAt_along G.radial_smooth (hBi i)).differentiableAt (by simp)
  have dθ i := (contDiffAt_along G.angular_smooth (hBi i)).differentiableAt (by simp)
  have dz i := (contDiffAt_along G.axial_smooth (hBi i)).differentiableAt (by simp)
  have dinv := (G.radius_smooth.inv G.radius_ne).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y => (R y)⁻¹) x at dinv
  have dR := G.radius_smooth.differentiableAt (by simp)
  have dVr := G.radial_smooth.differentiableAt (by simp)
  have dVθ := G.angular_smooth.differentiableAt (by simp)
  have dVz := G.axial_smooth.differentiableAt (by simp)
  have crθ i := along_commute (hBi i) dVr dVθ G.radial_angular
  have crz i := along_commute (hBi i) dVr dVz G.radial_axial
  have cθz i := along_commute (hBi i) dVθ dVz G.angular_axial
  have hir : along Vr (fun y => (R y)⁻¹) x = -((R x)⁻¹) ^ 2 := by
    rw [along_inv Vr dR G.radius_ne, G.radial_radius]
    simp
  have hiz : along Vz (fun y => (R y)⁻¹) x = 0 := by
    rw [along_inv Vz dR G.radius_ne, G.axial_radius, mul_zero]
  simp only [cylindricalDivergence, cylindricalCurl,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  rw [along_sub Vr (dinv.fun_smul (dθ 2)) (dz 1),
    along_sub Vθ (dz 0) (dr 2),
    along_sub Vz ((dr 1).fun_add (dinv.fun_smul (db 1))) (dinv.fun_smul (dθ 0)),
    along_add Vz (dr 1) (dinv.fun_smul (db 1)), along_real_smul Vr dinv (dθ 2),
    along_real_smul Vz dinv (db 1), along_real_smul Vz dinv (dθ 0), hir, hiz, crθ 2, crz 1, cθz 0]
  simp only [zero_smul, zero_add, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow]
  ring

theorem cylindricalDivergence_germ {R : D → ℝ} {Vr Vθ Vz : D → D}
    {a b : D → ComplexVector} {x : D} (h : a =ᶠ[𝓝 x] b) :
    cylindricalDivergence R Vr Vθ Vz a x = cylindricalDivergence R Vr Vθ Vz b x := by
  have hc i : (fun y => a y i) =ᶠ[𝓝 x] fun y => b y i := h.fun_comp (fun z => z i)
  unfold cylindricalDivergence
  rw [along_germ Vr (hc 0), along_germ Vθ (hc 1), along_germ Vz (hc 2), h.self_of_nhds]

theorem realizedCoefficient_divergence_at {K : ℝ} (hK : K ≠ 0)
    {R : D → ℝ} {Vr Vθ Vz : D → D} {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (G : GeometryAt R Vr Vθ Vz x) (hΦ : ContDiffAt ℝ ∞ Φ x) (ha : ContDiffAt ℝ ∞ a x)
    (hn : phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : (fun y => normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y)) =ᶠ[𝓝 x] fun _ => 0) :
    cylindricalDivergence R Vr Vθ Vz
      (vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a)) x = 0 := by
  rw [← cylindricalDivergence_germ (cylindricalCurl_vectorPotential_germ hK G.radius_smooth
    G.radius_ne
    G.radial_smooth G.angular_smooth G.axial_smooth hΦ ha hn ht)]
  exact divergence_curl_zero_at G (vectorPotential_contDiffAt K G.radius_smooth G.radius_ne
    G.radial_smooth G.angular_smooth G.axial_smooth hΦ ha hn)

theorem cylindricalDivergence_contDiffAt {R : D → ℝ} {Vr Vθ Vz : D → D}
    {a : D → ComplexVector} {x : D}
    (hR : ContDiffAt ℝ ∞ R x) (hRn : R x ≠ 0)
    (hr : ContDiffAt ℝ ∞ Vr x) (hθ : ContDiffAt ℝ ∞ Vθ x) (hz : ContDiffAt ℝ ∞ Vz x)
    (ha : ContDiffAt ℝ ∞ a x) : ContDiffAt ℝ ∞ (cylindricalDivergence R Vr Vθ Vz a) x := by
  have hai := contDiffAt_pi.mp ha
  exact (((contDiffAt_along hr (hai 0)).add ((hR.inv hRn).smul (hai 0))).add
    ((hR.inv hRn).smul (contDiffAt_along hθ (hai 1)))).add (contDiffAt_along hz (hai 2))

omit [NormedSpace ℝ D] in
theorem eq_zero_of_mem_closure {E : Type*} [NormedAddCommGroup E]
    {f : D → E} {C : Set D} {x : D} (hf : ContinuousAt f x)
    (hx : x ∈ closure C) (hzero : EqOn f (fun _ => 0) C) : f x = 0 := by
  have hm := mem_closure_image hf hx
  have hs : f '' C ⊆ ({0} : Set E) := by
    rintro y ⟨z, hz, rfl⟩
    exact hzero hz
  have he := closure_mono hs hm
  simpa only [closure_singleton, mem_singleton_iff] using he

/-- A second legitimate boundary interface: tangency on a set whose interior
approaches the selected point.  Continuity of the actual divergence is derived
from the supplied ambient jets. -/
theorem realizedCoefficient_divergence_of_mem_closure_interior {K : ℝ} (hK : K ≠ 0)
    {R : D → ℝ} {Vr Vθ Vz : D → D} {Φ : D → ℝ} {a : D → ComplexVector} {C : Set D} {x : D}
    (hG : ∀ y ∈ C, GeometryAt R Vr Vθ Vz y)
    (hΦ : ∀ y ∈ C, ContDiffAt ℝ ∞ Φ y) (ha : ∀ y ∈ C, ContDiffAt ℝ ∞ a y)
    (hn : ∀ y ∈ C, phaseNormal R Vr Vθ Vz Φ y ≠ 0)
    (ht : ∀ y ∈ C, normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y) = 0)
    (hx : x ∈ C) (hclosure : x ∈ closure (interior C)) :
    cylindricalDivergence R Vr Vθ Vz
      (vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a)) x = 0 := by
  have G := hG x hx
  have hc := realizedCoefficient_contDiffAt K G.radius_smooth G.radius_ne
    G.radial_smooth G.angular_smooth G.axial_smooth (hΦ x hx) (ha x hx) (hn x hx)
  apply eq_zero_of_mem_closure
    (cylindricalDivergence_contDiffAt G.radius_smooth G.radius_ne G.radial_smooth G.angular_smooth
      G.axial_smooth (vectorMode_contDiffAt K (hΦ x hx) hc)).continuousAt hclosure
  intro y hy
  have hyC := interior_subset hy
  apply realizedCoefficient_divergence_at hK (hG y hyC) (hΦ y hyC) (ha y hyC) (hn y hyC)
  filter_upwards [isOpen_interior.mem_nhds hy] with z hz
  exact ht z (interior_subset hz)

end Curl

/-! ## Literal cutoff/curl residual from primitive pointwise data -/

structure ExactAt (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (n : ℕ) (x : D) : Prop where
  radial_profile : ContDiffAt ℝ ∞ d.radialProfile x
  phase : ContDiffAt ℝ ∞ (a.phase n) x
  amplitude : ∀ j, ContDiffAt ℝ ∞ (fun y => a.amplitude n y j) x
  radius : DifferentiableAt ℝ (a.radius n) x
  radial_base : DifferentiableAt ℝ (a.radialBase n) x
  frequency_base : DifferentiableAt ℝ (a.frequencyBase n) x
  axial_base : DifferentiableAt ℝ (a.axialBase n) x
  pressure : DifferentiableAt ℝ (a.pressure n) x
  radius_nonzero : a.radius n x ≠ 0
  radial_radius : along (d.radialField n) (a.radius n) x = 1
  base_angular : ∀ j, along (fun _ => d.angular) (fun y =>
    LinearWaveResidual.base (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n) y j)
      x = 0
  amplitude_angular : ∀ j,
    along (fun _ => d.angular) (fun y => a.amplitude n y j) =ᶠ[𝓝 x] fun _ => 0
  phase_angular : ∃ p : ℝ, along (fun _ => d.angular) (a.phase n) =ᶠ[𝓝 x] fun _ => p
  pressure_angular : along (fun _ => d.angular) (a.pressure n) x = 0

theorem harmonicResidual_eq_at {a : WaveCoefficients D} {s : StripData D}
    {d : GraphDirections D} {n : ℕ} {x : D} (h : ExactAt a s d n x) :
    a.harmonicResidual s d n x = fun j =>
      (a.principal s d n x j + a.remainder s d n x j) * carrier (a.frequency n) (a.phase n) x := by
  obtain ⟨pθ, hpθ⟩ := h.phase_angular
  have hr : ContDiffAt ℝ ∞ (d.radialField n) x :=
    contDiffAt_const.add ((h.radial_profile.smul contDiffAt_const).const_smul (d.radialScale n))
  exact linearResidual_mode_split_at (s.epsilon n) (a.frequency n)
    (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n)
    (d.fastField n) (fun _ => d.slow) hr contDiffAt_const contDiffAt_const
    h.phase h.amplitude h.radius h.radial_base h.frequency_base h.axial_base
    h.radius_nonzero h.radial_radius h.base_angular h.amplitude_angular hpθ h.pressure
      h.pressure_angular

theorem harmonicResidual_eq_good_add_excluded_at
    (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (ψ : ℕ → D → ℝ) (f source : ℕ → D → ComplexVector) (n : ℕ) (x : D)
    (h : ExactAt ((a.withCutoff ψ).addAmplitude f) s d n x)
    (ha : ∀ j, DifferentiableAt ℝ (fun y => a.amplitude n y j) x)
    (hψ : DifferentiableAt ℝ (ψ n) x)
    (hf : ∀ j, DifferentiableAt ℝ (fun y => f n y j) x)
    (hsolve : a.principal s d n x = -source n x) :
    ((a.withCutoff ψ).addAmplitude f).harmonicResidual s d n x +
        (fun j => source n x j * carrier (a.frequency n) (a.phase n) x) =
      (fun j => (a.goodCoefficient s d ψ f n x j +
        excludedSlotError d ψ a.amplitude source n x j) * carrier (a.frequency n) (a.phase n) x) :=
          by
  rw [harmonicResidual_eq_at h]
  have he := LocalizedWaveBounds.corrected_coefficient_eq_good_add_excluded_at
    a s d ψ f source n x ha hψ hf hsolve
  ext j
  have hej := congrFun he j
  simp only [Pi.add_apply] at hej ⊢
  change (_ + _) * carrier (a.frequency n) (a.phase n) x +
      source n x j * carrier (a.frequency n) (a.phase n) x = _
  rw [← add_mul, hej]

/-- These are symmetries of the uncorrected input fields. -/
structure AngularData (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (ψ : ℕ → D → ℝ) (n : ℕ) : Prop where
  radius : CopyAngularInvariance.Invariant d.angular (a.radius n)
  radial_base : CopyAngularInvariance.Invariant d.angular (a.radialBase n)
  frequency_base : CopyAngularInvariance.Invariant d.angular (a.frequencyBase n)
  axial_base : CopyAngularInvariance.Invariant d.angular (a.axialBase n)
  radial_field : CopyAngularInvariance.Invariant d.angular (d.radialField n)
  phase : ∃ p : ℝ, CopyAngularInvariance.AffinePhase d.angular p (a.phase n)
  amplitude : CopyAngularInvariance.Invariant d.angular (a.amplitude n)
  pressure : CopyAngularInvariance.Invariant d.angular (a.pressure n)
  cutoff : CopyAngularInvariance.Invariant d.angular (ψ n)

/-- Only actual input jets and pointwise nondegeneracy enter this record. -/
structure RawJetsAt (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (ψ : ℕ → D → ℝ) (n : ℕ) (x : D) : Prop where
  radial_profile : ContDiffAt ℝ ∞ d.radialProfile x
  phase : ContDiffAt ℝ ∞ (a.phase n) x
  radius : ContDiffAt ℝ ∞ (a.radius n) x
  radial_base : DifferentiableAt ℝ (a.radialBase n) x
  frequency_base : DifferentiableAt ℝ (a.frequencyBase n) x
  axial_base : DifferentiableAt ℝ (a.axialBase n) x
  amplitude : ContDiffAt ℝ ∞ (a.amplitude n) x
  pressure : DifferentiableAt ℝ (a.pressure n) x
  cutoff : ContDiffAt ℝ ∞ (ψ n) x
  radius_ne : a.radius n x ≠ 0
  normal_ne : a.normal s d n x ≠ 0

namespace RawJetsAt

variable {a : WaveCoefficients D} {s : StripData D} {d : GraphDirections D}
  {ψ : ℕ → D → ℝ} {n : ℕ} {x : D} (h : RawJetsAt a s d ψ n x)

include h

theorem radial_field : ContDiffAt ℝ ∞ (d.radialField n) x :=
  contDiffAt_const.add ((h.radial_profile.smul contDiffAt_const).const_smul (d.radialScale n))

theorem curlCorrection : ContDiffAt ℝ ∞ ((a.withCutoff ψ).curlCorrection s d n) x :=
  curlRemainder_contDiffAt (a.frequency n) h.radius h.radius_ne h.radial_field
    contDiffAt_const contDiffAt_const (normalCoefficient_contDiffAt
      (phaseNormal_contDiffAt h.radius h.radius_ne h.radial_field contDiffAt_const contDiffAt_const
        h.phase)
      (h.cutoff.smul h.amplitude) h.normal_ne)

theorem corrected_amplitude : ContDiffAt ℝ ∞ ((a.corrected s d ψ).amplitude n) x :=
  (h.cutoff.smul h.amplitude).add h.curlCorrection

theorem corrected_exact (g : AngularData a s d ψ n)
    (hDr : along (d.radialField n) (a.radius n) x = 1) :
    ExactAt (a.corrected s d ψ) s d n x := by
  obtain ⟨pθ, hpθ⟩ := g.phase
  have hamp : CopyAngularInvariance.Invariant d.angular ((a.corrected s d ψ).amplitude n) :=
    CopyAngularInvariance.realizedCoefficient_invariant g.radius g.radial_field
      (CopyAngularInvariance.Invariant.const _) (CopyAngularInvariance.Invariant.const _) hpθ
      (g.cutoff.map₂ g.amplitude (fun r v => r • v)) (a.frequency n)
  have hpres : CopyAngularInvariance.Invariant d.angular ((a.corrected s d ψ).pressure n) :=
    g.cutoff.map₂ g.pressure (fun r p => (r : ℂ) * p)
  refine ⟨h.radial_profile, h.phase, contDiffAt_pi.mp h.corrected_amplitude,
    h.radius.differentiableAt (by simp), h.radial_base, h.frequency_base, h.axial_base,
    ?_, h.radius_ne, hDr, ?_, ?_, ?_, hpres.along_zero x⟩
  · exact ((Complex.ofRealCLM.hasFDerivAt.comp x
      (h.cutoff.differentiableAt (by simp)).hasFDerivAt).differentiableAt).mul h.pressure
  · intro j
    exact ((CopyAngularInvariance.base_invariant g.radius g.radial_base
      g.frequency_base g.axial_base).component j).along_zero x
  · intro j
    exact Filter.Eventually.of_forall (fun y => (hamp.component j).along_zero y)
  · exact ⟨pθ, (eventually_differentiableAt h.phase).mono (fun y hy => hpθ.directional_eq hy)⟩

theorem cancellation (g : AngularData a s d ψ n)
    (hDr : along (d.radialField n) (a.radius n) x = 1)
    (source : ℕ → D → ComplexVector) (hsolve : a.principal s d n x = -source n x) :
    (a.corrected s d ψ).harmonicResidual s d n x +
        (fun j => source n x j * carrier (a.frequency n) (a.phase n) x) =
      (fun j => (a.constructedGood s d ψ n x j + excludedSlotError d ψ a.amplitude source n x j) *
        carrier (a.frequency n) (a.phase n) x) :=
  harmonicResidual_eq_good_add_excluded_at a s d ψ ((a.withCutoff ψ).curlCorrection s d)
    source n x (h.corrected_exact g hDr)
    (fun j => (contDiffAt_pi.mp h.amplitude j).differentiableAt (by simp))
    (h.cutoff.differentiableAt (by simp))
    (fun j => (contDiffAt_pi.mp h.curlCorrection j).differentiableAt (by simp)) hsolve

end RawJetsAt

section Copies

variable {I : Type} {a : PeriodizedWaveBounds.CopyData D I} {s : StripData D}
  {d : GraphDirections D} {C : ℕ → I → Set D} {P : ℕ → I → D → ℝ} {α κ : ℝ}

theorem rawJets_of_localInput
    (h : LocalizedWaveBounds.InputBounds s C P α κ d (LocalizedWaveBounds.rawFamily a))
    (hψ : LocalizedWaveBounds.LocalUnweighted s C 0 a.cutoff)
    (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain) (hi : x ∈ C n i)
    (hΦ : ContDiffAt ℝ ∞ (a.background.phase n) x)
    (hR : a.background.radius n x ≠ 0) (hN : a.background.normal s d n x ≠ 0) :
    RawJetsAt (a.raw i) s d (fun n => a.cutoff n i) n x :=
  ⟨h.radial_profile.smooth n i x hx hi, hΦ, h.radius.smooth n i x hx hi,
    (h.radial_base.smooth n i x hx hi).differentiableAt (by simp),
    (h.frequency_base.smooth n i x hx hi).differentiableAt (by simp),
    (h.axial_base.smooth n i x hx hi).differentiableAt (by simp),
    contDiffAt_pi.mpr (fun j => (h.amplitude j).smooth n i x hx hi),
    (h.pressure.smooth n i x hx hi).differentiableAt (by simp),
    hψ.smooth n i x hx hi, hR, hN⟩

theorem native_cancellation_of_principal
    (h : LocalizedWaveBounds.InputBounds s C P α κ d (LocalizedWaveBounds.rawFamily a))
    (hψ : LocalizedWaveBounds.LocalUnweighted s C 0 a.cutoff)
    (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain) (hi : x ∈ C n i)
    (hΦ : ContDiffAt ℝ ∞ (a.background.phase n) x)
    (hR : a.background.radius n x ≠ 0) (hN : a.background.normal s d n x ≠ 0)
    (g : AngularData (a.raw i) s d (fun n => a.cutoff n i) n)
    (hDr : along (d.radialField n) (a.background.radius n) x = 1)
    (hsolve : (a.raw i).principal s d n x = -a.source n x) :
    (a.corrected s d i).harmonicResidual s d n x +
        (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) =
      (fun j => (a.localGood s d n i x j + a.localGaussian d n i x j) *
        carrier (a.background.frequency n) (a.background.phase n) x) :=
  (rawJets_of_localInput h hψ n i hx hi hΦ hR hN).cancellation g hDr a.source hsolve

theorem native_realizes_curl_at (n : ℕ) (i : I) (x : D)
    (h : RawJetsAt (a.raw i) s d (fun n => a.cutoff n i) n x)
    (hK : a.background.frequency n ≠ 0)
    (ht : normalDot (a.background.normal s d n x) (a.amplitude n i x) = 0) :
    CurlClassBounds.cylindricalCurl (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) ((a.localized i).curlPotential s d n) x =
      vectorMode (a.background.frequency n) (a.background.phase n) ((a.corrected s d i).amplitude
        n) x := by
  apply cylindricalCurl_vectorPotential_at hK h.radius h.radius_ne h.radial_field
    contDiffAt_const contDiffAt_const h.phase (h.cutoff.smul h.amplitude) h.normal_ne
  change normalDot (a.background.normal s d n x) (a.cutoff n i x • a.amplitude n i x) = 0
  rw [LocalizedCurlRealization.normalDot_real_smul, ht, mul_zero]

theorem native_divergence_zero_at (n : ℕ) (i : I) (x : D)
    (h : RawJetsAt (a.raw i) s d (fun n => a.cutoff n i) n x)
    (G : GeometryAt (a.background.radius n) (d.radialField n) (fun _ => d.angular) (d.axialField s
      n) x)
    (hK : a.background.frequency n ≠ 0)
    (ht : (fun y => normalDot (a.background.normal s d n y) (a.amplitude n i y)) =ᶠ[𝓝 x] fun _ =>
      0) :
    cylindricalDivergence (a.background.radius n) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (vectorMode (a.background.frequency n) (a.background.phase n)
        ((a.corrected s d i).amplitude n)) x = 0 := by
  apply realizedCoefficient_divergence_at hK G h.phase (h.cutoff.smul h.amplitude) h.normal_ne
  filter_upwards [ht] with y hy
  change normalDot (a.background.normal s d n y) (a.cutoff n i y • a.amplitude n i y) = 0
  rw [LocalizedCurlRealization.normalDot_real_smul, hy, mul_zero]

end Copies

end

end NavierStokes.ClosedNativeWaveIdentities
