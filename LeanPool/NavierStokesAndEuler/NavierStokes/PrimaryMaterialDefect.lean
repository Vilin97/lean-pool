/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BasePhaseGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds

@[expose] public section

/-!
# The actual primary material-phase defect

The large axial term in the phase is cancelled by its actual material
derivative before estimating any jets.  Only the slow coordinate map and
slot coordinate require polynomial bounds; the angular coordinate and
the unstripped phase itself need no such bound.
-/

noncomputable section

namespace NavierStokes.PrimaryMaterialDefect

open Set WeightedClasses LinearWaveBounds
open scoped Topology ContDiff

abbrev Slow := PhaseCalculus.Slow
abbrev Slot := PhaseCalculus.Slot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order chart identities, including the direction annihilated by
the physical radial graph derivative.  No phase derivative is an input. -/
structure NativeCoordinates (s : StripData E) (d : GraphDirections E)
    (χ : ℕ → E → Slot) : Prop where
  differentiable : ∀ n x, x ∈ s.domain → DifferentiableAt ℝ (χ n) x
  radial : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.radial = PhaseCalculus.eR
  auxiliary : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.auxiliary = 0
  angular : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.angular = PhaseCalculus.eTheta
  axial : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.axial = PhaseCalculus.eZ
  fast : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x (d.fastField n x) = PhaseCalculus.eV
  slow : ∀ n x, x ∈ s.domain → fderiv ℝ (χ n) x d.slow = PhaseCalculus.eT

namespace NativeCoordinates

variable {s : StripData E} {d : GraphDirections E} {χ : ℕ → E → Slot}
variable (hχ : NativeCoordinates s d χ)

include hχ

theorem radialField (n : ℕ) {x : E} (hx : x ∈ s.domain) :
    fderiv ℝ (χ n) x (d.radialField n x) = PhaseCalculus.eR := by
  simp only [GraphDirections.radialField, map_add, map_smul,
    hχ.radial n x hx, hχ.auxiliary n x hx, smul_zero, add_zero]

theorem axialField (n : ℕ) {x : E} (hx : x ∈ s.domain) :
    fderiv ℝ (χ n) x (d.axialField s n x) = s.epsilon n • PhaseCalculus.eZ := by
  simp only [GraphDirections.axialField, map_smul, hχ.axial n x hx]

theorem timeField (n : ℕ) {x : E} (hx : x ∈ s.domain) :
    fderiv ℝ (χ n) x
      (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow) x) =
      PhaseCalculus.eV - s.epsilon n • PhaseCalculus.eT := by
  simp only [LinearWaveResidual.timeDirection, map_sub, map_smul,
    hχ.fast n x hx, hχ.slow n x hx]

end NativeCoordinates

/-- For affine native/common coordinate maps, checking the six images is
linear algebra.  No differentiability premise is needed. -/
theorem affine_coordinates (s : StripData E) (d : GraphDirections E)
    (L : ℕ → E →L[ℝ] Slot) (c : ℕ → Slot)
    (hr : ∀ n, L n d.radial = PhaseCalculus.eR)
    (ha : ∀ n, L n d.auxiliary = 0)
    (hθ : ∀ n, L n d.angular = PhaseCalculus.eTheta)
    (hz : ∀ n, L n d.axial = PhaseCalculus.eZ)
    (hf : ∀ n, d.fastScale n • L n d.fast = PhaseCalculus.eV)
    (ht : ∀ n, L n d.slow = PhaseCalculus.eT) :
    NativeCoordinates s d (fun n x => L n x + c n) := by
  have hd n x : fderiv ℝ (fun y => L n y + c n) x = L n :=
    ((L n).hasFDerivAt.add_const (c n)).fderiv
  refine ⟨fun n _ _ => (L n).differentiableAt.add_const _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x _; rw [hd]; exact hr n
  · intro n x _; rw [hd]; exact ha n
  · intro n x _; rw [hd]; exact hθ n
  · intro n x _; rw [hd]; exact hz n
  · intro n x _; rw [hd]; simpa only [GraphDirections.fastField, map_smul] using hf n
  · intro n x _; rw [hd]; exact ht n

section CommonPullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Differential matching for a change from a common chart to a native
chart.  It concerns the coordinate map, not the phase or its defect. -/
structure DirectionMatch (s : StripData E) (d : GraphDirections E)
    (s' : StripData E') (d' : GraphDirections E') (ψ : ℕ → E' → E) : Prop where
  maps : ∀ n, MapsTo (ψ n) s'.domain s.domain
  differentiable : ∀ n x, x ∈ s'.domain → DifferentiableAt ℝ (ψ n) x
  radial : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.radial = d.radial
  auxiliary : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.auxiliary = d.auxiliary
  angular : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.angular = d.angular
  axial : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.axial = d.axial
  fast : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x (d'.fastField n x) = d.fastField n (ψ n x)
  slow : ∀ n x, x ∈ s'.domain → fderiv ℝ (ψ n) x d'.slow = d.slow

theorem NativeCoordinates.comp
    {s : StripData E} {d : GraphDirections E} {χ : ℕ → E → Slot}
    (hχ : NativeCoordinates s d χ)
    {s' : StripData E'} {d' : GraphDirections E'} {ψ : ℕ → E' → E}
    (hψ : DirectionMatch s d s' d' ψ) :
    NativeCoordinates s' d' (fun n => χ n ∘ ψ n) := by
  have hd n x hx := fderiv_comp x (hχ.differentiable n (ψ n x) (hψ.maps n hx))
    (hψ.differentiable n x hx)
  refine ⟨fun n x hx => (hχ.differentiable n (ψ n x) (hψ.maps n hx)).comp x
    (hψ.differentiable n x hx), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.radial n x hx]
    exact hχ.radial n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.auxiliary n x hx]
    exact hχ.auxiliary n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.angular n x hx]
    exact hχ.angular n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.axial n x hx]
    exact hχ.axial n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.fast n x hx]
    exact hχ.fast n _ (hψ.maps n hx)
  · intro n x hx; rw [hd n x hx, ContinuousLinearMap.comp_apply, hψ.slow n x hx]
    exact hχ.slow n _ (hψ.maps n hx)

end CommonPullback

theorem differentiableAt_phase (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    DifferentiableAt ℝ (PhaseCalculus.phase ε p pz x0 F G) q := by
  have hi : DifferentiableAt ℝ (fun z : Slot => z) q := differentiableAt_id
  have hFl := hF.comp q hi.fst
  have hGl := hG.comp q hi.fst
  exact (((hi.snd.fst.const_mul p).add (hi.fst.snd.fst.const_mul (pz / ε))).add
    (hi.fst.fst.const_mul x0)).sub
      (hi.snd.snd.mul ((hFl.const_mul p).add (hGl.const_mul pz)))

/-- The algebraic expression after exact material cancellation. -/
noncomputable def expression (ε p pz x0 v b G FR GR FT GT FZ GZ : ℝ) : ℝ :=
  b * x0 - v * (b * (p * FR + pz * GR) - ε * (p * FT + pz * GT) +
    ε * G * (p * FZ + pz * GZ))

/-- A chart pullback of the actual phase has exactly the native backward
material derivative, using only the chart differential identities. -/
theorem material_pullback
    (χ : E → Slot) (ε p pz x0 : ℝ) (b F G : Slow → ℝ)
    (Vr Vθ Vz Vf Vs : E → E) {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hε : ε ≠ 0) (hR : 0 < (χ x).1.1)
    (hF : DifferentiableAt ℝ F (χ x).1) (hG : DifferentiableAt ℝ G (χ x).1)
    (hr : fderiv ℝ χ x (Vr x) = PhaseCalculus.eR)
    (hθ : fderiv ℝ χ x (Vθ x) = PhaseCalculus.eTheta)
    (hz : fderiv ℝ χ x (Vz x) = ε • PhaseCalculus.eZ)
    (hf : fderiv ℝ χ x (Vf x) = PhaseCalculus.eV)
    (hs : fderiv ℝ χ x (Vs x) = PhaseCalculus.eT) :
    LinearWaveResidual.materialPhaseDefect (fun y => (χ y).1.1)
      (fun y => b (χ y).1) (fun y => F (χ y).1) (fun y => G (χ y).1)
      Vr Vθ Vz (LinearWaveResidual.timeDirection ε Vf Vs)
      (PhaseCalculus.phase ε p pz x0 F G ∘ χ) x =
    expression ε p pz x0 (χ x).2.2 (b (χ x).1) (G (χ x).1)
      (PhaseCalculus.slowR F (χ x).1) (PhaseCalculus.slowR G (χ x).1)
      (PhaseCalculus.slowT F (χ x).1) (PhaseCalculus.slowT G (χ x).1)
      (PhaseCalculus.slowZ F (χ x).1) (PhaseCalculus.slowZ G (χ x).1) := by
  have hΦ := differentiableAt_phase ε p pz x0 F G (χ x) hF hG
  have hd := fderiv_comp x hΦ hχ
  have hcancel : PhaseCalculus.baseV F (χ x).1 / (χ x).1.1 = F (χ x).1 := by
    unfold PhaseCalculus.baseV
    field_simp
  calc
    _ = PhaseCalculus.backwardMaterialOp ε b F G (PhaseCalculus.phase ε p pz x0 F G) (χ x) := by
      unfold LinearWaveResidual.materialPhaseDefect HarmonicCalculus.along
      simp only [hd, ContinuousLinearMap.comp_apply, LinearWaveResidual.timeDirection,
        map_sub, map_smul, hr, hθ, hz, hf, hs, smul_eq_mul]
      unfold PhaseCalculus.backwardMaterialOp PhaseCalculus.signedMaterialOp
      rw [hcancel]
      ring
    _ = _ := PhaseCalculus.backwardMaterialOp_phase ε p pz x0 b F G (χ x) hε hR hF hG

/-- Direct class estimate for the exact expression.  The six derivatives
here are scalar coefficient families; the primary specialization below
derives their classes from actual base-field jets. -/
theorem expression_class {s : StripData E}
    {p pz x0 v b G FR GR FT GT FZ GZ : ℕ → E → ℝ}
    (hp : UnweightedClass s 0 p) (hpz : UnweightedClass s 0 pz)
    (hx0 : UnweightedClass s 0 x0) (hv : UnweightedClass s 0 v)
    (hb : UnweightedClass s 1 b) (hG : UnweightedClass s 0 G)
    (hFR : UnweightedClass s 0 FR) (hGR : UnweightedClass s 0 GR)
    (hFT : UnweightedClass s 0 FT) (hGT : UnweightedClass s 0 GT)
    (hFZ : UnweightedClass s 0 FZ) (hGZ : UnweightedClass s 0 GZ) :
    UnweightedClass s 1 (fun n x => expression (s.epsilon n) (p n x) (pz n x)
      (x0 n x) (v n x) (b n x) (G n x) (FR n x) (GR n x)
      (FT n x) (GT n x) (FZ n x) (GZ n x)) := by
  have hR : UnweightedClass s 0 (fun n x => p n x * FR n x + pz n x * GR n x) := by
    simpa only [zero_add] using (unweighted_mul hp hFR).add (unweighted_mul hpz hGR)
  have hT : UnweightedClass s 0 (fun n x => p n x * FT n x + pz n x * GT n x) := by
    simpa only [zero_add] using (unweighted_mul hp hFT).add (unweighted_mul hpz hGT)
  have hZ : UnweightedClass s 0 (fun n x => p n x * FZ n x + pz n x * GZ n x) := by
    simpa only [zero_add] using (unweighted_mul hp hFZ).add (unweighted_mul hpz hGZ)
  have hbR : UnweightedClass s 1 (fun n x => b n x *
      (p n x * FR n x + pz n x * GR n x)) := by
    simpa only [add_zero] using unweighted_mul hb hR
  have heT : UnweightedClass s 1 (fun n x => s.epsilon n *
      (p n x * FT n x + pz n x * GT n x)) := by
    simpa only [zero_add, smul_eq_mul] using hT.band_smul (band_epsilon s)
  have heZ : UnweightedClass s 1 (fun n x => s.epsilon n * G n x *
      (p n x * FZ n x + pz n x * GZ n x)) := by
    simpa only [zero_add, smul_eq_mul, mul_assoc] using
      (unweighted_mul hG hZ).band_smul (band_epsilon s)
  have hinside := (class_sub hbR heT).add heZ
  have hfirst : UnweightedClass s 1 (fun n x => b n x * x0 n x) := by
    simpa only [add_zero] using unweighted_mul hb hx0
  have htail : UnweightedClass s 1 (fun n x => v n x *
      (b n x * (p n x * FR n x + pz n x * GR n x) -
        s.epsilon n * (p n x * FT n x + pz n x * GT n x) +
        s.epsilon n * G n x * (p n x * FZ n x + pz n x * GZ n x))) := by
    simpa only [zero_add] using unweighted_mul hv hinside
  exact class_sub hfirst htail

/-- Polynomial base jets compose with the actual slow coordinate map.
The angular coordinate is absent from this quantitative hypothesis. -/
theorem polynomial_comp_unweighted
    {s : StripData E} {U : PhaseJetBounds.Domain ℕ Slow}
    {f : ℕ → Slow → ℝ} (hf : PhaseJetBounds.PolynomialJets U f)
    {c : ℕ → E → Slow} (hc : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) c)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (c n) s.domain (U.carrier n)) :
    UnweightedClass s 0 (fun n x => f n (c n x)) :=
  ((PrimaryPulseBounds.EnvelopeJets.of_polynomial hf).comp hc hscale hmap).memClass s
    (fun _ => rfl) (fun _ => rfl)

/-- The same composition result allows polynomial inverse-edge losses in
the slow chart itself.  This is a quantitative chain-rule estimate, not
an assumption about the pulled-back base derivatives. -/
theorem polynomial_comp_with_edges
    {s : StripData E} {U : PhaseJetBounds.Domain ℕ Slow}
    {f : ℕ → Slow → ℝ} (hf : PhaseJetBounds.PolynomialJets U f)
    {c : ℕ → E → Slow} (hc : UnweightedClass s 0 c)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (c n) s.domain (U.carrier n)) :
    UnweightedClass s 0 (fun n x => f n (c n x)) := by
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf.smooth n).comp (hc.smooth n) (hmap n), ?_⟩
  intro N
  obtain ⟨A, hA, m, ha⟩ := hf.bound N
  obtain ⟨B, hB, k, hb⟩ := hc.bounds N
  refine ⟨(N.factorial : ℝ) * A * (B + 1) ^ N, by positivity, m + k * N, ?_⟩
  intro n x hx j hj
  have hg0 := s.growth_nonneg n x
  have hg1 := s.one_le_growth n x
  have hD : 1 ≤ (B + 1) * s.growth n x ^ k :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hg1)
  have hinner (a : ℕ) (haN : a ≤ N) :
      ‖iteratedFDeriv ℝ a (c n) x‖ ≤ (B + 1) * s.growth n x ^ k := by
    have hh := hb n x hx a haN
    simp only [majorant, Real.rpow_zero, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hg0 _))
  have houter (a : ℕ) (haN : a ≤ N) :
      ‖iteratedFDeriv ℝ a (f n) (c n x)‖ ≤ A * s.growth n x ^ m := by
    have hh := ha n a haN _ (hmap n hx)
    rw [hscale n] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) _)
      (zero_le_one.trans hA))
  have hn : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have hchain := norm_iteratedFDerivWithin_comp_le (hf.smooth n) (hc.smooth n) hn
    (U.isOpen n).uniqueDiffOn s.isOpen_domain.uniqueDiffOn (hmap n) hx
    (C := A * s.growth n x ^ m) (D := (B + 1) * s.growth n x ^ k)
    (fun a haj => ?_) (fun a ha1 haj => ?_)
  · rw [iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx] at hchain
    simp only [majorant, Real.rpow_zero, mul_one]
    calc
      _ ≤ (j.factorial : ℝ) * (A * s.growth n x ^ m) * ((B + 1) * s.growth n x ^ k) ^ j := hchain
      _ ≤ (N.factorial : ℝ) * (A * s.growth n x ^ m) * ((B + 1) * s.growth n x ^ k) ^ N := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity)
        · exact pow_le_pow_right₀ hD hj
        · positivity
        · positivity
      _ = _ := by rw [mul_pow, pow_add, pow_mul]; ring
  · rw [iteratedFDerivWithin_of_isOpen a (U.isOpen n) (hmap n hx)]
    exact houter a (haj.trans hj)
  · rw [iteratedFDerivWithin_of_isOpen a s.isOpen_domain hx]
    exact (hinner a (haj.trans hj)).trans (by simpa using pow_le_pow_right₀ hD ha1)

/-- The actual affine clock has polynomial jets from its value and linear
coefficient bounds.  This supplies the slot-coordinate class in either
native or common coordinates. -/
theorem affine_slot_class (s : StripData E) (L : ℕ → E →L[ℝ] ℝ) (c : ℕ → ℝ)
    {C : ℝ} {m : ℕ} (hC : 1 ≤ C)
    (hL : ∀ n, ‖L n‖ ≤ C * s.slow n ^ m)
    (hv : ∀ n x, x ∈ s.domain → |L n x + c n| ≤ C * s.slow n ^ m) :
    UnweightedClass s 0 (fun n x => L n x + c n) := by
  apply PrimaryPulseBounds.polynomial_memClass s
  refine ⟨fun n => (L n).contDiff.contDiffOn.add contDiffOn_const, fun _ => ⟨C, hC, m, ?_⟩⟩
  intro n j _ x hx
  have hd : fderiv ℝ (fun y => L n y + c n) = fun _ => L n := by
    funext y
    exact ((L n).hasFDerivAt.add_const (c n)).fderiv
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, PrimaryPulseBounds.phaseDomain]
    using hv n x hx
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv, hd]
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero, PrimaryPulseBounds.phaseDomain] using hL n
      | succ j =>
          rw [iteratedFDeriv_succ_const]
          simp only [Pi.zero_apply, norm_zero]
          exact mul_nonneg (zero_le_one.trans hC)
            (pow_nonneg (zero_le_one.trans (s.one_le_slow n)) _)

section Primary

variable {U : PhaseJetBounds.Domain ℕ Slow}

noncomputable def pulledPhase (P : PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → E → Slot) (n : ℕ) (x : E) : ℝ :=
  PhaseCalculus.phase (P.phase.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
    (P.phase.F n) (P.phase.G n) (χ n x)

/-- Canonical raw geometry with arbitrary amplitude/pressure.  Those two
fields do not enter the material defect.  The angular base field here is
the frequency `F`, as required by `LinearWaveResidual`, not `R*F`. -/
noncomputable def coefficients (P : PrimaryPulseBounds.PhaseConstruction U)
    (b : ℕ → Slow → ℝ) (χ : ℕ → E → Slot)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ) : WaveCoefficients E where
  radius n x := (χ n x).1.1
  radialBase n x := b n (χ n x).1
  frequencyBase n x := P.phase.F n (χ n x).1
  axialBase n x := P.phase.G n (χ n x).1
  phase := pulledPhase P χ
  amplitude := amplitude
  pressure := pressure
  frequency := frequency

theorem defect_formula (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ)
    (hχ : NativeCoordinates s d χ)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (n : ℕ) {x : E} (hx : x ∈ s.domain) (hR : 0 < (χ n x).1.1) :
    (coefficients P b χ amplitude pressure frequency).defect s d n x =
      expression (s.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
        (χ n x).2.2 (b n (χ n x).1) (P.phase.G n (χ n x).1)
        (PhaseCalculus.slowR (P.phase.F n) (χ n x).1)
        (PhaseCalculus.slowR (P.phase.G n) (χ n x).1)
        (PhaseCalculus.slowT (P.phase.F n) (χ n x).1)
        (PhaseCalculus.slowT (P.phase.G n) (χ n x).1)
        (PhaseCalculus.slowZ (P.phase.F n) (χ n x).1)
        (PhaseCalculus.slowZ (P.phase.G n) (χ n x).1) := by
  have hF := ((P.baseF.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
    (by simp)
  have hG := ((P.baseG.smooth n).contDiffAt ((U.isOpen n).mem_nhds (hmap n hx))).differentiableAt
    (by simp)
  have hm := material_pullback (χ n) (s.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
    (b n) (P.phase.F n) (P.phase.G n) (d.radialField n) (fun _ => d.angular)
    (d.axialField s n) (d.fastField n) (fun _ => d.slow)
    (hχ.differentiable n x hx) (s.epsilon_pos n).ne' hR hF hG
    (hχ.radialField n hx) (hχ.angular n x hx) (hχ.axialField n hx)
    (hχ.fast n x hx) (hχ.slow n x hx)
  have hpull : pulledPhase P χ n =
      PhaseCalculus.phase (s.epsilon n) (P.phase.p n) (P.phase.pz n) (P.phase.x0 n)
        (P.phase.F n) (P.phase.G n) ∘ χ n := by
    funext y
    simp only [pulledPhase, heps n, Function.comp_apply]
  simp only [WaveCoefficients.defect, coefficients]
  rw [hpull]
  exact hm

theorem frozen_classes (P : PrimaryPulseBounds.PhaseConstruction U) (s : StripData E) :
    UnweightedClass s 0 (fun n _ => P.phase.p n) ∧
    UnweightedClass s 0 (fun n _ => P.phase.pz n) ∧
    UnweightedClass s 0 (fun n _ => P.phase.x0 n) := by
  have hconst (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ P.M) :
      UnweightedClass s 0 (fun n _ => c n) := by
    apply PrimaryPulseBounds.polynomial_memClass s
    exact PhaseJetBounds.PolynomialJets.const_uniform c P.one_le_M
      (fun n => by simpa only [Real.norm_eq_abs] using hc n)
  exact ⟨hconst _ (fun n => (P.constants n).2.1),
    hconst _ (fun n => (P.constants n).2.2.1), hconst _ (fun n => (P.constants n).2.2.2)⟩

/-- Actual all-order defect bounds from base jets and primitive chart
data.  The six base-derivative classes are derived in the proof. -/
theorem defect_class (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ)
    (hχ : NativeCoordinates s d χ)
    (hslow : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) (fun n x => (χ n
      x).1))
    (hslot : UnweightedClass s 0 (fun n x => (χ n x).2.2))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hb : UnweightedClass s 1 (fun n x => b n (χ n x).1)) :
    UnweightedClass s 1 ((coefficients P b χ amplitude pressure frequency).defect s d) := by
  obtain ⟨hp, hpz, hx0⟩ := frozen_classes P s
  have hG := polynomial_comp_unweighted P.baseG hslow hscale hmap
  have hFR := polynomial_comp_unweighted (P.baseF.directional (1, (0, 0))) hslow hscale hmap
  have hGR := polynomial_comp_unweighted (P.baseG.directional (1, (0, 0))) hslow hscale hmap
  have hFT := polynomial_comp_unweighted (P.baseF.directional (0, (0, 1))) hslow hscale hmap
  have hGT := polynomial_comp_unweighted (P.baseG.directional (0, (0, 1))) hslow hscale hmap
  have hFZ := polynomial_comp_unweighted (P.baseF.directional (0, (1, 0))) hslow hscale hmap
  have hGZ := polynomial_comp_unweighted (P.baseG.directional (0, (1, 0))) hslow hscale hmap
  have he := expression_class hp hpz hx0 hslot hb hG hFR hGR hFT hGT hFZ hGZ
  apply class_congr he
  intro n x hx
  exact (defect_formula P s d χ b amplitude pressure frequency hχ hmap heps n hx (hR n x hx)).symm

theorem defect_class_of_mean (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (amplitude : ℕ → E → HarmonicCalculus.ComplexVector)
    (pressure : ℕ → E → ℂ) (frequency : ℕ → ℝ)
    (hχ : NativeCoordinates s d χ)
    (hslow : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) (fun n x => (χ n
      x).1))
    (hslot : UnweightedClass s 0 (fun n x => (χ n x).2.2))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hb : MeanClass s 1 (fun n x => b n (χ n x).1)) :
    UnweightedClass s 1 ((coefficients P b χ amplitude pressure frequency).defect s d) :=
  defect_class P s d χ b amplitude pressure frequency hχ hslow hslot hscale hmap heps hR
    (mean_unweighted hb hζ)

/-- Field matching binds an existing wave record to the exact phase.  It
does not assume equality or bounds of its material defect. -/
theorem defect_class_of_fields (P : PrimaryPulseBounds.PhaseConstruction U)
    (s : StripData E) (d : GraphDirections E) (χ : ℕ → E → Slot) (b : ℕ → Slow → ℝ)
    (a : WaveCoefficients E)
    (hχ : NativeCoordinates s d χ)
    (hslow : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) (fun n x => (χ n
      x).1))
    (hslot : UnweightedClass s 0 (fun n x => (χ n x).2.2))
    (hscale : ∀ n, U.scale n = s.slow n)
    (hmap : ∀ n, MapsTo (fun x => (χ n x).1) s.domain (U.carrier n))
    (heps : ∀ n, P.phase.epsilon n = s.epsilon n)
    (hR : ∀ n x, x ∈ s.domain → 0 < (χ n x).1.1)
    (hb : UnweightedClass s 1 (fun n x => b n (χ n x).1))
    (hbfield : a.radialBase = fun n x => b n (χ n x).1)
    (hFfield : a.frequencyBase = fun n x => P.phase.F n (χ n x).1)
    (hGfield : a.axialBase = fun n x => P.phase.G n (χ n x).1)
    (hphase : a.phase = pulledPhase P χ) : UnweightedClass s 1 (a.defect s d) := by
  have hd := defect_class P s d χ b a.amplitude a.pressure a.frequency
    hχ hslow hslot hscale hmap heps hR hb
  apply class_congr hd
  intro n x _
  simp only [WaveCoefficients.defect, LinearWaveResidual.materialPhaseDefect,
    coefficients, hbfield, hFfield, hGfield, hphase]

end Primary

/-- One finite-prefix constant and one polynomial degree work for every
band and point.  This is the explicit jet form of the order-one class. -/
theorem finite_jet_bounds {s : StripData E} {f : ℕ → E → ℝ}
    (hf : UnweightedClass s 1 f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ C * s.epsilon n * s.growth n x ^ p := by
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun n x hx j hj => by
    simpa only [majorant, Real.rpow_one, mul_one] using hb n x hx j hj⟩

end NavierStokes.PrimaryMaterialDefect
