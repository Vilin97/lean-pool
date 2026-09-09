/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledActualParticularControl

/-!
# Geometric jets for the actual scaled particular inverse

The normal, its native time derivative, and the action operator are
computed from the selected transported frame. Their native-copy jets
follow from the selected phase construction and the polynomial coordinate
cost, without estimates on a solved velocity or pressure as hypotheses.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ScaledParticularFrameJets

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds
open CommonCoverSolve TorusInverse ParticularWaveBounds PeriodizedWaveBounds
open ActualParticularControl
open scoped Topology ContDiff BigOperators

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane


section FrameAlgebra

variable {ι Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {U : Domain ι (Q × ℝ)} {d : ι → PrimaryODE.FrameData Q}

theorem frame_normal_jets (h : FrameJets U d) :
    PolynomialJets U (fun i => (d i).normal) := by
  exact ((h.beta.mul h.rho).pair (h.beta.smul h.K)).clm MovingFrameODE.packCLM

theorem frame_motion_jets (h : FrameJets U d) :
    PolynomialJets U (fun i => (d i).normalMotion) := by
  exact (((h.betaDot.mul h.rho).add (h.beta.mul h.rhoDot)).pair
    ((h.betaDot.smul h.K).add ((h.beta.mul h.rotation).smul h.N))).clm MovingFrameODE.packCLM

theorem frame_action_jets (h : FrameJets U d) :
    PolynomialJets U (fun i z => PrimaryCopyBridge.baseOperator ((d i).F z) ((d i).shear z)) :=
  (h.F.pair h.shear).clm PrimaryCopyBridge.baseOperatorFamily

end FrameAlgebra

section UniformAffine

variable {Label I X Q E : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The translation may depend on the lattice copy; its size never
enters a derivative bound. -/
theorem polynomial_native_jets (s : StripData X)
    {U : Domain (Label × ℕ) Q} {f : (Label × ℕ) → Q → E}
    (hf : PolynomialJets U f) (C : Label → ℕ → I → Set X)
    (L : Label → ℕ → X →L[ℝ] Q) (b : Label → ℕ → I → Q)
    (hscale : ∀ l n, U.scale (l, n) = s.slow n)
    {A : ℝ} {a : ℕ} (hA : 1 ≤ A)
    (hL : ∀ l n, ‖L l n‖ ≤ A * s.slow n ^ a)
    (hmap : ∀ l n k x, x ∈ s.domain → x ∈ C l n k → L l n x + b l n k ∈ U.carrier (l, n)) :
    UniformLocalJets s (fun _ _ _ => 1) 0 C
      (fun l n k x => f (l,n) (L l n x + b l n k)) := by
  let V : PrimaryCopyBounds.JetDomain (Label × ℕ) Q :=
    { toDomain := U
      growth := fun i _ => U.scale i
      scale_le_growth := fun _ _ _ => le_rfl }
  have hn : PrimaryCopyBounds.NativeJets V (fun _ _ => 1) f :=
    PrimaryCopyBounds.NativeJets.of_polynomial hf
  apply hn.copy_localJets s (fun _ _ _ => 1) 0 (fun l n => (l,n))
    (fun l n _ => L l n) b C (fun _ _ _ _ => zero_le_one) hmap
    (A := 1) (B := A) le_rfl hA 1 a
  · intro l n k x hx hk
    change U.scale (l,n) ≤ 1 * s.growth n x ^ 1
    simpa only [hscale, pow_one, one_mul] using s.slow_le_growth n x
  · intro l n k
    exact hL l n
  · intro l n k x hx hk
    simp only [Real.rpow_zero, mul_one, le_refl]

end UniformAffine

section NativeCoordinates

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Argument, given by `(χ x.1, (g.coordinates k x.2).2)`. -/
noncomputable def argument (χ : P →L[ℝ] Slow) (g : Geometry) (k : Frequency)
    (x : P × Plane) : Slow × ℝ := (χ x.1, (g.coordinates k x.2).2)

/-- Argument linear as an element of `(P × Plane) →L[ℝ] (Slow × ℝ)`. -/
noncomputable def argumentLinear (χ : P →L[ℝ] Slow) (g : Geometry) :
    (P × Plane) →L[ℝ] (Slow × ℝ) :=
  (χ.comp (ContinuousLinearMap.fst ℝ P Plane)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P
        Plane)))

theorem argument_affine (χ : P →L[ℝ] Slow) (g : Geometry) (k : Frequency) (x : P × Plane) :
    argument χ g k x = argumentLinear χ g x + (0,(g.coordinates k 0).2) := by
  change (χ x.1, (g.coordinates k x.2).2) = (χ x.1+0, (g.coordinateLinear x.2).2+(g.coordinates k
      0).2)
  rw [g.coordinates_eq_affine]
  simp only [Prod.snd_add, zero_add, add_comm]

theorem argumentLinear_norm (χ : P →L[ℝ] Slow) (g : Geometry) :
    ‖argumentLinear χ g‖ ≤ ‖χ‖ + CommonCoverClass.argumentCost g := by
  have hg : 0 ≤ CommonCoverClass.argumentCost g := zero_le_one.trans
      (CommonCoverClass.one_le_argumentCost g)
  have hc : ‖g.coordinateLinear‖ ≤ CommonCoverClass.argumentCost g := by
    unfold CommonCoverClass.argumentCost
    have hh : 0 ≤ ‖g.pointLinear‖ * (1+‖g.coordinateLinear‖) := by positivity
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) hg)
  intro x
  change ‖(χ x.1, (g.coordinateLinear x.2).2)‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · exact (χ.le_opNorm x.1).trans ((mul_le_mul_of_nonneg_left (norm_fst_le x) (norm_nonneg χ)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hg) (norm_nonneg x)))
  · exact (norm_snd_le (g.coordinateLinear x.2)).trans ((g.coordinateLinear.le_opNorm x.2).trans
      ((mul_le_mul hc (norm_snd_le x) (norm_nonneg x.2) hg).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg χ)) (norm_nonneg x))))

theorem argument_smooth (χ : P →L[ℝ] Slow) (g : Geometry) (k : Frequency) :
    ContDiff ℝ ∞ (argument χ g k) := by
  have he : argument χ g k = fun x => argumentLinear χ g x+(0,(g.coordinates k 0).2) :=
    funext (argument_affine χ g k)
  rw [he]
  exact (argumentLinear χ g).contDiff.add contDiff_const

end NativeCoordinates

section ActualJets

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : Domain (Label × ℕ) Slow}
  (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] Slow)
  (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
  (clock normal : ActualSignedControl.PositiveScale Label)
  (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)

/-- Tangent, given by `PrimaryCopyBridge.frameTangentData (nativeFrame
(ScaledActualParticularControl.frame F φ clock normal (l,n)) χ) j (source l n)`. -/
noncomputable def tangent (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) : TangentData P Space :=
  PrimaryCopyBridge.frameTangentData
    (nativeFrame (ScaledActualParticularControl.frame F φ clock normal (l,n)) χ) j (source l n)

theorem argument_mem {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    argument χ (g l n) k x ∈
      ((ScaledActualParticularControl.targetDomain (D := D) s φ).slot
        (ScaledActualParticularControl.interval F clock)
        (ScaledActualParticularControl.interval_open F clock)).carrier (l,n) :=
  ⟨hx.1.2.1, ScaledActualParticularControl.interval_contains F clock (l,n)
    ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩⟩

theorem frame_field_native_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Label × ℕ) → Slow × ℝ → E}
    (hf : PolynomialJets
      ((ScaledActualParticularControl.targetDomain (D := D) s φ).slot
        (ScaledActualParticularControl.interval F clock)
        (ScaledActualParticularControl.interval_open F clock)) f)
    {C : ℝ} {a : ℕ} (hC : 1 ≤ C)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ C * s.slow n ^ a) :
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => f (l,n) (argument χ (g l n) k x)) := by
  have hL l n : ‖argumentLinear χ (g l n)‖ ≤ (‖χ‖+C)*s.slow n^a := by
    apply (argumentLinear_norm χ (g l n)).trans
    have hs := one_le_pow₀ (s.one_le_slow n) (n := a)
    have hp := mul_le_mul_of_nonneg_left hs (norm_nonneg χ)
    nlinarith [hgeometry l n]
  have hj := polynomial_native_jets (CommonCoverClass.sourceStrip s) hf
    (ScaledActualParticularControl.patch s F χ φ clock g r)
    (fun l n => argumentLinear χ (g l n)) (fun l n k => (0,(g l n).coordinates k 0 |>.2))
    (fun _ _ => rfl) (A := ‖χ‖+C) (a := a) (by linarith [norm_nonneg χ]) hL
    (fun l n k x hx hk => by
      rw [← argument_affine]
      exact argument_mem s F χ φ clock g r hk)
  simpa only [← argument_affine] using hj

theorem native_normal_eq (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) (k : Frequency) (x : P × Plane) :
    (tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k x)
        =
      (ScaledActualParticularControl.frame F φ clock normal (l,n)).normal (argument χ (g l n) k x)
          := rfl

theorem native_motion_eq (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) (k : Frequency) (x : P × Plane) :
    (tangent F χ φ clock normal source j l n).normalDot (ParticularWaveBounds.nativePoint (g l n) k
        x) =
      (ScaledActualParticularControl.frame F φ clock normal (l,n)).normalMotion (argument χ (g l n)
          k x) := rfl

theorem native_action_eq (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    (l : Label) (n : ℕ) (k : Frequency) (x : P × Plane) :
    (tangent F χ φ clock normal source j l n).action (ParticularWaveBounds.nativePoint (g l n) k x)
        =
      PrimaryCopyBridge.baseOperator
        ((ScaledActualParticularControl.frame F φ clock normal (l,n)).F (argument χ (g l n) k x))
        ((ScaledActualParticularControl.frame F φ clock normal (l,n)).shear (argument χ (g l n) k
            x)) := rfl

/-- These are the three actual geometric inputs needed by the pressure
estimate in `ParticularCopyBounds.uniform_coefficients_jets`. -/
theorem native_geometry_jets
    (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    {A B C : ℝ} {a : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hφ : ∀ i, ‖φ i‖ ≤ A) (hscale : ∀ i, D.scale i ≤ B * s.slow i.2)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ C * s.slow n ^ a) :
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => (tangent F χ φ clock normal source j l n).normal
        (ParticularWaveBounds.nativePoint (g l n) k x)) ∧
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => (tangent F χ φ clock normal source j l n).normalDot
        (ParticularWaveBounds.nativePoint (g l n) k x)) ∧
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (fun l n k x => (tangent F χ φ clock normal source j l n).action
        (ParticularWaveBounds.nativePoint (g l n) k x)) := by
  have hd := ScaledActualParticularControl.frame_jets s F φ clock normal hA hB hφ hscale
  exact ⟨frame_field_native_jets s F χ φ clock g r (frame_normal_jets hd) hC hgeometry,
    frame_field_native_jets s F χ φ clock g r (frame_motion_jets hd) hC hgeometry,
    frame_field_native_jets s F χ φ clock g r (frame_action_jets hd) hC hgeometry⟩

end ActualJets

section NormalRange

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : Domain (Label × ℕ) Slow}
  (s : StripData P) (F : PhaseConstruction D) (χ : P →L[ℝ] Slow)
  (φ : (Label × ℕ) → Slow →L[ℝ] Slow)
  (clock normal : ActualSignedControl.PositiveScale Label)
  (g : Label → ℕ → Geometry) (r : Label → ℕ → ℝ)

/-- The frame reconstructed from the selected actual phase has exactly
that phase's normal; the nonzero transverse normal follows from its
proved reference comparison. -/
theorem selected_frame_normal_eq {i : Label × ℕ} {z : Slow × ℝ}
    (hz : z ∈ (D.slot F.V F.openV).carrier i) :
    (F.frame i).normal z = F.phase.normal i z := by
  have ht := (normal_range_of_reference_close F.B F.K F.slope F.error
    F.b_pos F.one_le_M F.B_bound F.K_unit F.slope_bound F.error_small F.normal_close).1 i z hz
  have hn : MovingFrameODE.tail (F.phase.normal i z) ≠ 0 :=
    norm_pos_iff.mp (F.b_pos.trans_le ht)
  exact PrimaryODE.FrameData.ofNormalLocal_normal _ _ _ _ _ _ _ _ hn

theorem native_normal_eq_scaled (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    (tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k x)
        =
      normal.value l n • F.phase.normal (l,n)
        (φ (l,n) (χ x.1), clock.value l n * ((g l n).coordinates k x.2).2) := by
  rw [native_normal_eq]
  change (transportedFrame (F.frame (l,n)) (φ (l,n)) 0 (clock.value l n) (normal.value l n)).normal
    (argument χ (g l n) k x) = _
  rw [transported_normal]
  simp only [argument, zero_add]
  congr 1
  exact selected_frame_normal_eq F ⟨hx.1.2.1,
    F.interval (l,n) (ScaledActualParticularControl.clock_mem F clock
        ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩)⟩

theorem normal_lower_pos : 0 < normal.lower * F.b := mul_pos normal.lower_pos F.b_pos

/-- Both range constants precede every label, band, native copy and
evaluation point. There is no inverse dependence on the clock rate. -/
theorem native_normal_bounds (source : Label → ℕ → P × Plane → Space) (j : ℤ)
    {l : Label} {n : ℕ} {k : Frequency} {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    normal.lower * F.b ≤
      ‖(tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k
          x)‖ ∧
    ‖(tangent F χ φ clock normal source j l n).normal (ParticularWaveBounds.nativePoint (g l n) k
        x)‖ ≤
      normal.upper * (F.M^2 + 3*F.M) := by
  rw [native_normal_eq_scaled s F χ φ clock normal g r source j hx,
    norm_smul, Real.norm_eq_abs, abs_of_pos (normal.value_pos l n)]
  have hz : (φ (l,n) (χ x.1), clock.value l n * ((g l n).coordinates k x.2).2) ∈
      (D.slot F.V F.openV).carrier (l,n) :=
    ⟨hx.1.2.1, F.interval (l,n)
      (ScaledActualParticularControl.clock_mem F clock ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩)⟩
  constructor
  · exact (mul_le_mul_of_nonneg_right (normal.bounds l n).1 F.b_pos.le).trans
      (mul_le_mul_of_nonneg_left (F.normal_range.1 (l,n) _ hz) (normal.value_pos l n).le)
  · exact (mul_le_mul_of_nonneg_right (normal.bounds l n).2 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (F.normal_range.2 (l,n) _ hz) (zero_le_one.trans normal.upper_one))

end NormalRange

end NavierStokes.ScaledParticularFrameJets
