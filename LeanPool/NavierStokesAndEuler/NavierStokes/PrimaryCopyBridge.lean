/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryODE
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverSolve

@[expose] public section

/-!
# The reconstructed forced solution is the actual copy solve

The frame is reindexed along the native transverse coordinate of each copy,
while the physical source is evaluated on the lifted earlier path.  Uniqueness
identifies the two constructed solutions from their common zero entry value.
No energy inequality for the ambient projected operator is assumed.
-/

noncomputable section

namespace NavierStokes.PrimaryCopyBridge

open Set Filter
open scoped Topology ContDiff InnerProductSpace

abbrev Plane := TorusInverse.Plane
abbrev Frequency := TorusInverse.Frequency
abbrev State := PrimaryODE.State
abbrev Space := PrimaryODE.Space

/-! ## Exact reindexing of primitive frame data -/

noncomputable def reindex {P Q : Type} (d : PrimaryODE.FrameData P) (φ : Q → P) :
    PrimaryODE.FrameData Q where
  beta z := d.beta (φ z.1, z.2)
  betaDot z := d.betaDot (φ z.1, z.2)
  rho z := d.rho (φ z.1, z.2)
  rhoDot z := d.rhoDot (φ z.1, z.2)
  rotation z := d.rotation (φ z.1, z.2)
  F z := d.F (φ z.1, z.2)
  shear z := d.shear (φ z.1, z.2)
  frame z := d.frame (φ z.1, z.2)
  eigenvalue z := d.eigenvalue (φ z.1, z.2)
  eigenvector z := d.eigenvector (φ z.1, z.2)
  eigenRate z := d.eigenRate (φ z.1, z.2)
  viscosity z := d.viscosity (φ z.1, z.2)

theorem reindex_kinematics {P Q : Type} (d : PrimaryODE.FrameData P) (φ : Q → P)
    {q : Q} {I : Set ℝ} (h : d.Kinematics (φ q) I) : (reindex d φ).Kinematics q I := by
  exact ⟨h.beta_ne_zero, h.eigenvector_ne_zero, h.beta_deriv, h.rho_deriv,
    h.eigenvector_deriv, h.frameK_deriv, h.frameN_deriv⟩

noncomputable def copyParameter {P : Type} (g : CommonCoverSolve.Geometry)
    (k : Frequency) (q : P × Plane) : P × ℝ := (q.1, (g.coordinates k q.2).1)

noncomputable def copyFrame {P : Type} (d : PrimaryODE.FrameData (P × ℝ))
    (g : CommonCoverSolve.Geometry) (k : Frequency) : PrimaryODE.FrameData (P × Plane) :=
  reindex d (copyParameter g k)

noncomputable def copySource {P : Type} (f : P × Plane → Space)
    (g : CommonCoverSolve.Geometry) (k : Frequency) (z : (P × Plane) × ℝ) : Space :=
  f (z.1.1, g.path k z.1.2 z.2)

@[simp] theorem copyFrame_normal {P : Type} (d : PrimaryODE.FrameData (P × ℝ))
    (g : CommonCoverSolve.Geometry) (k : Frequency) (z : (P × Plane) × ℝ) :
    (copyFrame d g k).normal z = d.normal (copyParameter g k z.1, z.2) := rfl

@[simp] theorem copyFrame_normalMotion {P : Type} (d : PrimaryODE.FrameData (P × ℝ))
    (g : CommonCoverSolve.Geometry) (k : Frequency) (z : (P × Plane) × ℝ) :
    (copyFrame d g k).normalMotion z = d.normalMotion (copyParameter g k z.1, z.2) := rfl

@[simp] theorem copyFrame_ambient {P : Type} (d : PrimaryODE.FrameData (P × ℝ))
    (g : CommonCoverSolve.Geometry) (k : Frequency) (z : (P × Plane) × ℝ) (w : State) :
    (copyFrame d g k).ambient z w = d.ambient (copyParameter g k z.1, z.2) w := rfl

theorem ambient_zero {P : Type} (d : PrimaryODE.FrameData P) (z : P × ℝ) :
    d.ambient z 0 = 0 := by
  ext i
  fin_cases i <;> simp [PrimaryODE.FrameData.ambient, MovingFrameODE.tangent, MovingFrameODE.pack]

/-! ## The native tangent data can be built directly from the frame -/

noncomputable def baseOperator (F : ℝ) (g : State) : Space →L[ℝ] Space :=
  MovingFrameODE.packCLM.comp
    (((-2 * F) • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1).prod
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).smulRight
        ((2 * F) • MovingFrameODE.unitTheta + g)))

@[simp] theorem baseOperator_apply (F : ℝ) (g : State) (x : Space) :
    baseOperator F g x = MovingFrameODE.baseAction F g x := rfl

noncomputable def nativePoint {P : Type} (z : P × Plane) : (P × ℝ) × ℝ :=
  ((z.1, z.2.1), z.2.2)

noncomputable def frameTangentData {P : Type} (d : PrimaryODE.FrameData (P × ℝ))
    (j : ℤ) (f : P × Plane → Space) : CommonCoverSolve.TangentData P Space where
  normal z := d.normal (nativePoint z)
  normalDot z := d.normalMotion (nativePoint z)
  action z := baseOperator (d.F (nativePoint z)) (d.shear (nativePoint z))
  damping z := d.damping j (nativePoint z)
  source := f

/-- Only primitive input fields are compared.  The structure contains no
equation, estimate, or identity concerning either output solution. -/
structure FrameMatchesAt {P : Type} (d : PrimaryODE.FrameData (P × ℝ))
    (t : CommonCoverSolve.TangentData P Space) (j : ℤ) (q : P × ℝ) (I : Set ℝ) : Prop where
  normal : ∀ v ∈ I, t.normal (q.1, (q.2, v)) = d.normal (q, v)
  normalMotion : ∀ v ∈ I, t.normalDot (q.1, (q.2, v)) = d.normalMotion (q, v)
  action : ∀ v ∈ I, ∀ x : Space,
    t.action (q.1, (q.2, v)) x = MovingFrameODE.baseAction (d.F (q, v)) (d.shear (q, v)) x
  damping : ∀ v ∈ I, t.damping (q.1, (q.2, v)) = d.damping j (q, v)

theorem frameTangentData_matches {P : Type} (d : PrimaryODE.FrameData (P × ℝ))
    (j : ℤ) (f : P × Plane → Space) (q : P × ℝ) (I : Set ℝ) :
    FrameMatchesAt d (frameTangentData d j f) j q I := by
  constructor
  · intro v hv; rfl
  · intro v hv; rfl
  · intro v hv x; rfl
  · intro v hv; rfl

/-! ## Uniqueness with continuity only along the actual finite copy paths -/

section PathUniqueness

variable {P V H : Type} [NormedAddCommGroup P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {a b : ℝ}

theorem anchoredSolve_hasDerivAt_along
    (d : CommonCoverSolve.LinearData P V H) (g : CommonCoverSolve.Geometry)
    (hab : a ≤ b) (k : Frequency) {Ω : Set (P × Plane)}
    (hA : ContinuousOn (d.coefficientAlong g k) (Ω ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcingAlong g k) (Ω ×ˢ Icc a b))
    {q : P × Plane} (hq : q ∈ Ω) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (d.anchoredSolve g hab k q)
      (d.coefficientAlong g k (q, v) (d.anchoredSolve g hab k q v) + d.forcingAlong g k (q, v)) v
        := by
  have hAc := SmoothPathFamily.slice_continuous hA hq
  have hfc := SmoothPathFamily.slice_continuous hf hq
  have hd := ParametricODE.solutionExtension_hasDerivAt hab
    (d.coefficientPath g k q) 0 (d.forcingPath g k q) ⟨v, hv⟩
  unfold CommonCoverSolve.LinearData.anchoredSolve
  simpa only [CommonCoverSolve.LinearData.anchoredSolve,
    CommonCoverSolve.LinearData.coefficientPath, CommonCoverSolve.LinearData.forcingPath,
    SmoothPathFamily.pathFamily_apply _ _ hAc, SmoothPathFamily.pathFamily_apply _ _ hfc] using hd

theorem anchoredSolve_unique_along
    (d : CommonCoverSolve.LinearData P V H) (g : CommonCoverSolve.Geometry)
    (hab : a ≤ b) (k : Frequency) {Ω : Set (P × Plane)}
    (hA : ContinuousOn (d.coefficientAlong g k) (Ω ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcingAlong g k) (Ω ×ˢ Icc a b))
    {q : P × Plane} (hq : q ∈ Ω) {u : ℝ → H} (hu0 : u a = 0)
    (hu : ∀ v ∈ Icc a b, HasDerivAt u
      (d.coefficientAlong g k (q, v) (u v) + d.forcingAlong g k (q, v)) v) :
    EqOn u (d.anchoredSolve g hab k q) (Icc a b) := by
  apply TangentODE.linear_solution_unique hab
    (fun v => d.coefficientAlong g k (q, v)) (fun v => d.forcingAlong g k (q, v))
    (hA.comp (continuous_const.prodMk continuous_id).continuousOn (fun v hv => ⟨hq, hv⟩)) hu
    (fun v hv => anchoredSolve_hasDerivAt_along d g hab k hA hf hq hv)
  rw [d.anchoredSolve_initial]
  exact hu0

end PathUniqueness

section Bridge

variable {P : Type} [NormedAddCommGroup P]
  (d : PrimaryODE.FrameData (P × ℝ)) (t : CommonCoverSolve.TangentData P Space)
  (j : ℤ) (g : CommonCoverSolve.Geometry) (k : Frequency) {a b : ℝ}

/-- All analytic assumptions are on actual input fields on the finite paths.
There is deliberately no ambient reference-energy or output-bound hypothesis. -/
structure Inputs (Ω : Set (P × Plane)) (a b : ℝ) : Prop where
  modal_coefficient : ContinuousOn ((copyFrame d g k).coefficient j) (Ω ×ˢ Icc a b)
  modal_forcing : ContinuousOn ((copyFrame d g k).forcing (copySource t.source g k)) (Ω ×ˢ Icc a b)
  ambient_coefficient : ContinuousOn (t.linearData.coefficientAlong g k) (Ω ×ˢ Icc a b)
  ambient_forcing : ContinuousOn (t.linearData.forcingAlong g k) (Ω ×ˢ Icc a b)
  kinematics : ∀ q ∈ Ω, d.Kinematics (copyParameter g k q) (Icc a b)
  compatibility : ∀ q ∈ Ω, FrameMatchesAt d t j (copyParameter g k q) (Icc a b)

noncomputable def reconstructedPath (hab : a ≤ b) (q : P × Plane) : ℝ → Space :=
  PrimaryODE.ambientSolution hab (copyFrame d g k) j (fun _ => 0) (copySource t.source g k) q

noncomputable def reconstructedCopy (hab : a ≤ b) (q : P × Plane) : Space :=
  reconstructedPath d t j g k hab q (g.coordinates k q.2).2

omit [NormedAddCommGroup P] in
theorem reconstructedPath_initial (hab : a ≤ b) (q : P × Plane) :
    reconstructedPath d t j g k hab q a = 0 := by
  unfold reconstructedPath PrimaryODE.ambientSolution
  rw [PrimaryODE.solution_initial]
  exact ambient_zero _ _

omit [NormedAddCommGroup P] in
theorem linear_rhs_eq_projected {q : P × Plane} {v : ℝ} {I : Set ℝ}
    (hm : FrameMatchesAt d t j (copyParameter g k q) I) (hv : v ∈ I) (x : Space) :
    t.linearData.coefficientAlong g k (q, v) x + t.linearData.forcingAlong g k (q, v) =
      TangentProjection.projectedRhs ((copyFrame d g k).normal (q, v))
        ((copyFrame d g k).normalMotion (q, v)) x
        (MovingFrameODE.baseAction ((copyFrame d g k).F (q, v))
          ((copyFrame d g k).shear (q, v)) x)
        (copySource t.source g k (q, v)) ((copyFrame d g k).damping j (q, v)) := by
  simp only [CommonCoverSolve.LinearData.coefficientAlong, CommonCoverSolve.LinearData.forcingAlong,
    CommonCoverSolve.TangentData.linearData, CommonCoverSolve.negativeTangentProjection_apply,
    ← sub_eq_add_neg, TangentODE.projectedOperator_apply]
  change TangentProjection.projectedRhs
    (t.normal ((copyParameter g k q).1, ((copyParameter g k q).2, v)))
    (t.normalDot ((copyParameter g k q).1, ((copyParameter g k q).2, v))) x
    (t.action ((copyParameter g k q).1, ((copyParameter g k q).2, v)) x)
    (copySource t.source g k (q, v))
    (t.damping ((copyParameter g k q).1, ((copyParameter g k q).2, v))) = _
  rw [hm.normal v hv, hm.normalMotion v hv, hm.action v hv x, hm.damping v hv]
  rfl

theorem reconstructedPath_hasDerivAt (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) {q : P × Plane} (hq : q ∈ Ω)
    {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (reconstructedPath d t j g k hab q)
      (t.linearData.coefficientAlong g k (q, v) (reconstructedPath d t j g k hab q v) +
        t.linearData.forcingAlong g k (q, v)) v := by
  rw [linear_rhs_eq_projected d t j g k (h.compatibility q hq) hv]
  exact PrimaryODE.ambientSolution_hasDerivAt hab (copyFrame d g k) j (fun _ => 0)
    (copySource t.source g k) h.modal_coefficient h.modal_forcing hq
    (reindex_kinematics d (copyParameter g k) (h.kinematics q hq)) hv

/-- Equality on the closed interval follows from the actual forced equation
and the common zero initial value, with no ambient energy estimate. -/
theorem reconstructedPath_eq_anchoredSolve (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) {q : P × Plane} (hq : q ∈ Ω) :
    EqOn (reconstructedPath d t j g k hab q) (t.linearData.anchoredSolve g hab k q) (Icc a b) :=
  anchoredSolve_unique_along t.linearData g hab k h.ambient_coefficient h.ambient_forcing hq
    (reconstructedPath_initial d t j g k hab q)
    (fun _ hv => reconstructedPath_hasDerivAt d t j g k hab h hq hv)

theorem reconstructedPath_tangent (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) {q : P × Plane} (hq : q ∈ Ω)
    {v : ℝ} (hv : v ∈ Icc a b) :
    ⟪t.normal (q.1, ((g.coordinates k q.2).1, v)), reconstructedPath d t j g k hab q v⟫_ℝ = 0 := by
  change ⟪t.normal ((copyParameter g k q).1, ((copyParameter g k q).2, v)), _⟫_ℝ = 0
  rw [(h.compatibility q hq).normal v hv]
  exact PrimaryODE.ambientSolution_tangent hab (copyFrame d g k) j (fun _ => 0)
    (copySource t.source g k) q v

theorem reconstructedCopy_eq_copySolve (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) {q : P × Plane} (hq : q ∈ Ω)
    (hv : (g.coordinates k q.2).2 ∈ Icc a b) :
    reconstructedCopy d t j g k hab q = t.linearData.copySolve g hab k q :=
  reconstructedPath_eq_anchoredSolve d t j g k hab h hq hv

/-! The smooth endpoint-rescaled modal representative used by the jet
estimates identifies with the very same copy solve. -/

noncomputable def reparamPath (a : ℝ) (z : (P × Plane) × ℝ) : Space :=
  (copyFrame d g k).ambient z
    (JointODE.reparamSolution a ((copyFrame d g k).coefficient j) (fun _ => 0)
      ((copyFrame d g k).forcing (copySource t.source g k)) z)

noncomputable def reparamCopy (a : ℝ) (q : P × Plane) : Space :=
  reparamPath d t j g k a (q, (g.coordinates k q.2).2)

theorem reparamPath_eq_reconstructedPath (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) {z : (P × Plane) × ℝ} (hz : z ∈ Ω ×ˢ Icc a b) :
    reparamPath d t j g k a z = reconstructedPath d t j g k hab z.1 z.2 := by
  unfold reparamPath
  rw [JointODE.reparamSolution_eq_actualSolution hab _ _ _ h.modal_coefficient h.modal_forcing hz]
  rfl

theorem reparamPath_eq_anchoredSolve (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) {z : (P × Plane) × ℝ} (hz : z ∈ Ω ×ˢ Icc a b) :
    reparamPath d t j g k a z = t.linearData.anchoredSolve g hab k z.1 z.2 := by
  rw [reparamPath_eq_reconstructedPath d t j g k hab h hz]
  exact reconstructedPath_eq_anchoredSolve d t j g k hab h hz.1 hz.2

theorem reparamCopy_eq_copySolve (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) {q : P × Plane} (hq : q ∈ Ω)
    (hv : (g.coordinates k q.2).2 ∈ Icc a b) :
    reparamCopy d t j g k a q = t.linearData.copySolve g hab k q :=
  reparamPath_eq_anchoredSolve d t j g k hab h ⟨hq, hv⟩

/-! ## Local identity of all actual joint derivatives -/

variable [NormedSpace ℝ P]

noncomputable def currentTime (q : P × Plane) : ℝ := (g.coordinates k q.2).2

theorem currentTime_contDiff : ContDiff ℝ ∞ (currentTime (P := P) g k) :=
  ((g.coordinates_contDiff k).comp contDiff_snd).snd

noncomputable def copyInterior (Ω : Set (P × Plane)) (a b : ℝ) : Set (P × Plane) :=
  Ω ∩ (currentTime (P := P) g k) ⁻¹' Ioo a b

theorem copyInterior_isOpen {Ω : Set (P × Plane)} (hΩ : IsOpen Ω) (a b : ℝ) :
    IsOpen (copyInterior g k Ω a b) :=
  hΩ.inter (isOpen_Ioo.preimage (currentTime_contDiff g k).continuous)

omit [NormedSpace ℝ P] in
theorem reparamCopy_eqOn (hab : a ≤ b) {Ω : Set (P × Plane)}
    (h : Inputs d t j g k Ω a b) :
    EqOn (reparamCopy d t j g k a) (t.linearData.copySolve g hab k)
      (copyInterior g k Ω a b) := by
  intro q hq
  exact reparamCopy_eq_copySolve d t j g k hab h hq.1 ⟨hq.2.1.le, hq.2.2.le⟩

/-- This equality transfers bounds for modal reconstruction to actual full
jets of the common-cover output; it introduces no energy estimate. -/
theorem reparamCopy_iteratedFDeriv_eq (hab : a ≤ b) {Ω : Set (P × Plane)}
    (hΩ : IsOpen Ω) (h : Inputs d t j g k Ω a b) {q : P × Plane}
    (hq : q ∈ copyInterior g k Ω a b) (n : ℕ) :
    iteratedFDeriv ℝ n (reparamCopy d t j g k a) q =
      iteratedFDeriv ℝ n (t.linearData.copySolve g hab k) q := by
  have he := (reparamCopy_eqOn d t j g k hab h).iteratedFDerivWithin (𝕜 := ℝ) n hq
  simpa only [iteratedFDerivWithin_of_isOpen _ (copyInterior_isOpen g k hΩ a b) hq] using he

theorem reparamPath_iteratedFDeriv_eq (hab : a ≤ b) {Ω : Set (P × Plane)}
    (hΩ : IsOpen Ω) (h : Inputs d t j g k Ω a b) {z : (P × Plane) × ℝ}
    (hz : z ∈ Ω ×ˢ Ioo a b) (n : ℕ) :
    iteratedFDeriv ℝ n (reparamPath d t j g k a) z =
      iteratedFDeriv ℝ n (fun w : (P × Plane) × ℝ => t.linearData.anchoredSolve g hab k w.1 w.2) z
        := by
  have he : EqOn (reparamPath d t j g k a)
      (fun w : (P × Plane) × ℝ => t.linearData.anchoredSolve g hab k w.1 w.2) (Ω ×ˢ Ioo a b) := by
    intro w hw
    exact reparamPath_eq_anchoredSolve d t j g k hab h ⟨hw.1, hw.2.1.le, hw.2.2.le⟩
  have hj := he.iteratedFDerivWithin (𝕜 := ℝ) n hz
  simpa only [iteratedFDerivWithin_of_isOpen _ (hΩ.prod isOpen_Ioo) hz] using hj

end Bridge

/-! ## Smooth primitive data discharge the continuity requirements -/

noncomputable def baseOperatorFamily : (ℝ × State) →L[ℝ] (Space →L[ℝ] Space) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => baseOperator z.1 z.2
    map_add' := by
      intro z w
      ext x i
      fin_cases i <;>
        simp [baseOperator_apply, MovingFrameODE.baseAction, MovingFrameODE.pack,
          MovingFrameODE.tail] <;>
        ring
    map_smul' := by
      intro c z
      ext x i
      fin_cases i <;>
        simp [baseOperator_apply, MovingFrameODE.baseAction, MovingFrameODE.pack,
          MovingFrameODE.tail] <;>
        ring }

@[simp] theorem baseOperatorFamily_apply (z : ℝ × State) :
    baseOperatorFamily z = baseOperator z.1 z.2 := rfl

theorem projectedOperator_continuousOn {X H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Set X} {n nd : X → H} {A : X → H →L[ℝ] H} {δ : X → ℝ}
    (hn : ContinuousOn n S) (hnd : ContinuousOn nd S) (hA : ContinuousOn A S)
    (hδ : ContinuousOn δ S) (hne : ∀ z ∈ S, n z ≠ 0) :
    ContinuousOn (fun z => TangentODE.projectedOperator (n z) (nd z) (A z) (δ z)) S := by
  have hlin : ContinuousOn (fun z => (innerSL ℝ (n z)).comp (A z) - innerSL ℝ (nd z)) S :=
    (((innerSL ℝ).continuous.comp_continuousOn hn).clm_comp hA).sub
      ((innerSL ℝ).continuous.comp_continuousOn hnd)
  have hv : ContinuousOn (fun z => (⟪n z, n z⟫_ℝ)⁻¹ • n z) S :=
    ((hn.inner hn).inv₀ (fun z hz => inner_self_ne_zero.mpr (hne z hz))).smul hn
  have ho : ContinuousOn (fun z =>
      ((innerSL ℝ (n z)).comp (A z) - innerSL ℝ (nd z)).smulRight
        ((⟪n z, n z⟫_ℝ)⁻¹ • n z)) S :=
    isBoundedBilinearMap_smulRight.continuous.comp_continuousOn (hlin.prodMk hv)
  exact (hA.neg.add ho).sub (hδ.smul continuousOn_const)

theorem projectedForcing_continuousOn {X : Type*} [TopologicalSpace X]
    {S : Set X} {n f : X → Space} (hn : ContinuousOn n S) (hf : ContinuousOn f S)
    (hne : ∀ z ∈ S, n z ≠ 0) :
    ContinuousOn (fun z => -TangentProjection.tangentProj (n z) (f z)) S := by
  unfold TangentProjection.tangentProj
  exact (hf.fun_sub (((hn.inner hf).div (hn.inner hn)
    (fun z hz => inner_self_ne_zero.mpr (hne z hz))).fun_smul hn)).fun_neg

section SmoothFrame

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {d : PrimaryODE.FrameData Q} {S : Set (Q × ℝ)}

theorem frame_normal_continuousOn (h : d.SmoothOn S) : ContinuousOn d.normal S :=
  MovingFrameODE.packCLM.continuous.comp_continuousOn
    ((h.beta.continuousOn.mul h.rho.continuousOn).prodMk
      (h.beta.continuousOn.smul (h.frame 0).continuousOn))

theorem frame_normalMotion_continuousOn (h : d.SmoothOn S) : ContinuousOn d.normalMotion S :=
  MovingFrameODE.packCLM.continuous.comp_continuousOn
    (((h.betaDot.continuousOn.mul h.rho.continuousOn).add
      (h.beta.continuousOn.mul h.rhoDot.continuousOn)).prodMk
      ((h.betaDot.continuousOn.smul (h.frame 0).continuousOn).add
        ((h.beta.continuousOn.mul h.rotation.continuousOn).smul (h.frame 1).continuousOn)))

theorem frame_baseOperator_continuousOn (h : d.SmoothOn S) :
    ContinuousOn (fun z => baseOperator (d.F z) (d.shear z)) S := by
  have hc : ContinuousOn (fun z => baseOperatorFamily (d.F z, d.shear z)) S :=
    baseOperatorFamily.continuous.comp_continuousOn (h.F.continuousOn.prodMk h.shear.continuousOn)
  simpa only [baseOperatorFamily_apply] using hc

end SmoothFrame

theorem reindex_smoothOn {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (d : PrimaryODE.FrameData P) (φ : Q → P)
    {S : Set (P × ℝ)} {Ω : Set (Q × ℝ)} (hd : d.SmoothOn S)
    (hφ : ContDiffOn ℝ ∞ (fun z : Q × ℝ => (φ z.1, z.2)) Ω)
    (hmap : MapsTo (fun z : Q × ℝ => (φ z.1, z.2)) Ω S) :
    (reindex d φ).SmoothOn Ω := by
  exact ⟨hd.beta.comp hφ hmap, hd.betaDot.comp hφ hmap, hd.rho.comp hφ hmap,
    hd.rhoDot.comp hφ hmap, hd.rotation.comp hφ hmap, hd.F.comp hφ hmap,
    hd.shear.comp hφ hmap, fun i => (hd.frame i).comp hφ hmap,
    hd.eigenvalue.comp hφ hmap, hd.eigenvector.comp hφ hmap,
    hd.eigenRate.comp hφ hmap, hd.viscosity.comp hφ hmap,
    fun z hz => hd.eigenvector_ne_zero _ (hmap hz)⟩

section CanonicalInputs

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (d : PrimaryODE.FrameData (P × ℝ)) (g : CommonCoverSolve.Geometry) (k : Frequency)

theorem copyParameter_contDiff : ContDiff ℝ ∞ (copyParameter (P := P) g k) :=
  contDiff_fst.prodMk (((g.coordinates_contDiff k).comp contDiff_snd).fst)

theorem copyArgument_contDiff :
    ContDiff ℝ ∞ (fun z : (P × Plane) × ℝ => (copyParameter g k z.1, z.2)) :=
  ((copyParameter_contDiff g k).comp contDiff_fst).prodMk contDiff_snd

theorem copyFrame_smoothOn {S : Set ((P × ℝ) × ℝ)} {Ω : Set ((P × Plane) × ℝ)}
    (hd : d.SmoothOn S)
    (hmap : MapsTo (fun z : (P × Plane) × ℝ => (copyParameter g k z.1, z.2)) Ω S) :
    (copyFrame d g k).SmoothOn Ω :=
  reindex_smoothOn d _ hd (copyArgument_contDiff g k).contDiffOn hmap

theorem copySource_contDiffOn {f : P × Plane → Space} {S : Set (P × Plane)}
    {Ω : Set ((P × Plane) × ℝ)} (hf : ContDiffOn ℝ ∞ f S)
    (hmap : MapsTo (fun z : (P × Plane) × ℝ => (z.1.1, g.path k z.1.2 z.2)) Ω S) :
    ContDiffOn ℝ ∞ (copySource f g k) Ω :=
  hf.comp (g.pathArgument_contDiff k).contDiffOn hmap

/-- For the concrete tangent datum built from the moving frame, no matching
or ambient continuity obligation is left over: smooth inputs and the actual
frame kinematics imply every bridge hypothesis. -/
theorem inputs_of_smooth_frame (j : ℤ) (f : P × Plane → Space)
    {Ω : Set (P × Plane)} {a b : ℝ}
    (hd : (copyFrame d g k).SmoothOn (Ω ×ˢ Icc a b))
    (hf : ContDiffOn ℝ ∞ (copySource f g k) (Ω ×ˢ Icc a b))
    (hk : ∀ q ∈ Ω, d.Kinematics (copyParameter g k q) (Icc a b)) :
    Inputs d (frameTangentData d j f) j g k Ω a b := by
  have hn : ContinuousOn (copyFrame d g k).normal (Ω ×ˢ Icc a b) := frame_normal_continuousOn hd
  have hnd : ContinuousOn (copyFrame d g k).normalMotion (Ω ×ˢ Icc a b) :=
    frame_normalMotion_continuousOn hd
  have hn0 : ∀ z ∈ Ω ×ˢ Icc a b, (copyFrame d g k).normal z ≠ 0 := by
    intro z hz
    exact MovingFrameODE.normal_ne_zero _ ((hk z.1 hz.1).beta_ne_zero z.2 hz.2)
  refine ⟨(hd.coefficient j).continuousOn, (hd.forcing hf).continuousOn, ?_, ?_, hk,
    fun q _ => frameTangentData_matches d j f (copyParameter g k q) _⟩
  · change ContinuousOn (fun z => TangentODE.projectedOperator ((copyFrame d g k).normal z)
      ((copyFrame d g k).normalMotion z)
      (baseOperator ((copyFrame d g k).F z) ((copyFrame d g k).shear z))
      ((copyFrame d g k).damping j z)) (Ω ×ˢ Icc a b)
    exact projectedOperator_continuousOn hn hnd (frame_baseOperator_continuousOn hd)
      (continuousOn_const.mul hd.viscosity.continuousOn) hn0
  · change ContinuousOn (fun z => CommonCoverSolve.negativeTangentProjection
      ((copyFrame d g k).normal z) (copySource f g k z)) (Ω ×ˢ Icc a b)
    simpa only [CommonCoverSolve.negativeTangentProjection_apply] using
      projectedForcing_continuousOn hn hf.continuousOn hn0

/-- Direct canonical bridge, with assumptions only on smooth primitive frame
and source data and their actual slot derivatives. -/
theorem frame_reconstructedCopy_eq_copySolve (j : ℤ) (f : P × Plane → Space)
    {Ω : Set (P × Plane)} {a b : ℝ} (hab : a ≤ b)
    (hd : (copyFrame d g k).SmoothOn (Ω ×ˢ Icc a b))
    (hf : ContDiffOn ℝ ∞ (copySource f g k) (Ω ×ˢ Icc a b))
    (hk : ∀ q ∈ Ω, d.Kinematics (copyParameter g k q) (Icc a b))
    {q : P × Plane} (hq : q ∈ Ω) (hv : (g.coordinates k q.2).2 ∈ Icc a b) :
    reconstructedCopy d (frameTangentData d j f) j g k hab q =
      (frameTangentData d j f).linearData.copySolve g hab k q :=
  reconstructedCopy_eq_copySolve d _ j g k hab
    (inputs_of_smooth_frame d g k j f hd hf hk) hq hv

/-- Exact transfer of all ordinary full tensors to the canonical copy solve.
The interval endpoints retain the pointwise equality proved above. -/
theorem frame_reparamCopy_iteratedFDeriv_eq (j : ℤ) (f : P × Plane → Space)
    {Ω : Set (P × Plane)} {a b : ℝ} (hab : a ≤ b) (hΩ : IsOpen Ω)
    (hd : (copyFrame d g k).SmoothOn (Ω ×ˢ Icc a b))
    (hf : ContDiffOn ℝ ∞ (copySource f g k) (Ω ×ˢ Icc a b))
    (hk : ∀ q ∈ Ω, d.Kinematics (copyParameter g k q) (Icc a b))
    {q : P × Plane} (hq : q ∈ copyInterior g k Ω a b) (n : ℕ) :
    iteratedFDeriv ℝ n (reparamCopy d (frameTangentData d j f) j g k a) q =
      iteratedFDeriv ℝ n ((frameTangentData d j f).linearData.copySolve g hab k) q :=
  reparamCopy_iteratedFDeriv_eq d _ j g k hab hΩ
    (inputs_of_smooth_frame d g k j f hd hf hk) hq n

end CanonicalInputs

/-! ## Seeded primary paths: the same equation, with their own initial data -/

section Seeded

variable {P : Type} [NormedAddCommGroup P]
  (d : PrimaryODE.FrameData (P × ℝ)) (t : CommonCoverSolve.TangentData P Space)
  (j : ℤ) (g : CommonCoverSolve.Geometry) (k : Frequency) {a b : ℝ}

noncomputable def seededReconstructedPath (hab : a ≤ b) (x₀ : P × Plane → State)
    (q : P × Plane) : ℝ → Space :=
  PrimaryODE.ambientSolution hab (copyFrame d g k) j x₀ (copySource t.source g k) q

omit [NormedAddCommGroup P] in
theorem seededReconstructedPath_initial (hab : a ≤ b) (x₀ : P × Plane → State) (q : P × Plane) :
    seededReconstructedPath d t j g k hab x₀ q a =
      d.ambient (copyParameter g k q, a) (x₀ q) := by
  unfold seededReconstructedPath PrimaryODE.ambientSolution
  rw [PrimaryODE.solution_initial]
  rfl

/-- The reconstructed seeded path satisfies the actual tangent equation.
This is not an identification with the zero-entry copy solve. -/
theorem seededReconstructedPath_hasDerivAt (hab : a ≤ b) (x₀ : P × Plane → State)
    {Ω : Set (P × Plane)} (h : Inputs d t j g k Ω a b)
    {q : P × Plane} (hq : q ∈ Ω) {v : ℝ} (hv : v ∈ Icc a b) :
    let z := (q.1, ((g.coordinates k q.2).1, v))
    HasDerivAt (seededReconstructedPath d t j g k hab x₀ q)
      (TangentProjection.projectedRhs (t.normal z) (t.normalDot z)
        (seededReconstructedPath d t j g k hab x₀ q v)
        (t.action z (seededReconstructedPath d t j g k hab x₀ q v))
        (t.source (q.1, g.path k q.2 v)) (t.damping z)) v := by
  have hd : HasDerivAt (seededReconstructedPath d t j g k hab x₀ q)
      (t.linearData.coefficientAlong g k (q, v) (seededReconstructedPath d t j g k hab x₀ q v) +
        t.linearData.forcingAlong g k (q, v)) v := by
    rw [linear_rhs_eq_projected d t j g k (h.compatibility q hq) hv]
    exact PrimaryODE.ambientSolution_hasDerivAt hab (copyFrame d g k) j x₀
      (copySource t.source g k) h.modal_coefficient h.modal_forcing hq
      (reindex_kinematics d (copyParameter g k) (h.kinematics q hq)) hv
  simpa only [CommonCoverSolve.LinearData.coefficientAlong,
    CommonCoverSolve.LinearData.forcingAlong,
    CommonCoverSolve.TangentData.linearData, CommonCoverSolve.negativeTangentProjection_apply,
    ← sub_eq_add_neg, TangentODE.projectedOperator_apply] using hd

theorem seededReconstructedPath_tangent (hab : a ≤ b) (x₀ : P × Plane → State)
    {Ω : Set (P × Plane)} (h : Inputs d t j g k Ω a b)
    {q : P × Plane} (hq : q ∈ Ω) {v : ℝ} (hv : v ∈ Icc a b) :
    ⟪t.normal (q.1, ((g.coordinates k q.2).1, v)),
      seededReconstructedPath d t j g k hab x₀ q v⟫_ℝ = 0 := by
  change ⟪t.normal ((copyParameter g k q).1, ((copyParameter g k q).2, v)), _⟫_ℝ = 0
  rw [(h.compatibility q hq).normal v hv]
  exact PrimaryODE.ambientSolution_tangent hab (copyFrame d g k) j x₀
    (copySource t.source g k) q v

end Seeded

end NavierStokes.PrimaryCopyBridge
