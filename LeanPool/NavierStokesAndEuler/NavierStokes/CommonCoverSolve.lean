/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TorusAverages
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlotGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothPathFamily
public import LeanPool.NavierStokesAndEuler.NavierStokes.JointODE
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedODEJets

@[expose] public section

/-!
# Actual slot solves on a common torus

The source is evaluated on the lifted copy path. Only periodicity on the
coarsest torus is used; finer native periodicity is not an input.
-/

noncomputable section

namespace NavierStokes.CommonCoverSolve

open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace
open TorusInverse

noncomputable def coverEquiv : Plane ≃L[ℝ] Plane :=
  TorusAverages.slotChart (3, 1) (1, 5) (by norm_num)

theorem coverEquiv_apply (Y : Plane) : coverEquiv Y = SlotGeometry.cover Y := by
  rw [coverEquiv, TorusAverages.slotChart_apply, SlotGeometry.cover_apply]
  ext <;> simp [mul_comm]

noncomputable def coverPower : ℕ → Plane ≃L[ℝ] Plane
  | 0 => ContinuousLinearEquiv.refl ℝ Plane
  | d + 1 => (coverPower d).trans coverEquiv

theorem coverPower_apply (d : ℕ) (Y : Plane) :
    coverPower d Y = (SlotGeometry.cover ^ d) Y := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change coverEquiv (coverPower d Y) = _
      rw [coverEquiv_apply, ih, pow_succ', _root_.mul_apply_eq_comp]

noncomputable def indexMap (k : Frequency) : Frequency :=
  (3 * k.1 + k.2, k.1 + 5 * k.2)

noncomputable def coverIndex (d : ℕ) (k : Frequency) : Frequency := indexMap^[d] k

theorem coverEquiv_lattice (k : Frequency) :
    coverEquiv (TorusAverages.latticePoint k) = TorusAverages.latticePoint (indexMap k) := by
  rw [coverEquiv_apply, SlotGeometry.cover_apply]
  ext <;> simp [TorusAverages.latticePoint, indexMap]

theorem coverPower_lattice (d : ℕ) (k : Frequency) :
    coverPower d (TorusAverages.latticePoint k) =
      TorusAverages.latticePoint (coverIndex d k) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change coverEquiv (coverPower d (TorusAverages.latticePoint k)) = _
      rw [ih, coverEquiv_lattice]
      simp only [coverIndex, Function.iterate_succ_apply']

theorem norm_coverPower_le (d : ℕ) (Y : Plane) :
    ‖coverPower d Y‖ ≤ (6 : ℝ) ^ d * ‖Y‖ := by
  rw [coverPower_apply]
  exact SlotGeometry.norm_cover_pow_le d Y

theorem norm_coverPower_le_of_gap_le {d D : ℕ} (hd : d ≤ D) (Y : Plane) :
    ‖coverPower d Y‖ ≤ (6 : ℝ) ^ D * ‖Y‖ :=
  (norm_coverPower_le d Y).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hd) (norm_nonneg _))

/-- Fixed geometry for a level whose gap above the common coarsest level is
`gap`. The columns of `basis` are the native radial and transverse vectors. -/
structure Geometry where
  gap : ℕ
  basis : Plane ≃L[ℝ] Plane
  center : Plane

namespace Geometry

variable (g : Geometry)

noncomputable def coordinates (k : Frequency) (Y : Plane) : Plane :=
  g.basis.symm (coverPower g.gap Y - g.center - TorusAverages.latticePoint k)

noncomputable def point (k : Frequency) (z : Plane) : Plane :=
  (coverPower g.gap).symm (g.center + TorusAverages.latticePoint k + g.basis z)

theorem coordinates_point (k : Frequency) (z : Plane) :
    g.coordinates k (g.point k z) = z := by
  unfold coordinates point
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have h : g.center + TorusAverages.latticePoint k + g.basis z - g.center -
      TorusAverages.latticePoint k = g.basis z := by abel
  rw [h, ContinuousLinearEquiv.symm_apply_apply]

theorem point_coordinates (k : Frequency) (Y : Plane) :
    g.point k (g.coordinates k Y) = Y := by
  unfold point coordinates
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have h : g.center + TorusAverages.latticePoint k +
      (coverPower g.gap Y - g.center - TorusAverages.latticePoint k) = coverPower g.gap Y := by abel
  rw [h, ContinuousLinearEquiv.symm_apply_apply]

theorem point_add (k : Frequency) (z h : Plane) :
    g.point k (z + h) = g.point k z + (coverPower g.gap).symm (g.basis h) := by
  simp only [point, map_add, add_assoc]

noncomputable def path (k : Frequency) (Y : Plane) (eta : ℝ) : Plane :=
  g.point k ((g.coordinates k Y).1, eta)

theorem coordinates_path (k : Frequency) (Y : Plane) (eta : ℝ) :
    g.coordinates k (g.path k Y eta) = ((g.coordinates k Y).1, eta) :=
  g.coordinates_point k _

theorem path_current (k : Frequency) (Y : Plane) :
    g.path k Y (g.coordinates k Y).2 = Y := by
  exact g.point_coordinates k Y

theorem path_path (k : Frequency) (Y : Plane) (eta eta' : ℝ) :
    g.path k (g.path k Y eta) eta' = g.path k Y eta' := by
  unfold path
  rw [g.coordinates_point]

/-- The manuscript's copy-path formula, in the common coarsest coordinates.
The final native basis vector is `v_t`. -/
theorem path_eq_shift (k : Frequency) (Y : Plane) (eta : ℝ) :
    g.path k Y eta = Y + (coverPower g.gap).symm
      ((eta - (g.coordinates k Y).2) • g.basis (0, 1)) := by
  let z := g.coordinates k Y
  have hz : (z.1, eta) = z + (eta - z.2) • (0, 1) := by
    ext <;> simp [z]
  change g.point k (z.1, eta) = _
  rw [hz, g.point_add, map_smul]
  rw [g.point_coordinates]

theorem point_deck (k n : Frequency) (z : Plane) :
    g.point (k + coverIndex g.gap n) z = g.point k z + TorusAverages.latticePoint n := by
  have h : g.center + TorusAverages.latticePoint (k + coverIndex g.gap n) + g.basis z =
      (g.center + TorusAverages.latticePoint k + g.basis z) +
        coverPower g.gap (TorusAverages.latticePoint n) := by
    rw [TorusAverages.latticePoint_add, coverPower_lattice]
    abel
  unfold point
  rw [h, map_add, ContinuousLinearEquiv.symm_apply_apply]

theorem coordinates_deck (k n : Frequency) (Y : Plane) :
    g.coordinates (k + coverIndex g.gap n) (Y + TorusAverages.latticePoint n) =
      g.coordinates k Y := by
  have h : g.point (k + coverIndex g.gap n) (g.coordinates k Y) =
      Y + TorusAverages.latticePoint n := by
    rw [g.point_deck, g.point_coordinates]
  rw [← h, g.coordinates_point]

theorem path_deck (k n : Frequency) (Y : Plane) (eta : ℝ) :
    g.path (k + coverIndex g.gap n) (Y + TorusAverages.latticePoint n) eta =
      g.path k Y eta + TorusAverages.latticePoint n := by
  unfold path
  rw [g.coordinates_deck, g.point_deck]

theorem coordinates_contDiff (k : Frequency) : ContDiff ℝ ∞ (g.coordinates k) :=
  g.basis.symm.contDiff.comp
    (((coverPower g.gap).contDiff.sub contDiff_const).sub contDiff_const)

theorem point_contDiff (k : Frequency) : ContDiff ℝ ∞ (g.point k) :=
  (coverPower g.gap).symm.contDiff.comp (contDiff_const.add g.basis.contDiff)

theorem path_contDiff (k : Frequency) :
    ContDiff ℝ ∞ (fun z : Plane × ℝ => g.path k z.1 z.2) :=
  (g.point_contDiff k).comp
    (((g.coordinates_contDiff k).comp contDiff_fst).fst.prodMk contDiff_snd)

end Geometry

/-! ## Actual forced linear equations on the copy paths -/

/-- Native coefficients and a native linear conversion of an ambient source.
The source itself is a function on the common coarsest coordinates. This
allows the tangent-frame projection to depend on the native slot. -/
structure LinearData (P V E : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  coefficient : P × Plane → E →L[ℝ] E
  forcingMap : P × Plane → V →L[ℝ] E
  source : P × Plane → V

def PeriodicAt {P V : Type} (f : P × Plane → V) (p : P) : Prop :=
  ∀ Y : Plane, ∀ n : Frequency,
    f (p, Y + TorusAverages.latticePoint n) = f (p, Y)

section Paths

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace LinearData

variable (d : LinearData P V E) (g : Geometry)

noncomputable def coefficientAlong (k : Frequency) (w : (P × Plane) × ℝ) : E →L[ℝ] E :=
  d.coefficient (w.1.1, ((g.coordinates k w.1.2).1, w.2))

noncomputable def forcingAlong (k : Frequency) (w : (P × Plane) × ℝ) : E :=
  d.forcingMap (w.1.1, ((g.coordinates k w.1.2).1, w.2))
    (d.source (w.1.1, g.path k w.1.2 w.2))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem coefficientAlong_deck (k n : Frequency) (p : P) (Y : Plane) (s : ℝ) :
    d.coefficientAlong g (k + coverIndex g.gap n) ((p, Y + TorusAverages.latticePoint n), s) =
      d.coefficientAlong g k ((p, Y), s) := by
  simp only [coefficientAlong, g.coordinates_deck]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem forcingAlong_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p)
    (Y : Plane) (s : ℝ) :
    d.forcingAlong g (k + coverIndex g.gap n) ((p, Y + TorusAverages.latticePoint n), s) =
      d.forcingAlong g k ((p, Y), s) := by
  simp only [forcingAlong, g.coordinates_deck, g.path_deck]
  rw [hp (g.path k Y s) n]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem coefficientAlong_reanchor (k : Frequency) (p : P) (Y : Plane) (eta s : ℝ) :
    d.coefficientAlong g k ((p, g.path k Y eta), s) =
      d.coefficientAlong g k ((p, Y), s) := by
  simp only [coefficientAlong, g.coordinates_path]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem forcingAlong_reanchor (k : Frequency) (p : P) (Y : Plane) (eta s : ℝ) :
    d.forcingAlong g k ((p, g.path k Y eta), s) = d.forcingAlong g k ((p, Y), s) := by
  simp only [forcingAlong, g.coordinates_path, g.path_path]

end LinearData

theorem pathFamily_congr_slice {Q W : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {a b : ℝ}
    (F G : Q × ℝ → W) (p q : Q)
    (h : ∀ t : Icc a b, F (p, t) = G (q, t)) :
    SmoothPathFamily.pathFamily (a := a) (b := b) F p =
      SmoothPathFamily.pathFamily G q := by
  have heq : (fun t : Icc a b => F (p, t)) = (fun t : Icc a b => G (q, t)) := funext h
  by_cases hF : Continuous (fun t : Icc a b => F (p, t))
  · have hG : Continuous (fun t : Icc a b => G (q, t)) := heq ▸ hF
    ext t
    rw [SmoothPathFamily.pathFamily_apply F p hF, SmoothPathFamily.pathFamily_apply G q hG]
    exact h t
  · have hG : ¬ Continuous (fun t : Icc a b => G (q, t)) := by
      intro hG
      exact hF (heq.symm ▸ hG)
    simp only [SmoothPathFamily.pathFamily, dite_eq_right hF, dite_eq_right hG]

namespace LinearData

variable [CompleteSpace E] {a b : ℝ}
variable (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)

noncomputable def coefficientPath (k : Frequency) (p : P × Plane) :
    ParametricODE.Coefficient a b E := SmoothPathFamily.pathFamily (d.coefficientAlong g k) p

noncomputable def forcingPath (k : Frequency) (p : P × Plane) :
    ParametricODE.Curve a b E := SmoothPathFamily.pathFamily (d.forcingAlong g k) p

/-- The genuine Volterra solution, with zero entry data, evaluated along the
copy path anchored at the current common coordinate. -/
noncomputable def anchoredSolve (k : Frequency) (p : P × Plane) (s : ℝ) : E :=
  ParametricODE.solutionExtension hab (d.coefficientPath g k p) 0 (d.forcingPath g k p) s

/-- Value of the constructed solution at the current native slot coordinate. -/
noncomputable def copySolve (k : Frequency) (p : P × Plane) : E :=
  d.anchoredSolve g hab k p (g.coordinates k p.2).2

omit [CompleteSpace E] in
theorem coefficientPath_deck (k n : Frequency) (p : P) (Y : Plane) :
    d.coefficientPath (a := a) (b := b) g (k + coverIndex g.gap n)
        (p, Y + TorusAverages.latticePoint n) = d.coefficientPath g k (p, Y) := by
  apply pathFamily_congr_slice
  intro s
  exact d.coefficientAlong_deck g k n p Y s

omit [CompleteSpace E] in
theorem forcingPath_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p) (Y : Plane) :
    d.forcingPath (a := a) (b := b) g (k + coverIndex g.gap n)
        (p, Y + TorusAverages.latticePoint n) = d.forcingPath g k (p, Y) := by
  apply pathFamily_congr_slice
  intro s
  exact d.forcingAlong_deck g k n p hp Y s

theorem anchoredSolve_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p)
    (Y : Plane) (s : ℝ) :
    d.anchoredSolve g hab (k + coverIndex g.gap n) (p, Y + TorusAverages.latticePoint n) s =
      d.anchoredSolve g hab k (p, Y) s := by
  unfold anchoredSolve
  rw [d.coefficientPath_deck, d.forcingPath_deck g k n p hp]

theorem copySolve_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p) (Y : Plane) :
    d.copySolve g hab (k + coverIndex g.gap n) (p, Y + TorusAverages.latticePoint n) =
      d.copySolve g hab k (p, Y) := by
  unfold copySolve
  rw [g.coordinates_deck, d.anchoredSolve_deck g hab k n p hp]

theorem anchoredSolve_reanchor (k : Frequency) (p : P) (Y : Plane) (eta s : ℝ) :
    d.anchoredSolve g hab k (p, g.path k Y eta) s = d.anchoredSolve g hab k (p, Y) s := by
  have hA : d.coefficientPath (a := a) (b := b) g k (p, g.path k Y eta) =
      d.coefficientPath g k (p, Y) :=
    pathFamily_congr_slice _ _ _ _ (fun t => d.coefficientAlong_reanchor g k p Y eta t)
  have hf : d.forcingPath (a := a) (b := b) g k (p, g.path k Y eta) =
      d.forcingPath g k (p, Y) :=
    pathFamily_congr_slice _ _ _ _ (fun t => d.forcingAlong_reanchor g k p Y eta t)
  unfold anchoredSolve
  rw [hA, hf]

theorem copySolve_path (k : Frequency) (p : P) (Y : Plane) (s : ℝ) :
    d.copySolve g hab k (p, g.path k Y s) = d.anchoredSolve g hab k (p, Y) s := by
  unfold copySolve
  rw [g.coordinates_path, d.anchoredSolve_reanchor g hab]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem anchoredSolve_initial (k : Frequency) (p : P × Plane) :
    d.anchoredSolve g hab k p a = 0 := by
  simp [anchoredSolve, ParametricODE.solutionExtension]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copySolve_at_entry (k : Frequency) (p : P) (xi : ℝ) :
    d.copySolve g hab k (p, g.point k (xi, a)) = 0 := by
  unfold copySolve
  rw [g.coordinates_point]
  exact d.anchoredSolve_initial g hab k _

end LinearData

theorem solutionExtension_zero {a b : ℝ} (hab : a ≤ b)
    (A : ParametricODE.Coefficient a b E) [CompleteSpace E] (s : ℝ) :
    ParametricODE.solutionExtension hab A 0 0 s = 0 := by
  have hsol : ParametricODE.solution hab A 0 0 = 0 := by
    simp [ParametricODE.solution, ParametricODE.source]
  have happ : ParametricODE.applyCoefficient A 0 = 0 := by
    ext t
    simp [ParametricODE.applyCoefficient]
  simp [ParametricODE.solutionExtension, hsol, happ, ParametricODE.extend]

namespace LinearData

variable [CompleteSpace E] {a b : ℝ}
variable (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)

omit [CompleteSpace E] in
theorem forcingPath_zero_of_source_zero (k : Frequency) (p : P) (Y : Plane)
    (hf : ∀ s ∈ Icc a b, d.source (p, g.path k Y s) = 0) :
    d.forcingPath (a := a) (b := b) g k (p, Y) = 0 := by
  have h : d.forcingPath (a := a) (b := b) g k (p, Y) =
      SmoothPathFamily.pathFamily (a := a) (b := b) (fun _ : (P × Plane) × ℝ => (0 : E))
        (p, Y) := by
    apply pathFamily_congr_slice
    intro s
    simp only [forcingAlong, hf s s.2, map_zero]
  rw [h]
  ext t
  rw [SmoothPathFamily.pathFamily_apply _ _ continuous_const]
  rfl

/-- Vanishing along the entire source path forces the constructed zero-entry
solution to vanish. No vanishing assumption on the output is used. -/
theorem anchoredSolve_zero_of_source_zero (k : Frequency) (p : P) (Y : Plane)
    (hf : ∀ s ∈ Icc a b, d.source (p, g.path k Y s) = 0) (eta : ℝ) :
    d.anchoredSolve g hab k (p, Y) eta = 0 := by
  unfold anchoredSolve
  rw [d.forcingPath_zero_of_source_zero g k p Y hf]
  exact solutionExtension_zero hab _ eta

theorem copySolve_zero_of_source_zero (k : Frequency) (p : P) (Y : Plane)
    (hf : ∀ s ∈ Icc a b, d.source (p, g.path k Y s) = 0) :
    d.copySolve g hab k (p, Y) = 0 := d.anchoredSolve_zero_of_source_zero g hab k p Y hf _

theorem copySolve_preserves_slow_support {U : Set P}
    (hf : ∀ p ∉ U, ∀ Y, d.source (p, Y) = 0) (k : Frequency) {p : P} (hp : p ∉ U)
    (Y : Plane) : d.copySolve g hab k (p, Y) = 0 :=
  d.copySolve_zero_of_source_zero g hab k p Y (fun _ _ => hf p hp _)

theorem copySolve_preserves_transverse_support (k : Frequency) {S : Set ℝ} (p : P)
    (hf : ∀ xi ∉ S, ∀ eta ∈ Icc a b, d.source (p, g.point k (xi, eta)) = 0)
    (Y : Plane) (hY : (g.coordinates k Y).1 ∉ S) : d.copySolve g hab k (p, Y) = 0 :=
  d.copySolve_zero_of_source_zero g hab k p Y (fun s hs => hf _ hY s hs)

end LinearData

namespace Geometry

theorem nativeArgument_contDiff (g : Geometry) (k : Frequency) :
    ContDiff ℝ ∞ (fun w : (P × Plane) × ℝ =>
      (w.1.1, ((g.coordinates k w.1.2).1, w.2))) :=
  contDiff_fst.fst.prodMk
    (((g.coordinates_contDiff k).comp contDiff_fst.snd).fst.prodMk contDiff_snd)

theorem pathArgument_contDiff (g : Geometry) (k : Frequency) :
    ContDiff ℝ ∞ (fun w : (P × Plane) × ℝ => (w.1.1, g.path k w.1.2 w.2)) := by
  have hp : ContDiff ℝ ∞ (fun w : (P × Plane) × ℝ => w.1.1) := contDiff_fst.fst
  have ht : ContDiff ℝ ∞ (fun w : (P × Plane) × ℝ => ((g.coordinates k w.1.2).1, w.2)) :=
    ((g.coordinates_contDiff k).comp contDiff_fst.snd).fst.prodMk contDiff_snd
  exact hp.prodMk ((g.point_contDiff k).comp ht)

end Geometry

namespace LinearData

variable (d : LinearData P V E) (g : Geometry) {U : Set P}

theorem coefficientAlong_continuousOn (k : Frequency)
    (hA : ContinuousOn d.coefficient (U ×ˢ univ)) :
    ContinuousOn (d.coefficientAlong g k) ((U ×ˢ univ) ×ˢ univ) :=
  hA.comp (g.nativeArgument_contDiff k).continuous.continuousOn
    (fun _ hw => ⟨hw.1.1, mem_univ _⟩)

theorem forcingAlong_continuousOn (k : Frequency)
    (hB : ContinuousOn d.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn d.source (U ×ˢ univ)) :
    ContinuousOn (d.forcingAlong g k) ((U ×ˢ univ) ×ˢ univ) :=
  (hB.comp (g.nativeArgument_contDiff k).continuous.continuousOn
    (fun _ hw => ⟨hw.1.1, mem_univ _⟩)).clm_apply
    (hf.comp (g.pathArgument_contDiff k).continuous.continuousOn
      (fun _ hw => ⟨hw.1.1, mem_univ _⟩))

theorem coefficientAlong_contDiffOn (k : Frequency)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (d.coefficientAlong g k) ((U ×ˢ univ) ×ˢ univ) :=
  hA.comp (g.nativeArgument_contDiff k).contDiffOn
    (fun _ hw => ⟨hw.1.1, mem_univ _⟩)

theorem forcingAlong_contDiffOn (k : Frequency)
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (d.forcingAlong g k) ((U ×ˢ univ) ×ˢ univ) :=
  (hB.comp (g.nativeArgument_contDiff k).contDiffOn
    (fun _ hw => ⟨hw.1.1, mem_univ _⟩)).clm_apply
    (hf.comp (g.pathArgument_contDiff k).contDiffOn
      (fun _ hw => ⟨hw.1.1, mem_univ _⟩))

variable [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)

/-- The constructed extension satisfies the original forced equation on the
copy path, including both endpoints as a differentiable extension. -/
theorem anchoredSolve_hasDerivAt (k : Frequency)
    (hA : ContinuousOn d.coefficient (U ×ˢ univ))
    (hB : ContinuousOn d.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn d.source (U ×ˢ univ))
    {p : P} (hp : p ∈ U) (Y : Plane) (s : Icc a b) :
    HasDerivAt (d.anchoredSolve g hab k (p, Y))
      (d.coefficientAlong g k ((p, Y), s) (d.anchoredSolve g hab k (p, Y) s) +
        d.forcingAlong g k ((p, Y), s)) s := by
  have hAc : Continuous (fun t : Icc a b => d.coefficientAlong g k ((p, Y), t)) :=
    SmoothPathFamily.slice_continuous
      ((d.coefficientAlong_continuousOn g k hA).mono
        (Set.prod_mono Subset.rfl (subset_univ _))) ⟨hp, mem_univ _⟩
  have hfc : Continuous (fun t : Icc a b => d.forcingAlong g k ((p, Y), t)) :=
    SmoothPathFamily.slice_continuous
      ((d.forcingAlong_continuousOn g k hB hf).mono
        (Set.prod_mono Subset.rfl (subset_univ _))) ⟨hp, mem_univ _⟩
  have hd := ParametricODE.solutionExtension_hasDerivAt hab
    (d.coefficientPath g k (p, Y)) 0 (d.forcingPath g k (p, Y)) s
  unfold anchoredSolve
  simpa only [coefficientPath, forcingPath,
    SmoothPathFamily.pathFamily_apply _ _ hAc, SmoothPathFamily.pathFamily_apply _ _ hfc]
    using hd

theorem copySolve_alongPath_hasDerivAt (k : Frequency)
    (hA : ContinuousOn d.coefficient (U ×ˢ univ))
    (hB : ContinuousOn d.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn d.source (U ×ˢ univ))
    {p : P} (hp : p ∈ U) (Y : Plane) (s : Icc a b) :
    HasDerivAt (fun t => d.copySolve g hab k (p, g.path k Y t))
      (d.coefficientAlong g k ((p, Y), s) (d.copySolve g hab k (p, g.path k Y s)) +
        d.forcingAlong g k ((p, Y), s)) s := by
  simpa only [copySolve_path] using d.anchoredSolve_hasDerivAt g hab k hA hB hf hp Y s

theorem anchoredSolve_unique (k : Frequency)
    (hA : ContinuousOn d.coefficient (U ×ˢ univ))
    (hB : ContinuousOn d.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn d.source (U ×ˢ univ))
    {p : P} (hp : p ∈ U) (Y : Plane) {u : ℝ → E} (hu0 : u a = 0)
    (hu : ∀ s ∈ Icc a b, HasDerivAt u
      (d.coefficientAlong g k ((p, Y), s) (u s) + d.forcingAlong g k ((p, Y), s)) s) :
    EqOn u (d.anchoredSolve g hab k (p, Y)) (Icc a b) := by
  apply TangentODE.linear_solution_unique hab
    (fun s => d.coefficientAlong g k ((p, Y), s))
    (fun s => d.forcingAlong g k ((p, Y), s))
    ((d.coefficientAlong_continuousOn g k hA).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s _ => ⟨⟨hp, mem_univ _⟩, mem_univ s⟩)) hu
    (fun s hs => d.anchoredSolve_hasDerivAt g hab k hA hB hf hp Y ⟨s, hs⟩)
  rw [d.anchoredSolve_initial]
  exact hu0

end LinearData

/-! ## Localization and the actual common-torus field -/

namespace Geometry

theorem cutoff_as_translate (g : Geometry) (κ : Plane → ℝ) (k : Frequency) (Y : Plane) :
    κ (g.coordinates k Y) = TorusAverages.nativeField g.basis g.center κ
      (TorusAverages.latticePoint (-k) + coverPower g.gap Y) := by
  have hneg : TorusAverages.latticePoint (-k) = -TorusAverages.latticePoint k := by
    ext <;> simp [TorusAverages.latticePoint]
  unfold coordinates TorusAverages.nativeField
  rw [hneg]
  congr 2
  abel

theorem finite_copy_cutoffs (g : Geometry) {κ : Plane → ℝ}
    (hκ : HasCompactSupport κ) (R : ℝ) :
    ∃ s : Finset Frequency, ∀ Y : Plane, ‖Y‖ ≤ R →
      ∀ k : Frequency, k ∉ s → κ (g.coordinates k Y) = 0 := by
  classical
  obtain ⟨s, hs⟩ := TorusAverages.finite_translates_on_ball
    (TorusAverages.nativeField_hasCompactSupport g.basis g.center hκ) ((6 : ℝ) ^ g.gap * R)
  refine ⟨s.image Neg.neg, ?_⟩
  intro Y hY k hk
  rw [g.cutoff_as_translate κ k Y]
  apply hs _ ((norm_coverPower_le g.gap Y).trans
    (mul_le_mul_of_nonneg_left hY (by positivity))) (-k)
  intro hneg
  exact hk (Finset.mem_image.mpr ⟨-k, hneg, neg_neg k⟩)

end Geometry

namespace LinearData

variable [CompleteSpace E] {a b : ℝ}
variable (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)

noncomputable def localizedCopy (κ : Plane → ℝ) (k : Frequency) (p : P × Plane) : E :=
  κ (g.coordinates k p.2) • d.copySolve g hab k p

/-- The actual sum of localized copy solves. Sources in different native
copies are evaluated at their own absolute-lift points. -/
noncomputable def commonSolve (κ : Plane → ℝ) (p : P × Plane) : E :=
  ∑' k : Frequency, d.localizedCopy g hab κ k p

theorem localizedCopy_deck (κ : Plane → ℝ) (k n : Frequency)
    (p : P) (hp : PeriodicAt d.source p) (Y : Plane) :
    d.localizedCopy g hab κ (k + coverIndex g.gap n) (p, Y + TorusAverages.latticePoint n) =
      d.localizedCopy g hab κ k (p, Y) := by
  unfold localizedCopy
  rw [g.coordinates_deck, d.copySolve_deck g hab k n p hp]

/-- Common-torus periodicity follows by reindexing the actual copy sum.
The source is required to be periodic only in the common variable. -/
theorem commonSolve_periodic (κ : Plane → ℝ) (p : P) (hp : PeriodicAt d.source p)
    (Y : Plane) (n : Frequency) :
    d.commonSolve g hab κ (p, Y + TorusAverages.latticePoint n) =
      d.commonSolve g hab κ (p, Y) := by
  unfold commonSolve
  calc
    (∑' k : Frequency, d.localizedCopy g hab κ k (p, Y + TorusAverages.latticePoint n)) =
        ∑' k : Frequency, d.localizedCopy g hab κ (k + coverIndex g.gap n)
          (p, Y + TorusAverages.latticePoint n) :=
      ((Equiv.addRight (coverIndex g.gap n)).tsum_eq
        (fun k => d.localizedCopy g hab κ k (p, Y + TorusAverages.latticePoint n))).symm
    _ = ∑' k : Frequency, d.localizedCopy g hab κ k (p, Y) := by
      apply tsum_congr
      intro k
      exact d.localizedCopy_deck g hab κ k n p hp Y

theorem commonSolve_preserves_slow_support (κ : Plane → ℝ) {U : Set P}
    (hf : ∀ p ∉ U, ∀ Y, d.source (p, Y) = 0) {p : P} (hp : p ∉ U) (Y : Plane) :
    d.commonSolve g hab κ (p, Y) = 0 := by
  have hzero (k : Frequency) : d.localizedCopy g hab κ k (p, Y) = 0 := by
    unfold localizedCopy
    rw [d.copySolve_preserves_slow_support g hab hf k hp Y, smul_zero]
  simp only [commonSolve, hzero, tsum_zero]

theorem localizedCopy_preserves_transverse_support (κ : Plane → ℝ) (k : Frequency)
    {S : Set ℝ} (p : P)
    (hf : ∀ xi ∉ S, ∀ eta ∈ Icc a b, d.source (p, g.point k (xi, eta)) = 0)
    (Y : Plane) (hY : (g.coordinates k Y).1 ∉ S) :
    d.localizedCopy g hab κ k (p, Y) = 0 := by
  unfold localizedCopy
  rw [d.copySolve_preserves_transverse_support g hab k p hf Y hY, smul_zero]

omit [NormedSpace ℝ P] in
theorem commonSolve_eventually_eq_sum {κ : Plane → ℝ} (hκ : HasCompactSupport κ)
    (p : P × Plane) :
    ∃ s : Finset Frequency,
      d.commonSolve g hab κ =ᶠ[𝓝 p] fun q => ∑ k ∈ s, d.localizedCopy g hab κ k q := by
  obtain ⟨s, hs⟩ := g.finite_copy_cutoffs hκ (‖p.2‖ + 1)
  refine ⟨s, ?_⟩
  have hn : {q : P × Plane | ‖q.2‖ < ‖p.2‖ + 1} ∈ 𝓝 p :=
    (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simp)
  filter_upwards [hn] with q hq
  apply tsum_eq_sum
  intro k hk
  unfold localizedCopy
  rw [hs q.2 hq.le k hk, zero_smul]

theorem commonSolve_contDiffOn_of_copies {U : Set P} (hU : IsOpen U)
    {κ : Plane → ℝ} (hκ : HasCompactSupport κ)
    (hc : ∀ k : Frequency, ContDiffOn ℝ ∞ (d.localizedCopy g hab κ k) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (d.commonSolve g hab κ) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro p hp
  obtain ⟨s, hs⟩ := d.commonSolve_eventually_eq_sum g hab hκ p
  have hsum : ContDiffAt ℝ ∞ (fun q => ∑ k ∈ s, d.localizedCopy g hab κ k q) p :=
    ContDiffAt.sum (fun k _ => (hc k).contDiffAt ((hU.prod isOpen_univ).mem_nhds hp))
  exact hsum.congr_of_eventuallyEq hs

end LinearData

end Paths

/-! ## A function on the quotient torus, not merely a periodic lift -/

def LatticePeriodic {W : Type} (f : Plane → W) : Prop :=
  ∀ Y : Plane, ∀ k : Frequency, f (Y + TorusAverages.latticePoint k) = f Y

theorem latticePeriodic_first {W : Type} {f : Plane → W} (hf : LatticePeriodic f) (y : ℝ) :
    Function.Periodic (fun x => f (x, y)) 1 := by
  intro x
  simpa [TorusAverages.latticePoint] using hf (x, y) (1, 0)

theorem latticePeriodic_second {W : Type} {f : Plane → W} (hf : LatticePeriodic f) (x : ℝ) :
    Function.Periodic (fun y => f (x, y)) 1 := by
  intro y
  simpa [TorusAverages.latticePoint] using hf (x, y) (0, 1)

noncomputable def firstDescent {W : Type} (f : Plane → W) (hf : LatticePeriodic f)
    (z : UnitAddCircle) (y : ℝ) : W := (latticePeriodic_first hf y).lift z

theorem firstDescent_periodic {W : Type} (f : Plane → W) (hf : LatticePeriodic f)
    (z : UnitAddCircle) : Function.Periodic (firstDescent f hf z) 1 := by
  intro y
  refine Quotient.inductionOn' z (fun x => ?_)
  change f (x, y + 1) = f (x, y)
  exact latticePeriodic_second hf x y

noncomputable def torusDescent {W : Type} (f : Plane → W) (hf : LatticePeriodic f)
    (z : Torus) : W := (firstDescent_periodic f hf z.1).lift z.2

theorem torusDescent_coe {W : Type} (f : Plane → W) (hf : LatticePeriodic f) (Y : Plane) :
    torusDescent f hf (TorusAverages.quotientPoint Y) = f Y := rfl

theorem torusDescent_continuous {W : Type} [TopologicalSpace W] {f : Plane → W}
    (hf : LatticePeriodic f) (hc : Continuous f) : Continuous (torusDescent f hf) := by
  have hq : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  exact (hq.prodMap hq).isQuotientMap.continuous_iff.mpr hc

namespace LinearData

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)

/-- The constructed common-torus solution is obtained by a genuine quotient
lift of the reindexed copy sum. -/
noncomputable def commonOnTorus (κ : Plane → ℝ) (p : P) (hp : PeriodicAt d.source p) :
    Torus → E := torusDescent (fun Y => d.commonSolve g hab κ (p, Y))
      (d.commonSolve_periodic g hab κ p hp)

theorem commonOnTorus_coe (κ : Plane → ℝ) (p : P) (hp : PeriodicAt d.source p) (Y : Plane) :
    d.commonOnTorus g hab κ p hp (TorusAverages.quotientPoint Y) =
      d.commonSolve g hab κ (p, Y) := rfl

/-! Joint regularity is derived from the actual ODE construction. -/

theorem anchoredSolve_contDiffOn {U : Set P} (hU : IsOpen U) (k : Frequency)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : (P × Plane) × ℝ => d.anchoredSolve g hab k z.1 z.2)
      ((U ×ˢ univ) ×ˢ Ioo a b) := by
  exact JointODE.contDiffOn_solutionExtension_joint_interior hab (U ×ˢ univ) univ
    (hU.prod isOpen_univ) isOpen_univ (subset_univ _)
    (d.coefficientAlong g k) (fun _ => 0) (d.forcingAlong g k)
    (d.coefficientAlong_contDiffOn g k hA) contDiffOn_const
    (d.forcingAlong_contDiffOn g k hB hf)

theorem copySolve_contDiffAt {U : Set P} (hU : IsOpen U) (k : Frequency)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {p : P × Plane} (hp : p.1 ∈ U) (heta : (g.coordinates k p.2).2 ∈ Ioo a b) :
    ContDiffAt ℝ ∞ (d.copySolve g hab k) p := by
  have hz : (p, (g.coordinates k p.2).2) ∈ ((U ×ˢ (univ : Set Plane)) ×ˢ Ioo a b) :=
    ⟨⟨hp, mem_univ _⟩, heta⟩
  have hs := (d.anchoredSolve_contDiffOn g hab hU k hA hB hf).contDiffAt
    (((hU.prod isOpen_univ).prod isOpen_Ioo).mem_nhds hz)
  have hc : ContDiff ℝ ∞ (fun q : P × Plane => (q, (g.coordinates k q.2).2)) :=
    contDiff_id.prodMk (((g.coordinates_contDiff k).comp contDiff_snd).snd)
  have hcomp := hs.comp p hc.contDiffAt
  exact hcomp

/-- The localization cutoff is supported strictly inside the slot interval.
The clamped extension outside the interval is never claimed to be smooth. -/
theorem localizedCopy_contDiffOn {U : Set P} (hU : IsOpen U) (k : Frequency)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) :
    ContDiffOn ℝ ∞ (d.localizedCopy g hab κ k) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro p hp
  have hc : ContDiff ℝ ∞ (fun q : P × Plane => g.coordinates k q.2) :=
    (g.coordinates_contDiff k).comp contDiff_snd
  by_cases hmem : g.coordinates k p.2 ∈ tsupport κ
  · exact ((hκ.comp hc).contDiffAt).smul
      (d.copySolve_contDiffAt g hab hU k hA hB hf hp.1 (hsupp hmem).2)
  · have hz : κ =ᶠ[𝓝 (g.coordinates k p.2)] (fun _ => 0) :=
      notMem_tsupport_iff_eventuallyEq.mp hmem
    have hzero : d.localizedCopy g hab κ k =ᶠ[𝓝 p] (fun _ => (0 : E)) := by
      filter_upwards [hz.comp_tendsto hc.continuous.continuousAt] with q hq
      change κ (g.coordinates k q.2) = 0 at hq
      simp only [localizedCopy, hq, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- The actual sum of native copy solves is jointly smooth in slow and common
torus coordinates. Local finiteness was proved from compact support. -/
theorem commonSolve_contDiffOn {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) :
    ContDiffOn ℝ ∞ (d.commonSolve g hab κ) (U ×ˢ univ) :=
  d.commonSolve_contDiffOn_of_copies g hab hU hcκ
    (fun k => d.localizedCopy_contDiffOn g hab hU k hA hB hf hκ hsupp)

theorem commonOnTorus_continuous {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (p : P) (hp : p ∈ U)
    (hper : PeriodicAt d.source p) : Continuous (d.commonOnTorus g hab κ p hper) := by
  apply torusDescent_continuous
  exact (d.commonSolve_contDiffOn g hab hU hA hB hf hκ hcκ hsupp).continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, mem_univ _⟩)

end LinearData

/-! ## Bounded covering gaps and actual derivative costs -/

noncomputable def coveringBound (D : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D + 1),
    (‖(coverPower d : Plane →L[ℝ] Plane)‖ + ‖((coverPower d).symm : Plane →L[ℝ] Plane)‖)

theorem coveringBound_pos (D : ℕ) : 0 < coveringBound D := by
  unfold coveringBound
  positivity

theorem coveringNorm_le_bound {d D : ℕ} (hd : d ≤ D) :
    ‖(coverPower d : Plane →L[ℝ] Plane)‖ ≤ coveringBound D := by
  have hm : d ∈ Finset.range (D + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hs := Finset.single_le_sum
    (f := fun i => ‖(coverPower i : Plane →L[ℝ] Plane)‖ +
      ‖((coverPower i).symm : Plane →L[ℝ] Plane)‖)
    (fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hm
  exact ((le_add_of_nonneg_right (norm_nonneg ((coverPower d).symm : Plane →L[ℝ] Plane))).trans
    hs).trans
    (le_add_of_nonneg_left zero_le_one)

theorem inverseCoveringNorm_le_bound {d D : ℕ} (hd : d ≤ D) :
    ‖((coverPower d).symm : Plane →L[ℝ] Plane)‖ ≤ coveringBound D := by
  have hm : d ∈ Finset.range (D + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hs := Finset.single_le_sum
    (f := fun i => ‖(coverPower i : Plane →L[ℝ] Plane)‖ +
      ‖((coverPower i).symm : Plane →L[ℝ] Plane)‖)
    (fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hm
  exact ((le_add_of_nonneg_left (norm_nonneg (coverPower d : Plane →L[ℝ] Plane))).trans hs).trans
    (le_add_of_nonneg_left zero_le_one)

namespace Geometry

variable (g : Geometry)

noncomputable def coordinateLinear : Plane →L[ℝ] Plane :=
  (g.basis.symm : Plane →L[ℝ] Plane).comp (coverPower g.gap : Plane →L[ℝ] Plane)

noncomputable def pointLinear : Plane →L[ℝ] Plane :=
  ((coverPower g.gap).symm : Plane →L[ℝ] Plane).comp (g.basis : Plane →L[ℝ] Plane)

noncomputable def horizontal : Plane →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0

noncomputable def pathLinear : Plane →L[ℝ] Plane :=
  g.pointLinear.comp (horizontal.comp g.coordinateLinear)

theorem coordinates_eq_affine (k : Frequency) (Y : Plane) :
    g.coordinates k Y = g.coordinates k 0 + g.coordinateLinear Y := by
  simp only [coordinates, coordinateLinear, ContinuousLinearMap.comp_apply, map_sub, map_zero]
  simp only [ContinuousLinearEquiv.coe_coe]
  abel

theorem point_eq_affine (k : Frequency) (Y : Plane) :
    g.point k Y = g.point k 0 + g.pointLinear Y := by
  simp only [point, pointLinear, ContinuousLinearMap.comp_apply, map_add, map_zero, add_zero,
    ContinuousLinearEquiv.coe_coe]

theorem path_eq_affine (k : Frequency) (eta : ℝ) (Y : Plane) :
    g.path k Y eta = g.path k 0 eta + g.pathLinear Y := by
  have harg : ((g.coordinates k Y).1, eta) =
      ((g.coordinates k 0).1, eta) + horizontal (g.coordinateLinear Y) := by
    rw [g.coordinates_eq_affine k Y]
    ext <;> simp [horizontal]
  change g.point k ((g.coordinates k Y).1, eta) = _
  rw [harg, g.point_add]
  rfl

theorem norm_coordinateLinear_le {D : ℕ} (hd : g.gap ≤ D) :
    ‖g.coordinateLinear‖ ≤ ‖(g.basis.symm : Plane →L[ℝ] Plane)‖ * coveringBound D :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (coveringNorm_le_bound hd) (norm_nonneg _))

theorem norm_pointLinear_le {D : ℕ} (hd : g.gap ≤ D) :
    ‖g.pointLinear‖ ≤ coveringBound D * ‖(g.basis : Plane →L[ℝ] Plane)‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (inverseCoveringNorm_le_bound hd) (norm_nonneg _))

theorem norm_horizontal_le : ‖horizontal‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  change max ‖Y.1‖ ‖(0 : ℝ)‖ ≤ 1 * ‖Y‖
  rw [norm_zero, max_eq_left (norm_nonneg _), one_mul]
  exact norm_fst_le Y

noncomputable def pathBound (D : ℕ) : ℝ :=
  (coveringBound D * ‖(g.basis : Plane →L[ℝ] Plane)‖) *
    (‖(g.basis.symm : Plane →L[ℝ] Plane)‖ * coveringBound D)

theorem pathBound_nonneg (D : ℕ) : 0 ≤ g.pathBound D := by
  unfold pathBound
  exact mul_nonneg (mul_nonneg (coveringBound_pos D).le (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (coveringBound_pos D).le)

theorem norm_pathLinear_le {D : ℕ} (hd : g.gap ≤ D) :
    ‖g.pathLinear‖ ≤ g.pathBound D := by
  have hh : ‖horizontal.comp g.coordinateLinear‖ ≤ ‖g.coordinateLinear‖ := by
    have hmul := mul_le_mul_of_nonneg_right norm_horizontal_le (norm_nonneg g.coordinateLinear)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by simpa only [one_mul] using hmul)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans
      (mul_le_mul (g.norm_pointLinear_le hd) (g.norm_coordinateLinear_le hd)
        (norm_nonneg _) (mul_nonneg (coveringBound_pos D).le (norm_nonneg _))))

/-- The common-variable path shifts have a bound depending only on the finite
index gap and the fixed native basis, never on the copy index. -/
theorem path_displacement_le {D : ℕ} (hd : g.gap ≤ D) (k : Frequency) (Y : Plane) (eta : ℝ) :
    ‖g.path k Y eta - Y‖ ≤ coveringBound D *
      (|eta - (g.coordinates k Y).2| * ‖g.basis (0, 1)‖) := by
  rw [g.path_eq_shift, add_sub_cancel_left]
  have h := ((coverPower g.gap).symm : Plane →L[ℝ] Plane).le_opNorm
    ((eta - (g.coordinates k Y).2) • g.basis (0, 1))
  exact h.trans (by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (inverseCoveringNorm_le_bound hd) (by positivity))

end Geometry

/-- All actual derivative orders of an affine pullback have the expected
operator-norm cost. No independent jet family is supplied. -/
theorem norm_iteratedFDeriv_affine_le {X Y W : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Y → W} (hf : ContDiff ℝ ∞ f) (L : X →L[ℝ] Y) (c : Y) (x : X) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => f (c + L z)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (c + L x)‖ * ‖L‖ ^ n := by
  have hh : ContDiff ℝ ∞ (fun z => f (c + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hd := L.iteratedFDeriv_comp_right hh x (i := n)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  change ‖iteratedFDeriv ℝ n ((fun z => f (c + z)) ∘ L) x‖ ≤ _
  rw [hd]
  simpa only [iteratedFDeriv_comp_add_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using
      (iteratedFDeriv ℝ n (fun z => f (c + z)) (L x)).norm_compContinuousLinearMap_le
        (fun _ : Fin n => L)

theorem Geometry.norm_path_pullback_jet_le {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (g : Geometry) {D : ℕ} (hd : g.gap ≤ D)
    {f : Plane → W} (hf : ContDiff ℝ ∞ f) (k : Frequency) (eta : ℝ) (Y : Plane) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun Z => f (g.path k Z eta)) Y‖ ≤
      ‖iteratedFDeriv ℝ n f (g.path k Y eta)‖ * (g.pathBound D) ^ n := by
  have h := norm_iteratedFDeriv_affine_le hf g.pathLinear (g.path k 0 eta) Y n
  have heq : (fun Z => f (g.path k Z eta)) =
      (fun Z => f (g.path k 0 eta + g.pathLinear Z)) := by
    funext Z
    rw [g.path_eq_affine k eta Z]
  rw [← heq, ← g.path_eq_affine k eta Y] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (g.norm_pathLinear_le hd) n) (norm_nonneg _))

/-- The verified weighted ODE estimate applies to this exact path solve.
All hypotheses are bounds on the actual pulled-back input coefficients and
source, rather than bounds or equations assumed for an output family. -/
theorem LinearData.anchoredSolve_jets_le_polynomial
    {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U) (k : Frequency)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {p : P × Plane} (hp : p.1 ∈ U)
    (rate W : ℝ → ℝ) {μ S K w : ℝ} (hμ : 0 ≤ μ)
    (hW : ∀ t, 0 < W t) (hdW : ∀ t, HasDerivAt W (rate t * W t) t)
    (henergy : ∀ t : Icc a b, ∀ x : E,
      ⟪x, d.coefficientAlong g k (p, t) x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2)
    (hC : Real.exp (μ * (b - a)) ≤ K) (hS : 1 ≤ S) (hK : 1 ≤ K) (hw : 0 ≤ w)
    (hslot : b - a ≤ K * S) (m N : ℕ)
    (hAj : ∀ j : ℕ, j ≤ N → ∀ t : Icc a b,
      ‖iteratedFDeriv ℝ j (fun q => d.coefficientAlong g k (q, t)) p‖ ≤ K * S ^ m)
    (hfj : ∀ j : ℕ, j ≤ N → ∀ t : Icc a b,
      ‖iteratedFDeriv ℝ j (fun q => d.forcingAlong g k (q, t)) p‖ ≤ w * K * S ^ m * W t)
    (n : ℕ) (hn : n ≤ N) (t : Icc a b) :
    ‖iteratedFDeriv ℝ n (fun q => d.anchoredSolve g hab k q t) p‖ ≤
      w * ((2 : ℝ) ^ (N + 1) * K ^ 3) ^ (n + 1) * S ^ ((m + 1) * (n + 1)) * W t := by
  have heq : (fun q => d.anchoredSolve g hab k q t) =
      (fun q => SmoothPathFamily.odeFamily hab (d.coefficientAlong g k) (fun _ => 0)
        (d.forcingAlong g k) q t) := by
    funext q
    exact ParametricODE.solutionExtension_coe hab _ _ _ t
  rw [heq]
  apply WeightedODEJets.norm_iteratedFDeriv_odeFamily_le_polynomial hab (U ×ˢ univ) univ
    (hU.prod isOpen_univ) isOpen_univ (subset_univ _)
    (d.coefficientAlong g k) (fun _ => 0) (d.forcingAlong g k)
    (d.coefficientAlong_contDiffOn g k hA) contDiffOn_const
    (d.forcingAlong_contDiffOn g k hB hf) ⟨hp, mem_univ _⟩
    rate W hμ hW hdW henergy hC hS hK hw hslot m N hAj _ hfj n hn t
  intro j _
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  exact mul_nonneg (mul_nonneg (mul_nonneg hw hK0) (pow_nonneg hS0 m)) (hW a).le

/-! ## Concrete projected tangent equation -/

noncomputable def negativeTangentProjection {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (n : H) : H →L[ℝ] H :=
  -(ContinuousLinearMap.id ℝ H - (innerSL ℝ n).smulRight ((⟪n, n⟫_ℝ)⁻¹ • n))

theorem negativeTangentProjection_apply {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (n x : H) :
    negativeTangentProjection n x = -TangentProjection.tangentProj n x := by
  simp only [negativeTangentProjection, _root_.neg_apply,
    _root_.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
    TangentProjection.tangentProj, div_eq_mul_inv]

/-- All quantities in the actual projected tangent equation, before solving.
The native normal and its slot derivative are explicit input fields. -/
structure TangentData (P H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  normal : P × Plane → H
  normalDot : P × Plane → H
  action : P × Plane → H →L[ℝ] H
  damping : P × Plane → ℝ
  source : P × Plane → H

namespace TangentData

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (t : TangentData P H) (g : Geometry) {a b : ℝ} (hab : a ≤ b)

noncomputable def linearData : LinearData P H H where
  coefficient z := TangentODE.projectedOperator (t.normal z) (t.normalDot z)
    (t.action z) (t.damping z)
  forcingMap z := negativeTangentProjection (t.normal z)
  source := t.source

/-- The concrete copy solve satisfies equation (27) with the source evaluated
at the actual lifted earlier point, including the normal-motion term. -/
theorem anchoredSolve_projected_equation {U : Set P} (k : Frequency)
    (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ)) {p : P} (hp : p ∈ U)
    (Y : Plane) (s : Icc a b) :
    let z := (p, ((g.coordinates k Y).1, (s : ℝ)))
    HasDerivAt (t.linearData.anchoredSolve g hab k (p, Y))
      (TangentProjection.projectedRhs (t.normal z) (t.normalDot z)
        (t.linearData.anchoredSolve g hab k (p, Y) s)
        (t.action z (t.linearData.anchoredSolve g hab k (p, Y) s))
        (t.source (p, g.path k Y s)) (t.damping z)) s := by
  have hd := t.linearData.anchoredSolve_hasDerivAt g hab k hA hB hf hp Y s
  simpa only [LinearData.coefficientAlong, LinearData.forcingAlong, linearData,
    negativeTangentProjection_apply, ← sub_eq_add_neg, TangentODE.projectedOperator_apply]
    using hd

/-- Tangency of this constructed solution follows from the moving-normal
defect equation and zero initial data. -/
theorem copySolve_tangent {U : Set P} (k : Frequency)
    (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ))
    (hδ : ContinuousOn t.damping (U ×ˢ univ)) {p : P} (hp : p ∈ U) (Y : Plane)
    (hn0 : ∀ s ∈ Icc a b, t.normal (p, ((g.coordinates k Y).1, s)) ≠ 0)
    (hn : ∀ s ∈ Icc a b,
      HasDerivAt (fun v => t.normal (p, ((g.coordinates k Y).1, v)))
        (t.normalDot (p, ((g.coordinates k Y).1, s))) s)
    (heta : (g.coordinates k Y).2 ∈ Icc a b) :
    ⟪t.normal (p, g.coordinates k Y), t.linearData.copySolve g hab k (p, Y)⟫_ℝ = 0 := by
  have hδ' : ContinuousOn (fun s => t.damping (p, ((g.coordinates k Y).1, s))) (Icc a b) :=
    hδ.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
      (fun _ _ => ⟨hp, mem_univ _⟩)
  have hu := TangentODE.projected_tangency_preserved hab
    (fun s => t.normal (p, ((g.coordinates k Y).1, s)))
    (fun s => t.normalDot (p, ((g.coordinates k Y).1, s)))
    (fun s => t.source (p, g.path k Y s))
    (t.linearData.anchoredSolve g hab k (p, Y))
    (fun s => t.action (p, ((g.coordinates k Y).1, s)))
    (fun s => t.damping (p, ((g.coordinates k Y).1, s))) hδ' hn0 hn
    (fun s hs => t.anchoredSolve_projected_equation g hab k hA hB hf hp Y ⟨s, hs⟩)
    (by simp only [t.linearData.anchoredSolve_initial g hab, inner_zero_right])
  exact hu _ heta

end TangentData

end NavierStokes.CommonCoverSolve
