/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development005






public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development002


public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001





public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.IntermediateValue
/-!
# Moving sofa: related mathematical developments

* `Motion.Foundations.Development001`.
* `Bounds.Foundations.Development001`.
* `Cap.Foundations.Development004`.
* `Bounds.Foundations.Development002`.
* `Geometry.Foundations.Development005`.
* `Analysis.Foundations.Development005`.
* `Convex.Foundations.Development003`.
* `Convex.Foundations.Development004`.
* `Area.Foundations.Development004`.
* `Optimality`.
* `Motion.Foundations.Development003`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Motion.Basic`.
* `Motion.CommonSubset`.
* `Motion.Compactness`.
* `Motion.Rotation`.
* `Motion.AngleLift`.
* `Motion.RotationAngleCalculation`.
* `Motion.SupportingHallways`.
* `Motion.Translation`.
* `Motion.StandardPosition`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Basic
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- A paper motion permits an initial translation and preserves orientation at every time. -/
@[expose]
def IsPaperMotion (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point) : Prop :=
  IsConnected s ∧ IsClosed s ∧ Continuous m ∧
    (∃ q : Point, ∀ p, m 0 p = p + q) ∧
    (∀ t, ∃ a : Real.Angle, ∀ p, m t p = rotationMap a p + m t 0) ∧
    m 0 '' s ⊆ horizontalHallway ∧
    (∀ t, m t '' s ⊆ hallway) ∧ m 1 '' s ⊆ verticalHallway

/-- Movability in the paper's translation-invariant convention. -/
@[expose]
def IsPaperMovingSofa (s : Set Point) : Prop :=
  ∃ m, IsPaperMotion s m

/-- Clockwise rotation angle of a particular admissible lifted motion witness. -/
@[expose]
def HasRotationAngle (s : Set Point) (ω : ℝ) : Prop :=
  ∃ (m : I → Point ≃ᵃⁱ[ℝ] Point), IsPaperMotion s m ∧
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ α 1 = -ω ∧
      ∀ t p, m t p = rotationMap (α t : Real.Angle) p + m t 0

/-- Standard position for a compact moving sofa with the specified rotation angle. -/
@[expose]
def IsStandardPosition (s : Set Point) (ω : ℝ) : Prop :=
  IsCompact s ∧ HasRotationAngle s ω ∧ 0 < ω ∧ ω ≤ Real.pi / 2 ∧
    supportValue s (ω : Real.Angle) = 1 ∧
    supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1

/-- The cap set constructed from all supporting outer quadrants. -/
@[expose]
def capOfSofa (s : Set Point) (ω : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    ⋂ t ∈ Set.Icc 0 ω, (rotatingHallwayParts s (t : Real.Angle)).outerQuadrant

/-- The intersection of supporting hallways used for monotonization. -/
@[expose]
def monotonization (s : Set Point) (ω : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩ ⋂ t ∈ Set.Icc 0 ω, supportingHallway s (t : Real.Angle)

/-- A monotone sofa is the monotonization of a sofa in standard position. -/
@[expose]
def IsMonotoneSofa (s : Set Point) : Prop :=
  ∃ (s₀ : Set Point) (ω : ℝ), IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω

/-- The finite-angle outer approximation to a cap. -/
@[expose]
def angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) : Set Point :=
  (stripParallelogram Θ.angle).1 ∩
    ⋂ t ∈ Θ.directions, (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).outerQuadrant

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Common Subset
-/

public section

noncomputable section

namespace MovingSofa

theorem HasRotationAngle.exists_translated_rotated_hallway {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) {t : ℝ} (ht : t ∈ Set.Icc 0 ω) :
    ∃ v : Point, s ⊆ (fun p ↦ rotationMap (t : Real.Angle) p + v) '' hallway := by
  obtain ⟨m, hm, α, hα, hα0, hα1, hmotion⟩ := hs
  obtain ⟨_, _, _, _, _, _, hhallway, _⟩ := hm
  obtain ⟨τ, hτ⟩ := mem_range_of_exists_le_of_exists_ge (c := -t) hα
    ⟨1, by rw [hα1]; linarith [ht.2]⟩ ⟨0, by rw [hα0]; linarith [ht.1]⟩
  refine ⟨-rotationMap (t : Real.Angle) (m τ 0), ?_⟩
  intro p hp
  refine ⟨m τ p, hhallway τ ⟨p, hp, rfl⟩, ?_⟩
  rw [hmotion τ p, hτ]
  simp only [rotationMap, Real.Angle.coe_neg, map_add,
    ← EuclideanGeometry.o.rotation_symm, LinearIsometryEquiv.apply_symm_apply,
    add_neg_cancel_right]

theorem HasRotationAngle.exists_translated_horizontal_strip {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    ∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).1 := by
  obtain ⟨m, hm, _⟩ := hs
  obtain ⟨_, _, _, ⟨v, hv⟩, _, hstart, _, _⟩ := hm
  refine ⟨-v, ?_⟩
  intro p hp
  have hmem := hstart ⟨p, hp, rfl⟩
  obtain ⟨x, y, hxy, heq⟩ := hmem
  refine ⟨p + v, ?_, by simp⟩
  change 0 ≤ (p + v) 1 ∧ (p + v) 1 ≤ 1
  rw [← hv p, ← heq]
  exact ⟨hxy.2.1, hxy.2.2⟩

theorem HasRotationAngle.exists_translated_vertical_strip {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    ∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).2.2 := by
  obtain ⟨m, hm, α, _, _, hα1, hmotion⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, hend⟩ := hm
  refine ⟨-rotationMap (ω : Real.Angle) (m 1 0), ?_⟩
  intro p hp
  have hmem := hend ⟨p, hp, rfl⟩
  obtain ⟨x, y, hxy, heq⟩ := hmem
  refine ⟨rotationMap (ω : Real.Angle) (m 1 p), ?_, ?_⟩
  · refine ⟨m 1 p, ?_, rfl⟩
    change 0 ≤ (m 1 p) 0 ∧ (m 1 p) 0 ≤ 1
    rw [← heq]
    exact ⟨hxy.1, hxy.2.1⟩
  · rw [hmotion 1 p, hα1]
    simp only [rotationMap, Real.Angle.coe_neg, map_add,
      ← EuclideanGeometry.o.rotation_symm, LinearIsometryEquiv.apply_symm_apply,
      add_neg_cancel_right]

private theorem isBounded_of_oblique_bounds (s : Set Point) (a c d A B : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hy : ∀ p ∈ s, a ≤ p 1 ∧ p 1 ≤ a + 1)
    (hx : ∀ p ∈ s, c * p 0 + d * p 1 ≤ A ∧ -d * p 0 + c * p 1 ≤ B) :
    Bornology.IsBounded s := by
  let l := (c * a - B) / d
  let u := (A - d * a) / c
  let M := |l| + |u|
  let N := |a| + |a + 1|
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + N, ?_⟩
  intro p hp
  obtain ⟨hy0, hy1⟩ := hy p hp
  obtain ⟨hx0, hx1⟩ := hx p hp
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hu : p 0 ≤ u := by
    apply (le_div_iff₀ hc).2
    nlinarith
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN : 0 ≤ N := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hxabs : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self u, abs_nonneg l, abs_nonneg u]
  have hyabs : |p 1| ≤ N := by
    apply abs_le.mpr
    dsimp [N]
    constructor <;> linarith [neg_abs_le a, le_abs_self (a + 1),
      abs_nonneg a, abs_nonneg (a + 1)]
  have hx2 := pow_le_pow_left₀ (abs_nonneg (p 0)) hxabs 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg (p 1)) hyabs 2
  have hnorm := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hnorm hx2 hy2
  nlinarith [mul_nonneg hM hN, norm_nonneg p]

theorem HasRotationAngle.isCompact {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) : IsCompact s := by
  obtain ⟨v, hv⟩ := hs.exists_translated_horizontal_strip
  have ht : ω / 2 ∈ Set.Icc 0 ω := ⟨by linarith [hω.1], by linarith [hω.1]⟩
  obtain ⟨w, hw⟩ := hs.exists_translated_rotated_hallway ht
  have hc : 0 < Real.cos (ω / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hω.1, Real.pi_pos], by linarith [hω.2, Real.pi_pos]⟩
  have hd : 0 < Real.sin (ω / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hω.1]) (by linarith [hω.2, Real.pi_pos])
  have hb : Bornology.IsBounded s := isBounded_of_oblique_bounds s (v 1)
      (Real.cos (ω / 2)) (Real.sin (ω / 2))
      (1 + inner ℝ w (normalVector ((ω / 2 : ℝ) : Real.Angle)))
      (1 + inner ℝ w (tangentVector ((ω / 2 : ℝ) : Real.Angle))) hc hd
      (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := hv hp
        change 0 ≤ q 1 ∧ q 1 ≤ 1 at hq
        change v 1 ≤ q 1 + v 1 ∧ q 1 + v 1 ≤ v 1 + 1
        constructor <;> linarith [hq.1, hq.2])
      (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := hw hp
        have hq01 : q 0 ≤ 1 ∧ q 1 ≤ 1 := by
          rcases hq with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
          · exact ⟨h.1, h.2.2⟩
          · exact ⟨h.2.1, h.2.2⟩
        obtain ⟨hq0, hq1⟩ := hq01
        have hn : inner ℝ (rotationMap ((ω / 2 : ℝ) : Real.Angle) q + w)
            (normalVector ((ω / 2 : ℝ) : Real.Angle)) ≤
              1 + inner ℝ w (normalVector ((ω / 2 : ℝ) : Real.Angle)) := by
          rw [inner_add_left, inner_rotationMap_normalVector]
          linarith
        have ht : inner ℝ (rotationMap ((ω / 2 : ℝ) : Real.Angle) q + w)
            (tangentVector ((ω / 2 : ℝ) : Real.Angle)) ≤
              1 + inner ℝ w (tangentVector ((ω / 2 : ℝ) : Real.Angle)) := by
          rw [inner_add_left, inner_rotationMap_tangentVector]
          linarith
        simpa [normalVector, tangentVector, frame, PiLp.inner_apply,
          Fin.sum_univ_two, Real.inner_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
          mul_comm] using And.intro hn ht)
  obtain ⟨m, hm, _⟩ := hs
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hm.2.1, hb⟩

private theorem width_le_of_forall_mem_Icc {s : Set Point} (hne : s.Nonempty)
    (f : Point → ℝ) (a b : ℝ) (h : ∀ p ∈ s, a ≤ f p ∧ f p ≤ b) :
    sSup (f '' s) - sInf (f '' s) ≤ b - a := by
  have hu : sSup (f '' s) ≤ b := csSup_le (hne.image f) (by
    rintro _ ⟨p, hp, rfl⟩
    exact (h p hp).2)
  have hl : a ≤ sInf (f '' s) := le_csInf (hne.image f) (by
    rintro _ ⟨p, hp, rfl⟩
    exact (h p hp).1)
  linarith

theorem HasRotationAngle.horizontal_width_le {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    sSup ((fun p : Point ↦ p 1) '' s) - sInf ((fun p : Point ↦ p 1) '' s) ≤ 1 := by
  obtain ⟨v, hv⟩ := hs.exists_translated_horizontal_strip
  obtain ⟨m, hm, _⟩ := hs
  have hb := width_le_of_forall_mem_Icc hm.1.nonempty (fun p ↦ p 1) (v 1) (v 1 + 1)
    (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := hv hp
      change 0 ≤ q 1 ∧ q 1 ≤ 1 at hq
      change v 1 ≤ q 1 + v 1 ∧ q 1 + v 1 ≤ v 1 + 1
      constructor <;> linarith [hq.1, hq.2])
  simpa using hb

theorem HasRotationAngle.normal_width_le {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    sSup ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) -
      sInf ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) ≤ 1 := by
  obtain ⟨v, hv⟩ := hs.exists_translated_vertical_strip
  obtain ⟨m, hm, _⟩ := hs
  have hb := width_le_of_forall_mem_Icc hm.1.nonempty
    (fun p ↦ inner ℝ p (normalVector (ω : Real.Angle)))
    (inner ℝ v (normalVector (ω : Real.Angle)))
    (inner ℝ v (normalVector (ω : Real.Angle)) + 1) (by
      intro p hp
      obtain ⟨q, ⟨r, hr, rfl⟩, rfl⟩ := hv hp
      change 0 ≤ r 0 ∧ r 0 ≤ 1 at hr
      rw [inner_add_left, inner_rotationMap_normalVector]
      constructor <;> linarith [hr.1, hr.2])
  simpa using hb

private theorem subset_Icc_of_width_le_of_csSup_eq {s : Set ℝ}
    (hbelow : BddBelow s) (habove : BddAbove s)
    (hwidth : sSup s - sInf s ≤ 1) (hsup : sSup s = 1) : s ⊆ Set.Icc 0 1 := by
  intro x hx
  have hl := csInf_le hbelow hx
  have hu := le_csSup habove hx
  rw [hsup] at hwidth hu
  exact ⟨by linarith, hu⟩

theorem IsStandardPosition.subset_strips {s : Set Point} {ω : ℝ}
    (hs : IsStandardPosition s ω) : s ⊆ (strips ω).1 ∩ (strips ω).2.2 := by
  obtain ⟨hcompact, hmotion, _, _, hnormal, hvertical⟩ := hs
  have hcy : IsCompact ((fun p : Point ↦ p 1) '' s) := hcompact.image (by fun_prop)
  have hcn : IsCompact ((fun p : Point ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) :=
    hcompact.image (by fun_prop)
  have hsupy : sSup ((fun p : Point ↦ p 1) '' s) = 1 := by
    simpa [supportValue, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hvertical
  have hy := subset_Icc_of_width_le_of_csSup_eq hcy.bddBelow hcy.bddAbove
    hmotion.horizontal_width_le hsupy
  have hn := subset_Icc_of_width_le_of_csSup_eq hcn.bddBelow hcn.bddAbove
    hmotion.normal_width_le hnormal
  intro p hp
  refine ⟨hy ⟨p, hp, rfl⟩, ?_⟩
  obtain ⟨q, rfl⟩ := (EuclideanGeometry.o.rotation (ω : Real.Angle)).surjective p
  refine ⟨q, ?_, rfl⟩
  have hb := hn ⟨rotationMap (ω : Real.Angle) q, hp, rfl⟩
  change 0 ≤ q 0 ∧ q 0 ≤ 1
  simpa only [Set.mem_Icc, inner_rotationMap_normalVector] using hb

theorem movingSofa_commonSubset (s : Set Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) :
    IsCompact s ∧
    (∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).1) ∧
    (∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).2.2) ∧
    (∀ t ∈ Set.Icc 0 ω, ∃ v : Point,
      s ⊆ (fun p ↦ rotationMap (t : Real.Angle) p + v) '' hallway) ∧
    (sSup ((fun p : Point ↦ p 1) '' s) - sInf ((fun p : Point ↦ p 1) '' s) ≤ 1) ∧
    (sSup ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) -
      sInf ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) ≤ 1) ∧
    (IsStandardPosition s ω → s ⊆ (strips ω).1 ∩ (strips ω).2.2) := by
  exact ⟨hs.isCompact hω, hs.exists_translated_horizontal_strip,
    hs.exists_translated_vertical_strip, fun _ ht ↦ hs.exists_translated_rotated_hallway ht,
    hs.horizontal_width_le, hs.normal_width_le, fun hstd ↦ hstd.subset_strips⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Compactness
-/

public section

noncomputable section

open Set MeasureTheory
open scoped unitInterval

namespace MovingSofa

private theorem abs_le_of_affine_coordinate {a b c x y z : ℝ}
    (ha : a ≠ 0) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (heq : z = a * x + b * y + c) :
    |x| ≤ (1 + |b| + |c|) / |a| := by
  have hmul : |a| * |x| ≤ 1 + |b| + |c| := by
    calc
      |a| * |x| = |z - (b * y + c)| := by rw [← abs_mul]; congr 1; linarith
      _ ≤ |z| + |b * y + c| := abs_sub _ _
      _ ≤ 1 + (|b| * |y| + |c|) := by
        grw [hz, abs_add_le, abs_mul]
      _ ≤ 1 + |b| + |c| := by nlinarith [abs_nonneg b]
  exact (le_div_iff₀ (abs_pos.mpr ha)).mpr (by nlinarith)

private theorem norm_le_of_coordinate_bounds {p : Point} {C : ℝ}
    (hC : 0 ≤ C) (hx : |p 0| ≤ C) (hy : |p 1| ≤ 1) : ‖p‖ ≤ C + 1 := by
  have hn : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p
  have hx2 := sq_le_sq₀ (abs_nonneg (p 0)) hC |>.mpr hx
  have hy2 := sq_le_sq₀ (abs_nonneg (p 1)) (by positivity : (0 : ℝ) ≤ 1) |>.mpr hy
  rw [sq_abs] at hx2 hy2
  nlinarith [norm_nonneg p]

private theorem affineIsometry_coordinate (e : Point ≃ᵃⁱ[ℝ] Point) (p : Point) (i : Fin 2) :
    e p i = (e.linearIsometryEquiv !₂[1, 0]) i * p 0 +
      (e.linearIsometryEquiv !₂[0, 1]) i * p 1 + e 0 i := by
  have hp : p = p 0 • !₂[1, 0] + p 1 • !₂[0, 1] := by
    ext j
    fin_cases j <;> simp
  have he := e.map_vadd (0 : Point) p
  change e (p + 0) = e.linearIsometryEquiv p + e 0 at he
  rw [add_zero] at he
  rw [he, hp, map_add, map_smul, map_smul]
  simp [mul_comm]

private theorem isBounded_affine_strip (e : Point ≃ᵃⁱ[ℝ] Point) (i : Fin 2)
    (hi : (e.linearIsometryEquiv !₂[1, 0]) i ≠ 0) :
    Bornology.IsBounded {p : Point | |p 1| ≤ 1 ∧ |e p i| ≤ 1} := by
  let C := (1 + |(e.linearIsometryEquiv !₂[0, 1]) i| + |e 0 i|) /
    |(e.linearIsometryEquiv !₂[1, 0]) i|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C + 1, fun p hp ↦ ?_⟩
  apply norm_le_of_coordinate_bounds hC _ hp.1
  exact abs_le_of_affine_coordinate hi hp.1 hp.2 (affineIsometry_coordinate e p i)

private theorem abs_snd_le_one_of_mem_horizontal {p : Point}
    (hp : p ∈ horizontalHallway) : |p 1| ≤ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hp
  simpa using
    (abs_le.mpr ⟨by linarith [hxy.2.1], hxy.2.2⟩ : |y| ≤ 1)

private theorem abs_fst_le_one_of_mem_vertical {p : Point}
    (hp : p ∈ verticalHallway) : |p 0| ≤ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hp
  simpa using
    (abs_le.mpr ⟨by linarith [hxy.1], hxy.2.1⟩ : |x| ≤ 1)

private theorem isBounded_of_mixed_direction (s : Set Point)
    (m : I → Point ≃ᵃⁱ[ℝ] Point) (h : IsMovingSofa s m) (t : I)
    (h0 : ((m t).linearIsometryEquiv !₂[1, 0]) 0 ≠ 0)
    (h1 : ((m t).linearIsometryEquiv !₂[1, 0]) 1 ≠ 0) : Bornology.IsBounded s := by
  apply ((isBounded_affine_strip (m t) 0 h0).union
    (isBounded_affine_strip (m t) 1 h1)).subset
  intro p hp
  have hy := abs_snd_le_one_of_mem_horizontal (h.initial hp)
  rcases h.subset_hallway t ⟨p, hp, rfl⟩ with hhor | hvert
  · exact Or.inr ⟨hy, abs_snd_le_one_of_mem_horizontal hhor⟩
  · exact Or.inl ⟨hy, abs_fst_le_one_of_mem_vertical hvert⟩

/-- A set admitting a canonical hallway motion is bounded. -/
theorem IsMovingSofa.isBounded {s : Set Point}
    {m : I → Point ≃ᵃⁱ[ℝ] Point} (h : IsMovingSofa s m) : Bornology.IsBounded s := by
  let d : I → Point := fun t ↦ (m t).linearIsometryEquiv !₂[1, 0]
  have hd : Continuous d := by
    have he (t : I) : d t = m t !₂[1, 0] - m t 0 := by
      have he := (m t).map_vadd (0 : Point) !₂[1, 0]
      change m t (!₂[1, 0] + 0) = d t + m t 0 at he
      rw [add_zero] at he
      exact eq_sub_iff_add_eq.mpr he.symm
    simp_rw [show d = (fun t ↦ m t !₂[1, 0] - m t 0) from funext he]
    have hm : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
      continuous_induced_dom.comp h.continuous
    exact (hm.eval_const _).sub (hm.eval_const _)
  have hnorm (t : I) : (d t 0) ^ 2 + (d t 1) ^ 2 = 1 := by
    have hn : ‖d t‖ = 1 := by
      dsimp [d]
      rw [(m t).linearIsometryEquiv.norm_map]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have hs := EuclideanSpace.real_norm_sq_eq (d t)
    simpa [hn, Fin.sum_univ_two] using hs.symm
  by_cases hmix : ∃ t, d t 0 ≠ 0 ∧ d t 1 ≠ 0
  · obtain ⟨t, h0, h1⟩ := hmix
    exact isBounded_of_mixed_direction s m h t h0 h1
  have hmem (t : I) : d t 0 ∈ ({-1, 0, 1} : Set ℝ) := by
    by_cases h0 : d t 0 = 0
    · simp [h0]
    have h1 : d t 1 = 0 := by
      by_contra hn
      exact hmix ⟨t, h0, hn⟩
    have hs : (d t 0) ^ 2 = (1 : ℝ) ^ 2 := by simpa [h1] using hnorm t
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hs) with he | he <;> simp [he]
  have hc : Continuous (fun t ↦ d t 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.comp hd
  have hconst (t : I) : d t 0 = d 0 0 :=
    isPreconnected_univ.constant_of_mapsTo
      (((finite_singleton (1 : ℝ)).insert 0).insert (-1)).isDiscrete
      hc.continuousOn (fun t _ ↦ hmem t) (mem_univ t) (mem_univ 0)
  have hd0 : d 0 0 = 1 := by simp only [d, h.zero]; rfl
  have hdir : ((m 1).linearIsometryEquiv !₂[1, 0]) 0 ≠ 0 := by
    change d 1 0 ≠ 0
    rw [hconst, hd0]
    norm_num
  apply (isBounded_affine_strip (m 1) 0 hdir).subset
  intro p hp
  exact ⟨abs_snd_le_one_of_mem_horizontal (h.initial hp),
    abs_fst_le_one_of_mem_vertical (h.final ⟨p, hp, rfl⟩)⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Rotation
-/

public section

noncomputable section

open Set
open scoped unitInterval

namespace MovingSofa

/-- The linear part of a continuous rigid motion varies continuously on each vector. -/
theorem continuous_motion_linear_apply (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (x : Point) :
    Continuous (fun t ↦ (m t).linearIsometryEquiv x) := by
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  have he (t : I) : (m t).linearIsometryEquiv x = m t x - m t 0 := by
    have he := (m t).map_vadd (0 : Point) x
    change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at he
    rw [add_zero] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  simp_rw [he]
  exact (hmc.eval_const x).sub (hmc.eval_const 0)

/-- The linear parts of an identity-starting continuous rigid motion have positive determinant. -/
theorem motion_linear_det_pos (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    0 < LinearMap.det (m t).linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  let L : I → Point →L[ℝ] Point := fun t ↦ (m t).linearIsometryEquiv.toContinuousLinearEquiv
  have hL : Continuous L := continuous_clm_apply.mpr
    (continuous_motion_linear_apply m hm)
  have hdet : Continuous (fun t ↦ (L t).det) := ContinuousLinearMap.continuous_det.comp hL
  have hne (u : I) : (L u).det ≠ 0 := (m u).linearIsometryEquiv.toLinearEquiv.isUnit_det'.ne_zero
  have hL0 : L 0 = ContinuousLinearMap.id ℝ Point := by
    ext x
    simp only [L, hzero]
    rfl
  have hzero' : (L 0).det = 1 := by rw [hL0]; simp [ContinuousLinearMap.det]
  change 0 < (L t).det
  by_contra hneg
  have hle : (L t).det ≤ 0 := le_of_not_gt hneg
  obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hdet ⟨hle, by rw [hzero']; norm_num⟩
  exact hne u hu

/-- Each placement of an identity-starting continuous rigid motion is a rotation and translation. -/
theorem exists_motion_rotation (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    ∃ θ : Real.Angle, ∀ x, m t x = rotationMap θ x + m t 0 := by
  obtain ⟨θ, hθ⟩ := EuclideanGeometry.o.exists_linearIsometryEquiv_eq_of_det_pos
    (motion_linear_det_pos m hm hzero t)
  refine ⟨θ, fun x ↦ ?_⟩
  have he := (m t).map_vadd (0 : Point) x
  change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at he
  simpa only [add_zero, hθ, rotationMap] using he

/-- Translation followed by a varying rotation depends continuously on both parameters. -/
theorem continuous_vaddConst_trans_rotation :
    Continuous (fun q : Real.Angle × Point ↦ ((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv)) := by
  rw [continuous_induced_rng]
  apply ContinuousAffineMap.continuous_rng
  · intro p
    change Continuous (fun q : Real.Angle × Point ↦
      (EuclideanGeometry.o.rotation q.1) (p + q.2))
    simp only [Orientation.rotation_apply]
    exact ((Real.Angle.continuous_cos.comp continuous_fst).smul
      (continuous_const.add continuous_snd)).add
      ((Real.Angle.continuous_sin.comp continuous_fst).smul
        (EuclideanGeometry.o.rightAngleRotation.continuous.comp
          (continuous_const.add continuous_snd)))
  · have heq : (fun q : Real.Angle × Point ↦
        (((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation
          q.1).toAffineIsometryEquiv)).toAffineIsometry.toContinuousAffineMap.contLinear) =
        (fun q : Real.Angle × Point ↦
          q.1.cos • ContinuousLinearMap.id ℝ Point +
          q.1.sin • EuclideanGeometry.o.rightAngleRotation.toContinuousLinearMap) := by
      funext q
      apply ContinuousLinearMap.ext
      intro p
      change (EuclideanGeometry.o.rotation q.1) p = _
      exact EuclideanGeometry.o.rotation_apply q.1 p
    change Continuous (fun q : Real.Angle × Point ↦
      (((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation
          q.1).toAffineIsometryEquiv)).toAffineIsometry.toContinuousAffineMap.contLinear)
    rw [heq]
    exact ((Real.Angle.continuous_cos.comp continuous_fst).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp continuous_fst).smul continuous_const)

/-- A continuously varying rotation about the origin followed by a continuously varying
translation is a continuous family of rigid motions. -/
theorem continuous_rotation_trans_vaddConst {X : Type*} [TopologicalSpace X]
    {θ : X → Real.Angle} {c : X → Point} (hθ : Continuous θ) (hc : Continuous c) :
    Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ (c x))) := by
  rw [continuous_induced_rng]
  apply ContinuousAffineMap.continuous_rng
  · intro p
    change Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)) p + c x)
    simp only [Orientation.rotation_apply]
    exact (((Real.Angle.continuous_cos.comp hθ).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp hθ).smul continuous_const)).add hc
  · have heq : (fun x ↦
        ((EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
          (AffineIsometryEquiv.vaddConst ℝ
            (c x))).toAffineIsometry.toContinuousAffineMap.contLinear) =
        (fun x ↦ (θ x).cos • ContinuousLinearMap.id ℝ Point +
            (θ x).sin • EuclideanGeometry.o.rightAngleRotation.toContinuousLinearMap) := by
      funext x
      apply ContinuousLinearMap.ext
      intro p
      change (EuclideanGeometry.o.rotation (θ x)) p = _
      exact EuclideanGeometry.o.rotation_apply (θ x) p
    change Continuous (fun x ↦
      ((EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
        (AffineIsometryEquiv.vaddConst ℝ
          (c x))).toAffineIsometry.toContinuousAffineMap.contLinear)
    rw [heq]
    exact ((Real.Angle.continuous_cos.comp hθ).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp hθ).smul continuous_const)

/-- Planar area is invariant under rotation about the origin, with no measurability
hypothesis on the set. -/
theorem area_image_rotationMap (α : Real.Angle) (S : Set Point) :
    ClassicalResults.area (rotationMap α '' S) = ClassicalResults.area S := by
  have himg : rotationMap α '' S = (EuclideanGeometry.o.rotation α).symm ⁻¹' S := by
    ext p
    simp only [rotationMap, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨_, h, (EuclideanGeometry.o.rotation α).apply_symm_apply p⟩
  change (MeasureTheory.volume (rotationMap α '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [himg]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving (EuclideanGeometry.o.rotation α).symm
    (E := Point) (F := Point)).measure_preimage_emb
    ((EuclideanGeometry.o.rotation α).symm.toHomeomorph.measurableEmbedding) S

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Angle Lift
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- An identity-starting continuous rigid motion has a normalized continuous real angle lift. -/
theorem exists_continuous_motion_angle_lift (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) :
    ∃ (α : I → ℝ) (p : I → Point), Continuous α ∧ Continuous p ∧
      α 0 = 0 ∧ p 0 = 0 ∧ ∀ t x, m t x = rotationMap (α t : Real.Angle) x + p t := by
  let e : Point := !₂[1, 0]
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun p : Point ↦ p 0) h
    norm_num [e] at this
  let θ : I → Real.Angle := fun t ↦ EuclideanGeometry.o.oangle e
    ((m t).linearIsometryEquiv e)
  have hθ : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : (m t).linearIsometryEquiv e ≠ 0 := by
      exact (m t).linearIsometryEquiv.map_ne_zero_iff.mpr he
    have ha : ContinuousAt (fun z : Point × Point ↦ EuclideanGeometry.o.oangle z.1 z.2)
        (e, (m t).linearIsometryEquiv e) :=
      EuclideanGeometry.o.continuousAt_oangle he hne
    have hp : ContinuousAt (fun u : I ↦ (e, (m u).linearIsometryEquiv e)) t :=
      continuousAt_const.prodMk (continuous_motion_linear_apply m hm e).continuousAt
    exact ContinuousAt.comp (f := fun u : I ↦ (e, (m u).linearIsometryEquiv e))
      (x := t) ha hp
  have hθ0 : θ 0 = 0 := by
    have h0 : (m 0).linearIsometryEquiv e = e := by rw [hzero]; rfl
    simp [θ, h0]
  have hrot (t : I) : (m t).linearIsometryEquiv = EuclideanGeometry.o.rotation (θ t) := by
    obtain ⟨u, hu⟩ := EuclideanGeometry.o.exists_linearIsometryEquiv_eq_of_det_pos
      (motion_linear_det_pos m hm hzero t)
    have ht : θ t = u := by
      dsimp [θ]
      rw [hu, EuclideanGeometry.o.oangle_rotation_self_right he]
    rw [ht, hu]
  obtain ⟨α, hα, hα0, hαθ⟩ := Real.Angle.exists_continuous_lift_zero θ hθ hθ0
  have hp : Continuous (fun t ↦ m t (0 : Point)) := by
    have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
      continuous_induced_dom.comp hm
    exact hmc.eval_const 0
  refine ⟨α, fun t ↦ m t 0, hα, hp, hα0, ?_, ?_⟩
  · change m 0 0 = 0
    rw [hzero]
    rfl
  · intro t x
    have hx := (m t).map_vadd (0 : Point) x
    change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at hx
    simpa only [add_zero, hrot t, hαθ t, rotationMap] using hx

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Rotation Angle Calculation
-/

public section

noncomputable section

namespace MovingSofa

/-- The rotation-angle interval from `arccos(5/11)` up to, but excluding, `π/2`. -/
abbrev RotationCalculationAngle := Set.Ico (Real.arccos (5 / 11 : ℝ)) (Real.pi / 2)

/-- The piecewise lower cutoff on the auxiliary distance used in the rotation estimate. -/
def rotationCalculationMinimum (ω : RotationCalculationAngle) : ℝ :=
  if ω.val < Real.arctan (11 / 5 : ℝ) then 5 / 4 else 11 / 10

/-- Auxiliary radii and points determined by an admissible rotation angle and distance. -/
@[expose]
def rotationCalculationValues (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val)) :
    ℝ × ℝ × Point × Point :=
  let r := 1 - d.val * (Real.cos ω.val / Real.sin ω.val)
  let g := Real.sqrt (1 - r ^ 2)
  let o := (stripParallelogram ω.val).2.2
  (r, g, o - tangentVector 0 + d.val • normalVector 0, o - g • normalVector 0)

theorem rotationCalculation_convex (d : ℝ) (hd : 1 ≤ d) :
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2))
      (fun t ↦ (1 - d * (Real.cos t / Real.sin t)) ^ 2) ∧
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2))
      (fun t ↦ Real.cos t ^ 2) := by
  let D := Set.Icc (Real.pi / 4) (Real.pi / 2)
  have hsin (t : ℝ) (ht : t ∈ D) : Real.sin t ≠ 0 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < Real.pi / 4) ht.1
    have htpi : t < Real.pi := lt_of_le_of_lt ht.2 (by linarith)
    exact (Real.sin_pos_of_pos_of_lt_pi ht0 htpi).ne'
  have hfirst (t : ℝ) (ht : t ∈ D) : HasDerivAt
      (fun s ↦ (1 - d * (Real.cos s / Real.sin s)) ^ 2)
      (2 * d * (1 - d * (Real.cos t / Real.sin t)) / Real.sin t ^ 2) t := by
    have htrig : -(Real.sin t * Real.sin t) - Real.cos t * Real.cos t = -1 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    convert (((hasDerivAt_const t 1).sub
      ((hasDerivAt_const t d).mul ((Real.hasDerivAt_cos t).div
        (Real.hasDerivAt_sin t) (hsin t ht)))).pow 2) using 1
    all_goals simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply]
    all_goals norm_num
    all_goals simp only [htrig]
    all_goals field_simp [hsin t ht]
  have hsecond (t : ℝ) (ht : t ∈ D) : HasDerivAt
      (fun s ↦ 2 * d * (1 - d * (Real.cos s / Real.sin s)) / Real.sin s ^ 2)
      (2 * d / Real.sin t ^ 4 *
        (d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t)) t := by
    have hs := hsin t ht
    have htrig : -(Real.sin t * Real.sin t) - Real.cos t * Real.cos t = -1 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    convert (((hasDerivAt_const t (2 * d)).mul
      ((hasDerivAt_const t 1).sub
        ((hasDerivAt_const t d).mul ((Real.hasDerivAt_cos t).div
          (Real.hasDerivAt_sin t) hs)))).div
      ((Real.hasDerivAt_sin t).pow 2) (pow_ne_zero 2 hs)) using 1
    all_goals simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
    all_goals norm_num
    all_goals simp only [htrig]
    all_goals field_simp [hs]
    all_goals ring
  constructor
  · apply convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun t ↦ 2 * d * (1 - d * (Real.cos t / Real.sin t)) / Real.sin t ^ 2)
      (f'' := fun t ↦ 2 * d / Real.sin t ^ 4 *
        (d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t)) (convex_Icc _ _)
    · fun_prop
    · intro t ht
      exact (hfirst t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact (hsecond t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have hc : 2 * Real.sin t * Real.cos t ≤ 1 := by
        nlinarith [sq_nonneg (Real.sin t - Real.cos t), Real.sin_sq_add_cos_sq t]
      have : 0 ≤ d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t := by
        nlinarith [sq_nonneg (Real.cos t)]
      positivity
  · apply convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun t ↦ -2 * Real.sin t * Real.cos t)
      (f'' := fun t ↦ -2 * Real.cos (2 * t)) (convex_Icc _ _)
    · fun_prop
    · intro t ht
      convert ((Real.hasDerivAt_cos t).mul (Real.hasDerivAt_cos t)).hasDerivWithinAt using 1 <;>
        first | funext s; simp [Pi.mul_apply]; ring | ring
    · intro t ht
      convert (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).const_mul (-2))
        |>.hasDerivWithinAt using 1 <;>
          first | funext s; simp [Pi.mul_apply]; ring |
            rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq t]; ring
    · intro t ht
      have htD := interior_subset ht
      change t ∈ Set.Icc (Real.pi / 4) (Real.pi / 2) at htD
      have h1 : Real.pi / 2 ≤ 2 * t := by
        calc
          Real.pi / 2 = 2 * (Real.pi / 4) := by ring
          _ ≤ 2 * t := mul_le_mul_of_nonneg_left htD.1 (by norm_num)
      have h2 : 2 * t ≤ Real.pi + Real.pi / 2 := by
        calc
          2 * t ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left htD.2 (by norm_num)
          _ ≤ Real.pi + Real.pi / 2 := by linarith [Real.pi_pos]
      exact mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2)

private def rotationBound (d t : ℝ) : ℝ :=
  (1 - d * (Real.cos t / Real.sin t)) ^ 2 + 4 * Real.cos t ^ 2

private theorem rotationBound_convex (d : ℝ) (hd : 1 ≤ d) :
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2)) (rotationBound d) := by
  obtain ⟨h₁, h₂⟩ := rotationCalculation_convex d hd
  exact h₁.add (h₂.smul (by norm_num : (0 : ℝ) ≤ 4))

private theorem rotationBound_arccos :
    rotationBound (5 / 4) (Real.arccos (5 / 11)) < 1 := by
  have hs : Real.sin (Real.arccos (5 / 11)) = Real.sqrt 96 / 11 := by
    rw [Real.sin_arccos]
    norm_num
  have hsq : Real.sqrt 96 ^ 2 = 96 := Real.sq_sqrt (by norm_num)
  have hlo : 97 / 10 < Real.sqrt 96 := by
    nlinarith [Real.sqrt_nonneg 96]
  have hhi : Real.sqrt 96 < 49 / 5 := by
    nlinarith [Real.sqrt_nonneg 96]
  unfold rotationBound
  rw [Real.cos_arccos (by norm_num) (by norm_num), hs]
  have hpos : 0 < Real.sqrt 96 := by positivity
  field_simp
  nlinarith

private theorem rotationBound_arctan_left :
    rotationBound (5 / 4) (Real.arctan (11 / 5)) < 1 := by
  unfold rotationBound
  rw [Real.cos_arctan, Real.sin_arctan]
  norm_num
  have hs : Real.sqrt (146 : ℝ) ^ 2 = 146 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (146 : ℝ) := by positivity
  field_simp
  nlinarith

private theorem rotationBound_arctan_right :
    rotationBound (11 / 10) (Real.arctan (11 / 5)) < 1 := by
  unfold rotationBound
  rw [Real.cos_arctan, Real.sin_arctan]
  norm_num
  have hs : Real.sqrt (146 : ℝ) ^ 2 = 146 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (146 : ℝ) := by positivity
  field_simp
  nlinarith

private theorem rotationBound_pi_div_two (d : ℝ) : rotationBound d (Real.pi / 2) = 1 := by
  simp [rotationBound]

/-- The three landmark angles of the rotation calculation are strictly ordered:
`π / 4 < arccos (5 / 11) < arctan (11 / 5) < π / 2`. -/
theorem rotationCalculation_angle_bounds :
    Real.pi / 4 < Real.arccos (5 / 11 : ℝ) ∧
    Real.arccos (5 / 11 : ℝ) < Real.arctan (11 / 5 : ℝ) ∧
    Real.arctan (11 / 5 : ℝ) < Real.pi / 2 := by
  have ha : Real.arccos (5 / 11 : ℝ) = Real.arctan (Real.sqrt 96 / 5) := by
    rw [Real.arccos_eq_arctan (by norm_num)]
    norm_num
    ring
  have hs : Real.sqrt 96 ^ 2 = 96 := Real.sq_sqrt (by norm_num)
  have hpos := Real.sqrt_nonneg 96
  refine ⟨?_, ?_, Real.arctan_lt_pi_div_two _⟩
  · rw [ha, ← Real.arctan_one]
    apply Real.arctan_strictMono
    nlinarith
  · rw [ha]
    apply Real.arctan_strictMono
    nlinarith

private theorem rotationBound_lt_one (ω : RotationCalculationAngle) :
    rotationBound (rotationCalculationMinimum ω) ω.val < 1 := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hdom₁ : Set.Icc (Real.arccos (5 / 11 : ℝ)) (Real.arctan (11 / 5 : ℝ)) ⊆
      Set.Icc (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    exact ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hdom₂ : Set.Icc (Real.arctan (11 / 5 : ℝ)) (Real.pi / 2) ⊆
      Set.Icc (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    exact ⟨(ha.le.trans hab.le).trans ht.1, ht.2⟩
  unfold rotationCalculationMinimum
  split_ifs with h
  · exact ConvexOn.lt_on_Ico_of_lt_of_le
      ((rotationBound_convex (5 / 4) (by norm_num)).subset hdom₁ (convex_Icc _ _))
      rotationBound_arccos rotationBound_arctan_left.le ω.property.1 h
  · exact ConvexOn.lt_on_Ico_of_lt_of_le
      ((rotationBound_convex (11 / 10) (by norm_num)).subset hdom₂ (convex_Icc _ _))
      rotationBound_arctan_right (rotationBound_pi_div_two _).le (le_of_not_gt h) ω.property.2

private theorem rotationCalculation_sin_bound (ω : RotationCalculationAngle) :
    1 < rotationCalculationMinimum ω * Real.sin ω.val := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hsinmono := Real.strictMonoOn_sin.monotoneOn
  unfold rotationCalculationMinimum
  split_ifs with h
  · have hs := hsinmono
      (show Real.arccos (5 / 11 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
      (show ω.val ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [ω.property.1, ω.property.2, Real.pi_pos]) ω.property.1
    rw [Real.sin_arccos] at hs
    norm_num at hs
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 96)
    have hp := Real.sqrt_nonneg 96
    have : 44 / 5 < Real.sqrt 96 := by nlinarith
    nlinarith
  · have hs := hsinmono
      (show Real.arctan (11 / 5 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
      (show ω.val ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [ω.property.1, ω.property.2, Real.pi_pos]) (le_of_not_gt h)
    rw [Real.sin_arctan] at hs
    norm_num at hs
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 146)
    have hp : 0 < Real.sqrt 146 := by positivity
    have hupper : Real.sqrt 146 < 121 / 10 := by nlinarith
    have hbase : 10 / 11 < 11 / Real.sqrt 146 := (lt_div_iff₀ hp).2 (by nlinarith)
    nlinarith

private theorem rotationCalculation_g_bound (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val))
    (hr : 0 ≤ (rotationCalculationValues ω d).1) :
    2 * Real.cos ω.val < (rotationCalculationValues ω d).2.1 := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hw0 : 0 < ω.val := by linarith [ω.property.1, Real.pi_pos]
  have hsin : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hcos : 0 < Real.cos ω.val := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    ω.property.2⟩
  have hcot : 0 ≤ Real.cos ω.val / Real.sin ω.val := le_of_lt (div_pos hcos hsin)
  have hmin : 0 ≤ rotationCalculationMinimum ω := by
    unfold rotationCalculationMinimum
    split_ifs <;> norm_num
  have hdd := mul_le_mul_of_nonneg_right d.property.1 hcot
  change 0 ≤ 1 - d.val * (Real.cos ω.val / Real.sin ω.val) at hr
  have hf := rotationBound_lt_one ω
  unfold rotationBound at hf
  have hrle : 1 - d.val * (Real.cos ω.val / Real.sin ω.val) ≤
      1 - rotationCalculationMinimum ω * (Real.cos ω.val / Real.sin ω.val) := by linarith
  have hr0 : 0 ≤ 1 - rotationCalculationMinimum ω * (Real.cos ω.val / Real.sin ω.val) := by linarith
  have hsquares := sq_le_sq₀ hr hr0 |>.2 hrle
  have hrad : 0 ≤ 1 - (1 - d.val * (Real.cos ω.val / Real.sin ω.val)) ^ 2 := by
    nlinarith [sq_nonneg (Real.cos ω.val)]
  have hsqrt := Real.sq_sqrt hrad
  have hnonneg := Real.sqrt_nonneg (1 - (1 - d.val * (Real.cos ω.val / Real.sin ω.val)) ^ 2)
  change 2 * Real.cos ω.val < Real.sqrt _
  nlinarith

theorem rotationCalculation_inequalities (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val))
    (hr : 0 ≤ (rotationCalculationValues ω d).1) :
    1 < inner ℝ
      ((rotationCalculationValues ω d).2.2.1 -
        ((stripParallelogram ω.val).2.2 - tangentVector 0))
      (normalVector ((Real.pi / 2 - ω.val : ℝ) : Real.Angle)) ∧
    1 < inner ℝ
      ((rotationCalculationValues ω d).2.2.2 -
        ((stripParallelogram ω.val).2.2 - normalVector (ω.val : Real.Angle)))
      (tangentVector ((Real.pi / 2 - ω.val : ℝ) : Real.Angle)) := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hw0 : 0 < ω.val := by linarith [ω.property.1, Real.pi_pos]
  have hsin : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hcos : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hg := rotationCalculation_g_bound ω d hr
  have hd := mul_le_mul_of_nonneg_right d.property.1 hsin.le
  have hds := rotationCalculation_sin_bound ω
  constructor
  · simp [rotationCalculationValues, inner_smul_left,
      normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
    linarith
  · have hvec : (rotationCalculationValues ω d).2.2.2 -
        ((stripParallelogram ω.val).2.2 - normalVector (ω.val : Real.Angle)) =
        normalVector (ω.val : Real.Angle) - (rotationCalculationValues ω d).2.1 • normalVector 0
          := by
      simp only [rotationCalculationValues]
      abel
    rw [hvec]
    simp only [inner_sub_left, inner_smul_left]
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
    have hm := mul_lt_mul_of_pos_right hg hcos
    nlinarith [Real.sin_sq_add_cos_sq ω.val]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Supporting Hallways
-/

public section

noncomputable section
open Set
open scoped unitInterval
namespace MovingSofa

/-- The supporting placement regarded as an affine isometry equivalence. -/
def supportingPlacementEquiv (s : Set Point) (t : Real.Angle) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (EuclideanGeometry.o.rotation t).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ
      ((supportValue s t - 1) • normalVector t +
       (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t))

theorem supportingPlacementEquiv_apply (s : Set Point) (t : Real.Angle) (p : Point) :
    supportingPlacementEquiv s t p = supportingPlacement s t p := by
  simp [supportingPlacementEquiv, supportingPlacement, rotationMap, add_assoc]

private def supportCorner (s : Set Point) (t : Real.Angle) : Point :=
  (supportValue s t - 1) • normalVector t +
    (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t

private theorem continuous_supportCorner_real (s : Set Point)
    (hs : s.Nonempty) (hc : IsCompact s) :
    Continuous (fun t : ℝ ↦ supportCorner s (t : Real.Angle)) := by
  have hh := (compactSet_support_continuity s s hs hc hs hc).2.2.1
  have hn := continuous_normalVector_real
  have hv : Continuous (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
    have h := hn.comp (continuous_id.add (continuous_const (y := Real.pi / 2)))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, Real.Angle.coe_add,
      normalVector_add_pi_div_two] using h
  exact (((hh.comp Real.Angle.continuous_coe).sub continuous_const).smul hn).add
    (((hh.comp (Real.Angle.continuous_coe.add continuous_const)).sub continuous_const).smul hv)

private theorem supportingPlacementEquiv_symm_apply (s : Set Point) (t : Real.Angle)
    (p : Point) :
    (supportingPlacementEquiv s t).symm p =
      ((AffineIsometryEquiv.vaddConst ℝ (-supportCorner s t)).trans
        (EuclideanGeometry.o.rotation (-t)).toAffineIsometryEquiv) p := by
  change (EuclideanGeometry.o.rotation t).symm (p - supportCorner s t) =
    (EuclideanGeometry.o.rotation (-t)) (p + -supportCorner s t)
  simp only [Orientation.rotation_symm_apply, Orientation.rotation_apply,
    Real.Angle.cos_neg, Real.Angle.sin_neg, neg_smul, sub_eq_add_neg]

private theorem continuous_inverse_supportingPlacement (s : Set Point)
    (hs : s.Nonempty) (hc : IsCompact s) :
    Continuous (fun t : ℝ ↦ (supportingPlacementEquiv s (t : Real.Angle)).symm) := by
  have h := continuous_vaddConst_trans_rotation.comp
    (Real.Angle.continuous_coe.neg.prodMk (continuous_supportCorner_real s hs hc).neg)
  apply h.congr
  intro t
  apply AffineIsometryEquiv.ext
  intro p
  exact (supportingPlacementEquiv_symm_apply s (t : Real.Angle) p).symm

private theorem inverse_supportingPlacement_coordinates (s : Set Point)
    (t : Real.Angle) (p : Point) :
    ((supportingPlacementEquiv s t).symm p) 0 =
      inner ℝ p (normalVector t) - supportValue s t + 1 ∧
    ((supportingPlacementEquiv s t).symm p) 1 =
      inner ℝ p (tangentVector t) -
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) + 1 := by
  have hn := inner_supportingPlacement_normalVector s t ((supportingPlacementEquiv s t).symm p)
  have ht := inner_supportingPlacement_tangentVector s t ((supportingPlacementEquiv s t).symm p)
  rw [← supportingPlacementEquiv_apply, AffineIsometryEquiv.apply_symm_apply] at hn ht
  constructor <;> linarith

private theorem inverse_supportingPlacement_mem_hallway (s : Set Point)
    (t : Real.Angle) {p : Point} (hp : p ∈ supportingHallway s t) :
    (supportingPlacementEquiv s t).symm p ∈ hallway := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← supportingPlacementEquiv_apply, AffineIsometryEquiv.symm_apply_apply]
  exact hq

private theorem hallway_coordinates_le {p : Point} (hp : p ∈ hallway) :
    p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  rcases hp with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
  · exact ⟨h.1, h.2.2⟩
  · exact ⟨h.2.1, h.2.2⟩

/-- A closed connected subset of the supporting-hallway intersection inherits its
clockwise hallway motion from the reference compact set. -/
theorem hasRotationAngle_of_subset_supportingHallways (s S : Set Point) (ω : ℝ)
    (hsne : s.Nonempty) (hscompact : IsCompact s) (hω : 0 ≤ ω)
    (hsω : supportValue s (ω : Real.Angle) = 1)
    (hsπ : supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1)
    (hSconn : IsConnected S) (hSclosed : IsClosed S)
    (hSsub : S ⊆ monotonization s ω) : HasRotationAngle S ω := by
  let m : I → Point ≃ᵃⁱ[ℝ] Point := fun r ↦
    (supportingPlacementEquiv s ((ω * (r : ℝ) : ℝ) : Real.Angle)).symm
  have hθ (r : I) : ω * (r : ℝ) ∈ Icc (0 : ℝ) ω := by
    exact ⟨mul_nonneg hω r.2.1,
      (mul_le_mul_of_nonneg_left r.2.2 hω).trans_eq (mul_one ω)⟩
  have hall (r : I) : m r '' S ⊆ hallway := by
    rintro p ⟨q, hq, rfl⟩
    apply inverse_supportingPlacement_mem_hallway
    exact mem_iInter.mp (mem_iInter.mp (hSsub hq).2 (ω * (r : ℝ))) (hθ r)
  have hrot (r : I) (p : Point) :
      m r p = rotationMap ((-ω * (r : ℝ) : ℝ) : Real.Angle) p + m r 0 := by
    dsimp [m]
    rw [supportingPlacementEquiv_symm_apply, supportingPlacementEquiv_symm_apply]
    change rotationMap (-((ω * (r : ℝ) : ℝ) : Real.Angle))
      (p + -supportCorner s _) = _
    rw [show ((-ω * (r : ℝ) : ℝ) : Real.Angle) =
      -((ω * (r : ℝ) : ℝ) : Real.Angle) by rw [neg_mul, Real.Angle.coe_neg]]
    simp [rotationMap, map_add]
  refine ⟨m, ?_, (fun r ↦ -ω * (r : ℝ)), by fun_prop, by simp, by simp, hrot⟩
  refine ⟨hSconn,
    hSclosed,
    (continuous_inverse_supportingPlacement s hsne hscompact).comp
      (continuous_const.mul continuous_subtype_val), ?_, ?_, ?_, hall, ?_⟩
  · refine ⟨-supportCorner s 0, ?_⟩
    intro p
    simp [m, supportingPlacementEquiv_symm_apply,
      Orientation.rotation_zero]
  · intro r
    exact ⟨((-ω * (r : ℝ) : ℝ) : Real.Angle), hrot r⟩
  · rintro p ⟨q, hq, rfl⟩
    apply mem_horizontalHallway_of_coordinates
    · exact (hallway_coordinates_le (hall 0 ⟨q, hq, rfl⟩)).1
    · have hc := (inverse_supportingPlacement_coordinates s 0 q).2
      have hqP := (mem_stripParallelogram_iff ω q).mp (hSsub hq).1
      have hy : (m 0 q) 1 = q 1 := by
        simpa [m, hsπ, tangentVector, frame, PiLp.inner_apply,
          Fin.sum_univ_two] using hc
      rw [hy]
      exact hqP.1
  · rintro p ⟨q, hq, rfl⟩
    apply mem_verticalHallway_of_coordinates
    · have hc := (inverse_supportingPlacement_coordinates s (ω : Real.Angle) q).1
      have hqP := (mem_stripParallelogram_iff ω q).mp (hSsub hq).1
      have hx : (m 1 q) 0 = inner ℝ q (normalVector (ω : Real.Angle)) := by
        simpa [m, hsω] using hc
      rw [hx]
      exact hqP.2
    · exact (hallway_coordinates_le (hall 1 ⟨q, hq, rfl⟩)).2

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Translation
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private def translatedMotion (v : Point) (m : I → Point ≃ᵃⁱ[ℝ] Point) (t : I) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (AffineIsometryEquiv.vaddConst ℝ (-v)).trans (m t)

private theorem continuous_translatedMotion (v : Point)
    (m : I → Point ≃ᵃⁱ[ℝ] Point) (hm : Continuous m) :
    Continuous (translatedMotion v m) := by
  rw [continuous_induced_rng]
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  apply (ContinuousAffineMap.continuous_comp_right
    (AffineIsometryEquiv.vaddConst ℝ (-v)).toAffineIsometry.toContinuousAffineMap).comp
      hmc |>.congr
  intro t
  rfl

/-- Translating a sofa preserves each admitted rotation angle. -/
theorem hasRotationAngle_image_add (s : Set Point) (v : Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) :
    HasRotationAngle ((fun p ↦ p + v) '' s) ω := by
  obtain ⟨m, hm, α, hα, hα0, hα1, hmotion⟩ := hs
  refine ⟨translatedMotion v m, ?_, α, hα, hα0, hα1, ?_⟩
  · obtain ⟨hconn, hclosed, hcont, ⟨q, hq⟩, hrot, hini, hall, hfinal⟩ := hm
    refine ⟨hconn.image _ (by fun_prop), ?_, continuous_translatedMotion v m hcont,
      ⟨q - v, ?_⟩, ?_, ?_, ?_, ?_⟩
    · change IsClosed ((AffineIsometryEquiv.vaddConst ℝ v) '' s)
      exact (AffineIsometryEquiv.vaddConst ℝ v).toHomeomorph.isClosedMap s hclosed
    · intro p
      change m 0 (p - v) = p + (q - v)
      rw [hq]
      abel
    · intro t
      obtain ⟨a, ha⟩ := hrot t
      refine ⟨a, fun p ↦ ?_⟩
      change m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p) =
        rotationMap a p + m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)
      rw [ha ((AffineIsometryEquiv.vaddConst ℝ (-v)) p),
        ha ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)]
      have hvp : (AffineIsometryEquiv.vaddConst ℝ (-v)) p = p - v := by rfl
      have hv0 : (AffineIsometryEquiv.vaddConst ℝ (-v)) 0 = -v := by simp
      rw [hvp, hv0]
      simp only [rotationMap, map_sub, map_neg]
      abel
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hini ⟨y, hy, by simp [translatedMotion]⟩
    · intro t
      rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact hall t ⟨y, hy, by simp [translatedMotion]⟩
    · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact hfinal ⟨y, hy, by simp [translatedMotion]⟩
  · intro t p
    change m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p) =
      rotationMap (α t : Real.Angle) p +
        m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)
    rw [hmotion t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p),
      hmotion t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)]
    have hvp : (AffineIsometryEquiv.vaddConst ℝ (-v)) p = p - v := by rfl
    have hv0 : (AffineIsometryEquiv.vaddConst ℝ (-v)) 0 = -v := by simp
    rw [hvp, hv0]
    simp only [rotationMap, map_sub, map_neg]
    abel

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Standard Position
-/

public section

noncomputable section

namespace MovingSofa

theorem exists_standardPosition_translation (s : Set Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) :
    (∃ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω) ∧
    (∀ v w : Point,
      IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      IsStandardPosition ((fun p ↦ p + w) '' s) ω →
      (ω < Real.pi / 2 → v = w) ∧ (ω = Real.pi / 2 → v 1 = w 1)) ∧
    (∀ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      ω = Real.pi / 2 → ∀ a : ℝ,
        IsStandardPosition ((fun p ↦ p + (v + a • normalVector 0)) '' s) ω) ∧
    (∀ v : Point, IsStandardPosition ((fun p ↦ p + v) '' s) ω →
      (fun p ↦ p + v) '' s ⊆ (stripParallelogram ω).1) := by
  have hc : IsCompact s := hs.isCompact hω
  have hne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs
    exact hm.1.nonempty
  have hadd (v : Point) (t : Real.Angle) :
      supportValue ((fun p ↦ p + v) '' s) t =
        supportValue s t + inner ℝ v (normalVector t) :=
    supportValue_image_add_of_isCompact hc hne v t
  have hcos (hlt : ω < Real.pi / 2) : Real.cos ω ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hω.1, Real.pi_pos], hlt⟩).ne'
  constructor
  · rcases lt_or_eq_of_le hω.2 with hlt | rfl
    · let v : Point := !₂[
          (1 - supportValue s (ω : Real.Angle) -
            (1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)) * Real.sin ω) /
              Real.cos ω,
          1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)]
      refine ⟨v, hc.image (by fun_prop), hasRotationAngle_image_add s v ω hs,
        hω.1, hω.2, ?_, ?_⟩
      · rw [hadd]
        simp only [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
          Real.Angle.cos_coe, Real.Angle.sin_coe, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        field_simp [hcos hlt]
        ring
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    · let v : Point := !₂[0,
          1 - supportValue s ((Real.pi / 2 : ℝ) : Real.Angle)]
      refine ⟨v, hc.image (by fun_prop),
        hasRotationAngle_image_add s v (Real.pi / 2) hs, hω.1, hω.2, ?_, ?_⟩
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      · rw [hadd]
        simp [v, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  · constructor
    · intro v w hv hw
      have hvω := hv.2.2.2.2.1
      have hvπ := hv.2.2.2.2.2
      have hwω := hw.2.2.2.2.1
      have hwπ := hw.2.2.2.2.2
      rw [hadd] at hvω hvπ hwω hwπ
      constructor
      · intro hlt
        have hy : v 1 = w 1 := by
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ hwπ
          linarith
        apply PiLp.ext
        intro i
        fin_cases i
        · have hcω := hcos hlt
          change v 0 = w 0
          simp only [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
            RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hvω hwω
          rw [hy] at hvω
          apply mul_left_cancel₀ hcω
          linarith [hvω, hwω]
        · exact hy
      · intro _
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ hwπ
        linarith
    · constructor
      · intro v hv hωeq a
        subst ω
        have hvπ := hv.2.2.2.2.2
        rw [hadd] at hvπ
        refine ⟨hc.image (by fun_prop),
          hasRotationAngle_image_add s (v + a • normalVector 0) (Real.pi / 2) hs,
          hω.1, hω.2, ?_, ?_⟩
        · rw [hadd]
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ ⊢
          linarith
        · rw [hadd]
          simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hvπ ⊢
          linarith
      · intro v hv
        exact hv.subset_strips

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Bounds.WedgeContainment`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Bounds / Wedge Containment
-/

public section

noncomputable section

namespace MovingSofa

private theorem smul_mem_of_mem_of_le_of_le {K : ConvexBody Point} {v : Point}
    {l x r : ℝ} (hl : l • v ∈ (K : Set Point)) (hr : r • v ∈ (K : Set Point))
    (hlx : l ≤ x) (hxr : x ≤ r) : x • v ∈ (K : Set Point) := by
  by_cases hlr : l = r
  · have hx : x = l := by linarith
    simpa [hx] using hl
  · have hlrpos : 0 < r - l := sub_pos.mpr (lt_of_le_of_ne (hlx.trans hxr) hlr)
    have hratio : (x - l) / (r - l) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hlx) hlrpos.le
      · exact (div_le_one hlrpos).2 (by linarith)
    have hmem := K.convex.lineMap_mem hl hr hratio
    rw [AffineMap.lineMap_apply_module] at hmem
    have heq : (1 - (x - l) / (r - l)) • l • v +
        ((x - l) / (r - l)) • r • v = x • v := by
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      field_simp
      ring
    rw [heq] at hmem
    exact hmem

private theorem inner_lineMap (x y u : Point) (s : ℝ) :
    inner ℝ (AffineMap.lineMap x y s) u =
      inner ℝ x u + s * (inner ℝ y u - inner ℝ x u) := by
  rw [AffineMap.lineMap_apply_module, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  ring

private theorem mem_segment_lineMap_of_one_le (x y : Point) {s : ℝ} (hs : 1 ≤ s) :
    y ∈ segment ℝ x (AffineMap.lineMap x y s) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  rw [segment_eq_image_lineMap]
  refine ⟨1 / s, ⟨by positivity, (div_le_one hspos).2 hs⟩, ?_⟩
  ext i
  simp [AffineMap.lineMap_apply_module, one_div, hspos.ne']
  field_simp
  ring

private theorem exists_lineMap_fan_boundary (x y u v : Point)
    (hyu : 0 ≤ inner ℝ y u) (hyv : 0 ≤ inner ℝ y v)
    (hdu : inner ℝ (y - x) u < 0) (hdv : inner ℝ (y - x) v < 0) :
    ∃ s : ℝ, 1 ≤ s ∧
      0 ≤ inner ℝ (AffineMap.lineMap x y s) u ∧
      0 ≤ inner ℝ (AffineMap.lineMap x y s) v ∧
      (inner ℝ (AffineMap.lineMap x y s) u = 0 ∨
        inner ℝ (AffineMap.lineMap x y s) v = 0) := by
  let du := inner ℝ x u - inner ℝ y u
  let dv := inner ℝ x v - inner ℝ y v
  have hdu' : 0 < du := by
    rw [inner_sub_left] at hdu
    dsimp [du]
    linarith
  have hdv' : 0 < dv := by
    rw [inner_sub_left] at hdv
    dsimp [dv]
    linarith
  by_cases hratio : inner ℝ x u / du ≤ inner ℝ x v / dv
  · let s := inner ℝ x u / du
    have hs : 1 ≤ s := by
      apply (le_div_iff₀ hdu').2
      dsimp [du]
      linarith
    have hsdu : s * du = inner ℝ x u := by
      dsimp [s]
      field_simp
    have hsu : inner ℝ (AffineMap.lineMap x y s) u = 0 := by
      rw [inner_lineMap]
      have hdiff : inner ℝ y u - inner ℝ x u = -du := by simp [du]
      rw [hdiff, mul_neg, hsdu]
      ring
    have hsv : 0 ≤ inner ℝ (AffineMap.lineMap x y s) v := by
      have hmul : s * dv ≤ inner ℝ x v := (le_div_iff₀ hdv').mp hratio
      rw [inner_lineMap]
      dsimp [dv] at hmul
      linarith
    exact ⟨s, hs, hsu.ge, hsv, Or.inl hsu⟩
  · let s := inner ℝ x v / dv
    have hs : 1 ≤ s := by
      apply (le_div_iff₀ hdv').2
      dsimp [dv]
      linarith
    have hsdv : s * dv = inner ℝ x v := by
      dsimp [s]
      field_simp
    have hsv : inner ℝ (AffineMap.lineMap x y s) v = 0 := by
      rw [inner_lineMap]
      have hdiff : inner ℝ y v - inner ℝ x v = -dv := by simp [dv]
      rw [hdiff, mul_neg, hsdv]
      ring
    have hsu : 0 ≤ inner ℝ (AffineMap.lineMap x y s) u := by
      have hmul : s * du ≤ inner ℝ x u := (le_div_iff₀ hdu').mp (not_le.mp hratio).le
      rw [inner_lineMap]
      dsimp [du] at hmul
      linarith
    exact ⟨s, hs, hsu, hsv.ge, Or.inr hsv⟩

private theorem cap_fan_boundary_mem {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 ω) (p : Point)
    (hpy : 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    (hpω : 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)))
    (hpboundary : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∨
    inner ℝ p (normalVector (ω : Real.Angle)) = 0)
    (hpt : inner ℝ p (normalVector (t : Real.Angle)) <
      supportValue K.val (t : Real.Angle) - 1)
    (hptv : inner ℝ p (tangentVector (t : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) :
    p ∈ (K.val : Set Point) := by
  have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsinδ : 0 < Real.sin (ω - t) := Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩
  by_cases hωeq : ω = Real.pi / 2
  · have hpy0 : p 1 = 0 := by
      rcases hpboundary with hpy0 | hpω0
      · simpa [normalVector, frame, PiLp.inner_apply] using hpy0
      · rw [hωeq] at hpω0
        simpa [normalVector, frame, PiLp.inner_apply] using hpω0
    let l := -supportValue K.val (Real.pi : Real.Angle)
    let r := supportValue K.val (0 : Real.Angle)
    have hleft : l • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
      have h := supportValue_pi_smul_normalVector_mem_of_eq K hωeq
      convert h using 1
      ext i
      fin_cases i <;> simp [l, normalVector, frame]
    have hright : r • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
      exact supportValue_zero_smul_normalVector_mem K
    have hbounds := K.supportValue_upper_bounds ht
    have hsint_lt : Real.sin t < 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hcost]
    have hcost_lt : Real.cos t < 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hsint]
    have hpr : p 0 ≤ r := by
      have hpt' := hpt
      simp [normalVector, frame, PiLp.inner_apply, hpy0] at hpt'
      dsimp [r]
      nlinarith [hbounds.1]
    have hangle : ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
        (Real.pi : Real.Angle) := by
      congr 1
      rw [hωeq]
      ring
    have hbound₂ := hbounds.2
    rw [hangle] at hbound₂
    have hsinωt : Real.sin (ω - t) = Real.cos t := by
      rw [hωeq, Real.sin_pi_div_two_sub]
    have hcosωt : Real.cos (ω - t) = Real.sin t := by
      rw [hωeq, Real.cos_pi_div_two_sub]
    rw [hsinωt, hcosωt] at hbound₂
    have hlp : l ≤ p 0 := by
      have hptv' := hptv
      simp only [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        neg_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, hpy0, mul_zero, add_zero,
        Real.Angle.coe_add, neg_lt_sub_iff_lt_add] at hptv'
      dsimp [l]
      by_contra hp
      have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hp) hsint
      have hsum : Real.sin t * p 0 + supportValue K.val
          ((t + Real.pi / 2 : ℝ) : Real.Angle) < 1 := by
        calc
          _ < Real.sin t * (-supportValue K.val (Real.pi : Real.Angle)) +
              supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) :=
            by
              simpa [add_comm] using add_lt_add_right hmul
                (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle))
          _ ≤ Real.sin t * (-supportValue K.val (Real.pi : Real.Angle)) +
              (Real.cos t + Real.sin t * supportValue K.val (Real.pi : Real.Angle)) :=
            by
              simpa [add_comm] using
                add_le_add_left hbound₂
                  (Real.sin t * (-supportValue K.val (Real.pi : Real.Angle)))
          _ = Real.cos t := by ring
          _ < 1 := hcost_lt
      exact (not_lt_of_ge hsum.le) hptv'
    have hpEq : p = p 0 • normalVector (0 : Real.Angle) := by
      ext i
      fin_cases i <;> simp [normalVector, frame, hpy0]
    rw [hpEq]
    exact smul_mem_of_mem_of_le_of_le hleft hright hlp hpr
  · have hωlt : ω < Real.pi / 2 := K.property.2.1.lt_of_ne hωeq
    have hzero := zero_mem_cap_of_lt K hωlt
    have hbounds := K.supportValue_upper_bounds ht
    have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [K.property.1, Real.pi_pos], hωlt⟩
    rcases hpboundary with hpy0 | hpω0
    · have hpy0' : p 1 = 0 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hpy0
      have hpx0 : 0 ≤ p 0 := by
        have hpω' := hpω
        simp [normalVector, frame, PiLp.inner_apply, hpy0'] at hpω'
        by_contra hneg
        have := mul_neg_of_pos_of_neg hcosω (lt_of_not_ge hneg)
        linarith
      have hsint_lt : Real.sin t < 1 := by
        nlinarith [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hcost]
      have hpxr : p 0 ≤ supportValue K.val (0 : Real.Angle) := by
        have hpt' := hpt
        simp [normalVector, frame, PiLp.inner_apply, hpy0'] at hpt'
        nlinarith [hbounds.1]
      have hpEq : p = p 0 • normalVector (0 : Real.Angle) := by
        ext i
        fin_cases i <;> simp [normalVector, frame, hpy0']
      rw [hpEq]
      exact K.val.convex.smul_mem_of_nonneg_of_le hzero
        (supportValue_zero_smul_normalVector_mem K) hpx0 hpxr
    · let μ := inner ℝ p (tangentVector (ω : Real.Angle))
      have hpEq : μ • tangentVector (ω : Real.Angle) = p := by
        have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
          p (ω : Real.Angle)
        rw [hpω0, zero_smul, zero_add] at hframe
        exact hframe
      have hμ0 : 0 ≤ μ := by
        have hp1 := congrArg (fun x : Point ↦ x 1) hpEq
        change μ * Real.cos ω = p 1 at hp1
        have hpy' : 0 ≤ p 1 := by
          simpa [normalVector, frame, PiLp.inner_apply] using hpy
        rw [← hp1] at hpy'
        by_contra hneg
        have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hcosω
        linarith
      have hsinδ_lt : Real.sin (ω - t) < 1 := by
        nlinarith only [Real.sin_sq_add_cos_sq (ω - t), sq_pos_of_pos hcosδ]
      have htv : inner ℝ (tangentVector (ω : Real.Angle))
          (tangentVector (t : Real.Angle)) = Real.cos (ω - t) := by
        simp [tangentVector, frame, PiLp.inner_apply, Real.cos_sub]
        ring
      have hμL : μ ≤ supportValue K.val
          ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
        have hptv' := hptv
        rw [← hpEq, real_inner_smul_left, htv] at hptv'
        nlinarith [hbounds.2]
      rw [← hpEq]
      exact K.val.convex.smul_mem_of_nonneg_of_le hzero
        (supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt K hωlt) hμ0 hμL

theorem capWedge_subset_of_innerCorner_mem {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 ω)
    (hz : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner ∈
      (K.val : Set Point)) :
    capWedge K t ⊆ (K.val : Set Point) := by
  intro q hq
  rcases hq with ⟨hqFan, hqQuad⟩
  let z := (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
  change z ∈ (K.val : Set Point) at hz
  change q ∈ supportingPlacement (K.val : Set Point) (t : Real.Angle) ''
    hallwayParts.innerQuadrant at hqQuad
  obtain ⟨a, ha, hqa⟩ := hqQuad
  change a 0 < 0 ∧ a 1 < 0 at ha
  have hqQuad : inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val (t : Real.Angle) - 1 ∧
    inner ℝ q (tangentVector (t : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    constructor
    · rw [← hqa, inner_supportingPlacement_normalVector]
      linarith [ha.1]
    · rw [← hqa, inner_supportingPlacement_tangentVector]
      change a 1 + supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 < _
      linarith [ha.2]
  have hzu : inner ℝ z (normalVector (t : Real.Angle)) =
      supportValue K.val (t : Real.Angle) - 1 := by
    have h := inner_supportingPlacement_normalVector (K.val : Set Point)
      (t : Real.Angle) (0 : Point)
    simpa [z, rotatingHallwayParts, hallwayParts] using h
  have hzv : inner ℝ z (tangentVector (t : Real.Angle)) =
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    have h := inner_supportingPlacement_tangentVector (K.val : Set Point)
      (t : Real.Angle) (0 : Point)
    simpa [z, rotatingHallwayParts, hallwayParts] using h
  let d := q - z
  have hdu : inner ℝ d (normalVector (t : Real.Angle)) < 0 := by
    change inner ℝ (q - z) (normalVector (t : Real.Angle)) < 0
    rw [inner_sub_left]
    linarith [hqQuad.1, hzu]
  have hdv : inner ℝ d (tangentVector (t : Real.Angle)) < 0 := by
    change inner ℝ (q - z) (tangentVector (t : Real.Angle)) < 0
    rw [inner_sub_left]
    linarith [hqQuad.2, hzv]
  have hdφ (φ : ℝ) : inner ℝ d (normalVector (φ : Real.Angle)) =
      inner ℝ d (normalVector (t : Real.Angle)) * Real.cos (φ - t) +
        inner ℝ d (tangentVector (t : Real.Angle)) * Real.sin (φ - t) := by
    have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
      d (t : Real.Angle)
    nth_rewrite 1 [← hframe]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hcos : Real.cos (t - φ) = Real.cos (φ - t) := by
      rw [show t - φ = -(φ - t) by ring, Real.cos_neg]
    rw [inner_normalVector_normalVector, hcos]
    have hsin : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (φ : Real.Angle)) = Real.sin (φ - t) := by
      simp [normalVector, tangentVector, frame, PiLp.inner_apply, Real.sin_sub]
      ring
    rw [hsin]
  have hsint : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsinδ : 0 < Real.sin (ω - t) := Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩
  have hdy : inner ℝ d (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) < 0 := by
    rw [hdφ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    exact add_neg (mul_neg_of_neg_of_pos hdu hsint) (mul_neg_of_neg_of_pos hdv hcost)
  have hdω : inner ℝ d (normalVector (ω : Real.Angle)) < 0 := by
    rw [hdφ]
    exact add_neg (mul_neg_of_neg_of_pos hdu hcosδ)
      (mul_neg_of_neg_of_pos hdv hsinδ)
  have hqy : 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hqFan.2
  have hqω : 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) := hqFan.1
  obtain ⟨s, hs, hpy, hpω, hpboundary⟩ := exists_lineMap_fan_boundary z q
    (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) (normalVector (ω : Real.Angle))
    hqy hqω (by simpa only [d] using hdy) (by simpa only [d] using hdω)
  let p := AffineMap.lineMap z q s
  change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpy
  change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
  change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∨
    inner ℝ p (normalVector (ω : Real.Angle)) = 0 at hpboundary
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hpt : inner ℝ p (normalVector (t : Real.Angle)) <
      supportValue K.val (t : Real.Angle) - 1 := by
    rw [inner_lineMap]
    have hdiff : inner ℝ q (normalVector (t : Real.Angle)) -
        inner ℝ z (normalVector (t : Real.Angle)) =
        inner ℝ d (normalVector (t : Real.Angle)) := by
      change _ = inner ℝ (q - z) (normalVector (t : Real.Angle))
      rw [inner_sub_left]
    rw [hdiff, hzu]
    have := mul_neg_of_pos_of_neg hspos hdu
    linarith
  have hptv : inner ℝ p (tangentVector (t : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    have hpinner := inner_lineMap z q (tangentVector (t : Real.Angle)) s
    change inner ℝ p (tangentVector (t : Real.Angle)) = _ at hpinner
    rw [hpinner]
    have hdiff : inner ℝ q (tangentVector (t : Real.Angle)) -
        inner ℝ z (tangentVector (t : Real.Angle)) =
        inner ℝ d (tangentVector (t : Real.Angle)) := by
      change _ = inner ℝ (q - z) (tangentVector (t : Real.Angle))
      rw [inner_sub_left]
    rw [hdiff, hzv]
    have := mul_neg_of_pos_of_neg hspos hdv
    linarith
  have hpFan : p ∈ capFan ω := ⟨hpω, hpy⟩
  have hqp : q ∈ segment ℝ z p := mem_segment_lineMap_of_one_le z q hs
  have hpK := cap_fan_boundary_mem K t ht p hpy hpω hpboundary hpt hptv
  exact K.val.convex.segment_subset hz hpK hqp

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Cap.Balanced`.
* `Cap.Clipped.Estimates`.
* `Cap.Clipped`.
* `Cap.Densities`.
* `Cap.UpperBoundary`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Balanced
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The polygonal cap area minus the area of its polygonal niche. -/
@[expose]
def polygonAreaFunctional (Θ : AngleSet) (K : CapSpace Θ.angle) : ℝ :=
  ClassicalResults.area (angleCap Θ K) - ClassicalResults.area (polygonNiche Θ K)

/-- A cap containing the distinguished fan point maximizes the polygonal area functional. -/
@[expose]
def IsMaximumPolygonCap (Θ : AngleSet) (K : PolygonCapSpace Θ) : Prop :=
  (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) ∧
    ∀ L : PolygonCapSpace Θ, polygonAreaFunctional Θ L.val ≤ polygonAreaFunctional Θ K.val

/-- The cap is a Hausdorff limit of polygonal maxima on increasingly fine dyadic meshes. -/
@[expose]
def IsBalancedMaximumCap {ω : ℝ} (K : CapSpace ω) : Prop :=
  ∃ (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i), StrictMono n ∧
    (∀ i, ∃ k : ℕ, n i = 2 ^ k) ∧
    ∃ P : ∀ i, PolygonCapSpace (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)),
      (∀ i, IsMaximumPolygonCap _ (P i)) ∧
      Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point) (K.val : Set Point))
        atTop (𝓝 0)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Clipped / Estimates
-/

public section

noncomputable section

namespace MovingSofa

private theorem clippedArea_bound_low {u t : ℝ}
    (ht : 39 / 20 < t) (ht' : t ≤ 11 / 5) (hu : u < 121 / 50) :
    u - (t - 5 / 4) ^ 2 / t < 11 / 5 := by
  have ht0 : 0 < t := by linarith
  have hsq : 49 / 100 < (t - 5 / 4) ^ 2 := by nlinarith
  have hquot : 49 / 220 < (t - 5 / 4) ^ 2 / t := by
    apply (lt_div_iff₀ ht0).2
    nlinarith
  linarith

private theorem clippedArea_bound {C S : ℝ} (hC : 0 < C) (hS : 0 < S)
    (hcircle : S ^ 2 + C ^ 2 = 1) (hC' : C ≤ 5 / 11) :
    let d : ℝ := if S / C < 11 / 5 then 5 / 4 else 11 / 10
    1 / C - (S / C - d) ^ 2 * (C / S) < 11 / 5 := by
  dsimp
  split_ifs with h
  · have ht : 0 < S / C := div_pos hS hC
    have hid : (1 / C) ^ 2 = 1 + (S / C) ^ 2 := by
      field_simp
      nlinarith
    have hu : 11 / 5 ≤ 1 / C := by
      apply (le_div_iff₀ hC).2
      linarith
    have hlo : 39 / 20 < S / C := by nlinarith
    have hhi : 1 / C < 121 / 50 := by
      have hu0 : 0 < 1 / C := by positivity
      nlinarith
    have hb := clippedArea_bound_low hlo h.le hhi
    convert hb using 1
    field_simp
  · have hs1 : S ≤ 1 := by nlinarith [sq_nonneg C]
    have hc : C / (1 + S) ≤ C / S / 2 := by
      have hs' : 0 < 1 + S := by linarith
      apply (div_le_iff₀ hs').2
      field_simp
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hs1)]
    have hid : 1 / C - (S / C - 11 / 10) ^ 2 * (C / S) =
        C / (1 + S) + 11 / 5 - (121 / 100) * (C / S) := by
      field_simp
      nlinarith [hcircle]
    rw [hid]
    have hp : 0 < C / S := div_pos hC hS
    linarith

theorem rotationCalculation_area_estimate (ω : RotationCalculationAngle) :
    1 / Real.cos ω.val - (Real.tan ω.val - rotationCalculationMinimum ω) ^ 2 *
      (Real.cos ω.val / Real.sin ω.val) < 11 / 5 := by
  have hw0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  have hC : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hS : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hC' : Real.cos ω.val ≤ 5 / 11 := by
    have h := Real.strictAntiOn_cos.antitoneOn
      (show Real.arccos (5 / 11 : ℝ) ∈ Set.Icc 0 Real.pi from
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
      (show ω.val ∈ Set.Icc 0 Real.pi from
        ⟨hw0.le, by linarith [ω.property.2, Real.pi_pos]⟩) ω.property.1
    simpa only [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 5 / 11)
      (by norm_num : (5 / 11 : ℝ) ≤ 1)] using h
  have hs : (Real.sin ω.val / Real.cos ω.val < 11 / 5) ↔
      ω.val < Real.arctan (11 / 5 : ℝ) := by
    rw [← Real.tan_eq_sin_div_cos, ← Real.arctan_lt_arctan_iff]
    rw [Real.arctan_tan (by linarith [Real.pi_pos]) ω.property.2]
  have hb := clippedArea_bound hC hS (Real.sin_sq_add_cos_sq ω.val) hC'
  dsimp at hb
  simp only [hs] at hb
  simpa only [← Real.tan_eq_sin_div_cos, rotationCalculationMinimum] using hb

theorem rotationCalculationMinimum_pos (ω : RotationCalculationAngle) :
    0 < rotationCalculationMinimum ω := by
  unfold rotationCalculationMinimum
  split_ifs <;> norm_num

theorem rotationCalculationMinimum_lt_tan (ω : RotationCalculationAngle) :
    rotationCalculationMinimum ω < Real.tan ω.val := by
  have hw0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  have hC : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hS : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hC' : Real.cos ω.val ≤ 5 / 11 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg (5 / 11))
      (by linarith [ω.property.2, Real.pi_pos] : ω.val ≤ Real.pi) ω.property.1
    simpa only [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 5 / 11)
      (by norm_num : (5 / 11 : ℝ) ≤ 1)] using h
  have hsq : Real.cos ω.val ^ 2 ≤ (5 / 11 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hC.le hC' 2
  have ht : (5 / 4 : ℝ) < Real.tan ω.val := by
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hC]
    nlinarith [Real.sin_sq_add_cos_sq ω.val]
  unfold rotationCalculationMinimum
  split_ifs <;> linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Clipped
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Clip the strip parallelogram by the two additional symmetric wall constraints. -/
@[expose]
def clippedCap (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    normalHalfPlane 0 (d + Real.tan ((Real.pi / 2 - ω) / 2)) false false ∩
    normalHalfPlane ((ω + Real.pi / 2 : ℝ) : Real.Angle)
      (d + Real.tan ((Real.pi / 2 - ω) / 2)) false false

theorem mem_clippedCap_iff (ω d : ℝ) (p : Point) :
    p ∈ clippedCap ω d ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
        Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1) ∧
      p 0 ≤ d + Real.tan ((Real.pi / 2 - ω) / 2) ∧
      -Real.sin ω * p 0 + Real.cos ω * p 1 ≤
        d + Real.tan ((Real.pi / 2 - ω) / 2) := by
  simp only [clippedCap, Set.mem_inter_iff, mem_stripParallelogram_iff]
  simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.cos_add, Real.sin_add, -Real.Angle.coe_add, and_assoc, mul_comm]

theorem clippedCap_removed_pieces_disjoint {C S c d : ℝ}
    (hC : 0 < C) (hS : 0 ≤ S) (hd : 0 ≤ d) (hc : c * (1 + S) = C) :
    Disjoint {p : Point | p 1 ≤ 1 ∧ c + d < p 0}
      {p : Point | c + d < -S * p 0 + C * p 1} := by
  rw [Set.disjoint_left]
  intro p hp hq
  change p 1 ≤ 1 ∧ c + d < p 0 at hp
  change c + d < -S * p 0 + C * p 1 at hq
  have hmul := mul_le_mul_of_nonneg_left hp.1 hC.le
  have hmul' := mul_le_mul_of_nonneg_left (le_of_lt hp.2) hS
  have hprod := mul_nonneg hd (by linarith : 0 ≤ 1 + S)
  nlinarith

private theorem mem_stripParallelogram_coordinates (ω : ℝ) (p : Point) :
    p ∈ (stripParallelogram ω).1 ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
        Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1) := by
  rw [mem_stripParallelogram_iff]
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

private theorem capReflection_rotatedCoordinate (ω : ℝ) (p : Point) :
    Real.cos ω * capReflection ω p 0 +
        Real.sin ω * capReflection ω p 1 = p 1 := by
  rw [capReflection_apply_zero, capReflection_apply_one]
  calc
    _ = (Real.sin ω ^ 2 + Real.cos ω ^ 2) * p 1 := by ring
    _ = p 1 := by rw [Real.sin_sq_add_cos_sq]; ring

private def rightRemovedTriangle (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    {p | d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0}

private def leftRemovedTriangle (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    {p | d + Real.tan ((Real.pi / 2 - ω) / 2) <
      -Real.sin ω * p 0 + Real.cos ω * p 1}

private theorem leftRemovedTriangle_eq_preimage (ω d : ℝ) :
    leftRemovedTriangle ω d =
      capReflection ω ⁻¹' rightRemovedTriangle ω d := by
  ext p
  simp only [leftRemovedTriangle, rightRemovedTriangle, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_preimage]
  rw [mem_stripParallelogram_coordinates,
    mem_stripParallelogram_coordinates,
    capReflection_rotatedCoordinate, capReflection_apply_zero,
    capReflection_apply_one]
  tauto

private theorem volume_stripParallelogram (ω : ℝ) (hC : 0 < Real.cos ω) :
    volume (stripParallelogram ω).1 = ENNReal.ofReal (1 / Real.cos ω) := by
  let f : ℝ → ℝ := fun y ↦ (-Real.sin ω * y) / Real.cos ω
  let g : ℝ → ℝ := fun y ↦ (1 - Real.sin ω * y) / Real.cos ω
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hfi : IntegrableOn f (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous f).intervalIntegrable 0 1)
  have hgi : IntegrableOn g (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous g).intervalIntegrable 0 1)
  have hfg : ∀ y ∈ Icc (0 : ℝ) 1, f y ≤ g y := by
    intro y _
    dsimp [f, g]
    rw [div_le_div_iff_of_pos_right hC]
    linarith
  have hset : (stripParallelogram ω).1 =
      {p : Point | p 1 ∈ Icc (0 : ℝ) 1 ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} := by
    ext p
    rw [mem_stripParallelogram_coordinates]
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨hy, ?_, ?_⟩
      · dsimp [f]
        apply (div_le_iff₀ hC).2
        linarith [hz.1]
      · dsimp [g]
        apply (le_div_iff₀ hC).2
        linarith [hz.2]
    · rintro ⟨hy, hx0, hx1⟩
      refine ⟨hy, ?_, ?_⟩
      · dsimp [f] at hx0
        have := (div_le_iff₀ hC).1 hx0
        linarith
      · dsimp [g] at hx1
        have := (le_div_iff₀ hC).1 hx1
        linarith
  rw [hset, volume_horizontalIcc hf hg measurableSet_Icc hfi hgi hfg]
  have hdiff : g - f = fun _ ↦ 1 / Real.cos ω := by
    funext y
    dsimp [f, g]
    field_simp [hC.ne']
    ring
  rw [hdiff, setIntegral_const]
  simp

private theorem volume_rightRemovedTriangle (ω d : ℝ)
    (hω : ω ∈ Ioo 0 (Real.pi / 2)) (hd0 : 0 ≤ d) (hdt : d ≤ Real.tan ω) :
    volume (rightRemovedTriangle ω d) =
      ENNReal.ofReal ((Real.tan ω - d) ^ 2 *
        (Real.cos ω / Real.sin ω) / 2) := by
  let C := Real.cos ω
  let S := Real.sin ω
  let c := Real.tan ((Real.pi / 2 - ω) / 2)
  let A := c + d
  let b := Real.tan ω - d
  let H := b * C / S
  let f : ℝ → ℝ := fun _ ↦ A
  let g : ℝ → ℝ := fun y ↦ (1 - S * y) / C
  have hC : 0 < C :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi hω.1
    (by linarith [hω.2, Real.pi_pos])
  have hcircle : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq ω
  have hgap : c = C⁻¹ - Real.tan ω :=
    (parallelogram_gap ω ⟨hω.1.le, hω.2⟩).2.2.2.2
  have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
  have hcC : c * C = 1 - S := by
    rw [hgap, htan]
    field_simp [hC.ne']
  have hS1 : S < 1 := by nlinarith [sq_pos_of_pos hC]
  have hc0 : 0 < c := by
    have hcdiv : c = (1 - S) / C := by
      apply (eq_div_iff hC.ne').2
      exact hcC
    rw [hcdiv]
    exact div_pos (sub_pos.mpr hS1) hC
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hbC : b * C = S - d * C := by
    dsimp [b]
    rw [htan]
    field_simp [hC.ne']
  have hAC : A * C = 1 - b * C := by
    dsimp [A]
    nlinarith [hcC, hbC]
  have hH0 : 0 ≤ H := by positivity
  have hH1 : H ≤ 1 := by
    dsimp [H, b]
    apply (div_le_iff₀ hS).2
    dsimp [b] at hbC
    nlinarith
  have hf : Measurable f := measurable_const
  have hg : Measurable g := by fun_prop
  have hfi : IntegrableOn f (Icc (0 : ℝ) H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH0).mp
      ((by fun_prop : Continuous f).intervalIntegrable 0 H)
  have hgi : IntegrableOn g (Icc (0 : ℝ) H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH0).mp
      ((by fun_prop : Continuous g).intervalIntegrable 0 H)
  have hfg : ∀ y ∈ Icc (0 : ℝ) H, f y ≤ g y := by
    intro y hy
    dsimp [f, g, A]
    apply (le_div_iff₀ hC).2
    dsimp [H, b] at hy
    dsimp [b] at hbC hAC
    have hy' := (le_div_iff₀ hS).1 hy.2
    nlinarith
  have hset : rightRemovedTriangle ω d =
      {p : Point | p 1 ∈ Icc (0 : ℝ) H ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} := by
    ext p
    simp only [rightRemovedTriangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_Icc, Set.mem_Ioc]
    rw [mem_stripParallelogram_coordinates]
    constructor
    · rintro ⟨⟨hy, hz⟩, hxA⟩
      refine ⟨⟨hy.1, ?_⟩, ?_, ?_⟩
      · dsimp [H, b]
        have hu : C * A + S * p 1 < 1 := by
          dsimp [A]
          nlinarith [mul_lt_mul_of_pos_left hxA hC]
        apply (le_div_iff₀ hS).2
        nlinarith [hAC]
      · simpa [f, A, add_comm]
      · dsimp [g]
        apply (le_div_iff₀ hC).2
        linarith [hz.2]
    · rintro ⟨hy, hxA, hxU⟩
      refine ⟨⟨⟨hy.1, hy.2.trans hH1⟩, ?_, ?_⟩, ?_⟩
      · have hA0 : 0 < A := by dsimp [A]; linarith
        dsimp [f, A] at hxA
        nlinarith [mul_pos hC (lt_trans hA0 hxA)]
      · dsimp [g] at hxU
        have := (le_div_iff₀ hC).1 hxU
        linarith
      · simpa [f, A, add_comm] using hxA
  rw [hset, volume_horizontalIoc hf hg measurableSet_Icc hfi hgi hfg]
  have hdiff : g - f = fun y ↦ b - S / C * y := by
    funext y
    dsimp [f, g, A, b]
    rw [hgap, htan]
    field_simp [hC.ne']
    ring
  rw [hdiff, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hH0]
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ b) volume 0 H :=
    continuous_const.intervalIntegrable 0 H
  have hlinear : IntervalIntegrable (fun y : ℝ ↦ S / C * y) volume 0 H :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 H
  rw [intervalIntegral.integral_sub hconst hlinear,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [sub_zero, smul_eq_mul]
  congr 1
  norm_num
  change H * b - S / C * (H ^ 2 / 2) = b ^ 2 * (C / S) / 2
  dsimp [H]
  field_simp [hC.ne', hS.ne']
  ring

private theorem measurableSet_stripParallelogram (ω : ℝ) :
    MeasurableSet (stripParallelogram ω).1 := by
  rw [show (stripParallelogram ω).1 =
      {p : Point |
        (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
          Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1)} by
    ext p
    exact mem_stripParallelogram_coordinates ω p]
  measurability

private theorem measurableSet_rightRemovedTriangle (ω d : ℝ) :
    MeasurableSet (rightRemovedTriangle ω d) := by
  unfold rightRemovedTriangle
  apply (measurableSet_stripParallelogram ω).inter
  measurability

private theorem measurableSet_leftRemovedTriangle (ω d : ℝ) :
    MeasurableSet (leftRemovedTriangle ω d) := by
  unfold leftRemovedTriangle
  apply (measurableSet_stripParallelogram ω).inter
  measurability

private theorem volume_leftRemovedTriangle_eq_right (ω d : ℝ) :
    volume (leftRemovedTriangle ω d) = volume (rightRemovedTriangle ω d) := by
  rw [leftRemovedTriangle_eq_preimage]
  exact (LinearIsometryEquiv.measurePreserving (capReflection ω)).measure_preimage
    (measurableSet_rightRemovedTriangle ω d).nullMeasurableSet

private theorem stripParallelogram_decomposition (ω d : ℝ) :
    (stripParallelogram ω).1 =
      (clippedCap ω d ∪ rightRemovedTriangle ω d) ∪ leftRemovedTriangle ω d := by
  ext p
  simp only [Set.mem_union]
  constructor
  · intro hp
    by_cases hx : p 0 ≤ d + Real.tan ((Real.pi / 2 - ω) / 2)
    · by_cases hz : -Real.sin ω * p 0 + Real.cos ω * p 1 ≤
          d + Real.tan ((Real.pi / 2 - ω) / 2)
      · exact Or.inl (Or.inl ((mem_clippedCap_iff ω d p).2
          ⟨((mem_stripParallelogram_coordinates ω p).1 hp).1,
            ((mem_stripParallelogram_coordinates ω p).1 hp).2, hx, hz⟩))
      · exact Or.inr ⟨hp, by
          change d + Real.tan ((Real.pi / 2 - ω) / 2) <
            -Real.sin ω * p 0 + Real.cos ω * p 1
          exact lt_of_not_ge hz⟩
    · exact Or.inl (Or.inr ⟨hp, by
        change d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0
        exact lt_of_not_ge hx⟩)
  · rintro (hp | hp)
    · rcases hp with hp | hp
      · exact (mem_stripParallelogram_coordinates ω p).2
          ⟨((mem_clippedCap_iff ω d p).1 hp).1,
            ((mem_clippedCap_iff ω d p).1 hp).2.1⟩
      · exact hp.1
    · exact hp.1

private theorem clippedCap_disjoint_rightRemovedTriangle (ω d : ℝ) :
    Disjoint (clippedCap ω d) (rightRemovedTriangle ω d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := ((mem_clippedCap_iff ω d p).1 hp).2.2.1
  exact (not_lt_of_ge hp') hq.2

private theorem clippedCap_disjoint_leftRemovedTriangle (ω d : ℝ) :
    Disjoint (clippedCap ω d) (leftRemovedTriangle ω d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := ((mem_clippedCap_iff ω d p).1 hp).2.2.2
  exact (not_lt_of_ge hp') hq.2

private theorem rightRemovedTriangle_disjoint_leftRemovedTriangle
    {ω d : ℝ} (hC : 0 < Real.cos ω) (hS : 0 ≤ Real.sin ω) (hd : 0 ≤ d)
    (hc : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) = Real.cos ω) :
    Disjoint (rightRemovedTriangle ω d) (leftRemovedTriangle ω d) := by
  apply (clippedCap_removed_pieces_disjoint hC hS hd hc).mono
  · rintro p ⟨hp, hright⟩
    change d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0 at hright
    exact ⟨((mem_stripParallelogram_coordinates ω p).1 hp).1.2,
      by simpa [add_comm] using hright⟩
  · rintro p ⟨_, hleft⟩
    change d + Real.tan ((Real.pi / 2 - ω) / 2) <
      -Real.sin ω * p 0 + Real.cos ω * p 1 at hleft
    simpa [add_comm] using hleft

theorem clippedCap_area_formula (ω d : ℝ)
    (hω : ω ∈ Ioo 0 (Real.pi / 2)) (hd0 : 0 ≤ d) (hdt : d ≤ Real.tan ω) :
    ClassicalResults.area (clippedCap ω d) =
      1 / Real.cos ω - (Real.tan ω - d) ^ 2 *
        (Real.cos ω / Real.sin ω) := by
  let C := Real.cos ω
  let S := Real.sin ω
  let c := Real.tan ((Real.pi / 2 - ω) / 2)
  let T := (Real.tan ω - d) ^ 2 * (C / S) / 2
  have hC : 0 < C :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi hω.1
    (by linarith [hω.2, Real.pi_pos])
  have hgap : c = C⁻¹ - Real.tan ω :=
    (parallelogram_gap ω ⟨hω.1.le, hω.2⟩).2.2.2.2
  have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
  have hcC : c * C = 1 - S := by
    rw [hgap, htan]
    field_simp [hC.ne']
  have hc : c * (1 + S) = C := by
    apply (mul_right_cancel₀ hC.ne')
    nlinarith [hcC, Real.sin_sq_add_cos_sq ω]
  have hP := volume_stripParallelogram ω hC
  have hR := volume_rightRemovedTriangle ω d hω hd0 hdt
  have hL : volume (leftRemovedTriangle ω d) = ENNReal.ofReal T := by
    rw [volume_leftRemovedTriangle_eq_right, hR]
  have hR' : volume (rightRemovedTriangle ω d) = ENNReal.ofReal T := by
    simpa [T, C, S] using hR
  have hCR := clippedCap_disjoint_rightRemovedTriangle ω d
  have hCL := clippedCap_disjoint_leftRemovedTriangle ω d
  have hRL := rightRemovedTriangle_disjoint_leftRemovedTriangle hC hS.le hd0 hc
  have hdecomp : volume (stripParallelogram ω).1 =
      (volume (clippedCap ω d) + volume (rightRemovedTriangle ω d)) +
        volume (leftRemovedTriangle ω d) := by
    rw [stripParallelogram_decomposition,
      measure_union (hCL.union_left hRL) (measurableSet_leftRemovedTriangle ω d),
      measure_union hCR (measurableSet_rightRemovedTriangle ω d)]
  rw [hP, hR', hL] at hdecomp
  have hclip_subset : clippedCap ω d ⊆ (stripParallelogram ω).1 := by
    intro p hp
    exact (mem_stripParallelogram_coordinates ω p).2
      ⟨((mem_clippedCap_iff ω d p).1 hp).1,
        ((mem_clippedCap_iff ω d p).1 hp).2.1⟩
  have hclip_ne : volume (clippedCap ω d) ≠ ⊤ := by
    apply ne_of_lt
    refine lt_of_le_of_lt (measure_mono hclip_subset) ?_
    rw [hP]
    exact ENNReal.ofReal_lt_top
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hTne : ENNReal.ofReal T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum_ne : volume (clippedCap ω d) + ENNReal.ofReal T ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hclip_ne, hTne⟩
  have hreal := congrArg ENNReal.toReal hdecomp
  rw [ENNReal.toReal_add hsum_ne hTne,
    ENNReal.toReal_add hclip_ne hTne,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / Real.cos ω),
    ENNReal.toReal_ofReal hT0] at hreal
  unfold ClassicalResults.area
  dsimp [T, C, S] at hreal ⊢
  linarith

theorem clippedCap_minimum_area (ω : RotationCalculationAngle) :
    ClassicalResults.area (clippedCap ω.val (rotationCalculationMinimum ω)) < 11 / 5 := by
  have hω0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  calc
    ClassicalResults.area (clippedCap ω.val (rotationCalculationMinimum ω)) =
        1 / Real.cos ω.val -
          (Real.tan ω.val - rotationCalculationMinimum ω) ^ 2 *
            (Real.cos ω.val / Real.sin ω.val) :=
      clippedCap_area_formula ω.val (rotationCalculationMinimum ω)
        ⟨hω0, ω.property.2⟩ (rotationCalculationMinimum_pos ω).le
        (rotationCalculationMinimum_lt_tan ω).le
    _ < 11 / 5 := rotationCalculation_area_estimate ω

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Densities
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MovingSofa

private theorem coe_injOn_halfTurn :
    Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Icc 0 Real.pi) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro x hx y hy heq
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show x ∈ Ico 0 (0 + 2 * Real.pi) from ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
    (show y ∈ Ico 0 (0 + 2 * Real.pi) from ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩)).mp heq

/-- A right-angle cap whose surface area measure has angular densities on the two upper quarter
circles has no atom at a normal direction of the right upper quarter. -/
theorem HasCapDensities.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico
    {K : RightAngleCapSpace} {r s : ℝ → ℝ≥0} (hK : HasCapDensities K r s) {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) :
    surfaceAreaMeasure K.1 {(t : Real.Angle)} = 0 := by
  have he := congrArg (fun μ : Measure Real.Angle ↦ μ {(t : Real.Angle)}) hK.2.2.1
  have hm : (t : Real.Angle) ∈
      (fun x : ℝ ↦ (x : Real.Angle)) '' Ico 0 (Real.pi / 2) := ⟨t, ht, rfl⟩
  rw [Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.mpr (singleton_subset_iff.mpr hm)] at he
  rw [he]
  apply Measure.map_restrict_withDensity_singleton volume _ Real.Angle.continuous_coe.measurable
    _ (coe_injOn_halfTurn.mono ?_) _ ht
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩

/-- A right-angle cap whose surface area measure has angular densities on the two upper quarter
circles has no atom at a normal direction of the left upper quarter. -/
theorem HasCapDensities.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc
    {K : RightAngleCapSpace} {r s : ℝ → ℝ≥0} (hK : HasCapDensities K r s) {t : ℝ}
    (ht : t ∈ Ioc 0 (Real.pi / 2)) :
    surfaceAreaMeasure K.1 {((t + Real.pi / 2 : ℝ) : Real.Angle)} = 0 := by
  have he := congrArg (fun μ : Measure Real.Angle ↦
    μ {((t + Real.pi / 2 : ℝ) : Real.Angle)}) hK.2.2.2
  have hm : ((t + Real.pi / 2 : ℝ) : Real.Angle) ∈
      (fun x : ℝ ↦ (x : Real.Angle)) '' Ioc (Real.pi / 2) Real.pi :=
    ⟨t + Real.pi / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  rw [Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.mpr (singleton_subset_iff.mpr hm)] at he
  rw [he]
  apply Measure.map_restrict_withDensity_singleton volume _
    (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable
    _ ?_ _ ht
  intro x hx y hy hxy
  have heq := coe_injOn_halfTurn
    (show x + Real.pi / 2 ∈ Icc 0 Real.pi from
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩)
    (show y + Real.pi / 2 ∈ Icc 0 Real.pi from
      ⟨by linarith [hy.1, Real.pi_pos], by linarith [hy.2]⟩) hxy
  linarith

theorem capDensities_contact_eq (K : RightAngleCapSpace)
    (hK : ∃ r s, HasCapDensities K r s) :
    (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (capVertices K t).1.1 = (capVertices K t).1.2 ∧
      (tangentArmLengths K t).1.1 = (tangentArmLengths K t).1.2) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      (capVertices K t).2.1 = (capVertices K t).2.2 ∧
      (tangentArmLengths K t).2.1 = (tangentArmLengths K t).2.2) := by
  obtain ⟨r, s, hK⟩ := hK
  constructor
  · intro t ht
    have h := (surfaceAreaMeasure_atom_length K.1 (t : Real.Angle)).2.2
    rw [hK.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ht] at h
    simp only [ENNReal.toReal_zero, zero_smul, add_zero] at h
    have h' : (capVertices K t).1.1 = (capVertices K t).1.2 := h
    exact ⟨h', by simp only [tangentArmLengths, h']⟩
  · intro t ht
    have h := (surfaceAreaMeasure_atom_length K.1
      ((t + Real.pi / 2 : ℝ) : Real.Angle)).2.2
    rw [hK.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc ht] at h
    simp only [ENNReal.toReal_zero, zero_smul, add_zero] at h
    have h' : (capVertices K t).2.1 = (capVertices K t).2.2 := h
    exact ⟨h', by simp only [tangentArmLengths, h']⟩

/-- A right-angle cap carrying angular densities has singleton extreme faces at every upper normal
direction except possibly the vertical one: the densities exclude atoms of the surface area measure
on the two open quarter circles, so the corresponding faces have zero side length. -/
theorem capDensities_edgeVertices_eq (K : RightAngleCapSpace)
    (hK : ∃ r s, HasCapDensities K r s) {t : ℝ} (ht : t ∈ Icc 0 Real.pi)
    (htop : t ≠ Real.pi / 2) :
    (edgeVertices K.val (t : Real.Angle)).1 = (edgeVertices K.val (t : Real.Angle)).2 := by
  rcases lt_or_gt_of_ne htop with h | h
  · exact ((capDensities_contact_eq K hK).1 t ⟨ht.1, h⟩).1
  · have hmem : t - Real.pi / 2 ∈ Ioc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith [ht.2]⟩
    have h' : (edgeVertices K.val ((t - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 =
        (edgeVertices K.val ((t - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).2 :=
      ((capDensities_contact_eq K hK).2 (t - Real.pi / 2) hmem).1
    rwa [show t - Real.pi / 2 + Real.pi / 2 = t from by ring] at h'

/-- The two cap contact paths and their scalar density functions on the quarter-turn interval. -/
@[expose]
def nondegenerateCapData (K : RightAngleCapSpace)
    (_hK : ∃ r s, HasCapDensities K r s) :
    ((Set.Icc (0 : ℝ) (Real.pi / 2) → Point) ×
      (Set.Icc (0 : ℝ) (Real.pi / 2) → Point)) ×
    ((Set.Icc (0 : ℝ) (Real.pi / 2) → ℝ) ×
      (Set.Icc (0 : ℝ) (Real.pi / 2) → ℝ)) := by
  classical
  exact ((fun t ↦ if (t : ℝ) = Real.pi / 2 then (capVertices K t).1.2
      else (capVertices K t).1.1,
    fun t ↦ (capVertices K t).2.1),
    (fun t ↦ if (t : ℝ) = Real.pi / 2 then (tangentArmLengths K t).1.2
      else (tangentArmLengths K t).1.1,
    fun t ↦ (tangentArmLengths K t).2.1))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Cap / Upper Boundary
-/

public section

noncomputable section

namespace MovingSofa

/-- The union of exposed cap edges over the upper range of normal directions. -/
@[expose]
def capUpperBoundary {ω : ℝ} (K : CapSpace ω) : Set Point :=
  ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2), exposedEdge K.val (t : Real.Angle)

theorem capUpperBoundary_connected {ω : ℝ} (K : CapSpace ω) :
    IsConnected (capUpperBoundary K) := by
  let I : Set ℝ := Set.Icc 0 (ω + Real.pi / 2)
  let G : Set (I × Point) :=
    {q | q.2 ∈ exposedEdge K.val ((q.1 : ℝ) : Real.Angle)}
  have hω : 0 ≤ ω + Real.pi / 2 := by
    have := K.property.1
    positivity
  have hI : IsConnected I := isConnected_Icc hω
  let _ : ConnectedSpace I := Subtype.connectedSpace hI
  have hnormal : Continuous (fun q : I × Point ↦
      normalVector (((q.1 : I) : ℝ) : Real.Angle)) :=
    continuous_normalVector_real.comp (continuous_subtype_val.comp continuous_fst)
  have hsupport : Continuous (fun q : I × Point ↦
      supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)) :=
    (continuous_supportValue_real K.val).comp (continuous_subtype_val.comp continuous_fst)
  have heq : IsClosed {q : I × Point |
      inner ℝ q.2 (normalVector (((q.1 : I) : ℝ) : Real.Angle)) =
        supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)} :=
    isClosed_eq (continuous_snd.inner hnormal) hsupport
  have hG : IsCompact G := by
    rw [show G = Set.univ ×ˢ (K.val : Set Point) ∩
        {q : I × Point | inner ℝ q.2 (normalVector (((q.1 : I) : ℝ) : Real.Angle)) =
          supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)} by
      ext q
      simp only [G, exposedEdge, supportingLineHalfPlane, normalLine, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]]
    exact (isCompact_univ.prod K.val.isCompact).inter_right heq
  let _ : CompactSpace G := isCompact_iff_compactSpace.mp hG
  let π : G → I := fun q ↦ q.1.1
  have hπcont : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπsurj : Function.Surjective π := by
    intro t
    obtain ⟨x, hx⟩ := exposedEdge_nonempty K.val ((t : ℝ) : Real.Angle)
    exact ⟨⟨(t, x), hx⟩, rfl⟩
  have hπquot : Topology.IsQuotientMap π :=
    Topology.IsQuotientMap.of_surjective_continuous hπsurj hπcont
  have hfiber (t : I) : IsConnected (π ⁻¹' {t}) := by
    let E := exposedEdge K.val ((t : ℝ) : Real.Angle)
    let e : E → G := fun x ↦ ⟨(t, x), x.property⟩
    have hecont : Continuous e := by
      apply Continuous.subtype_mk
      exact continuous_const.prodMk continuous_subtype_val
    have himage : e '' Set.univ = π ⁻¹' {t} := by
      ext q
      constructor
      · rintro ⟨x, -, rfl⟩
        simp [π, e]
      · intro hq
        have hqt : q.1.1 = t := by simpa [π] using hq
        have hqx : q.1.2 ∈ exposedEdge K.val ((t : ℝ) : Real.Angle) := by
          have hqG := q.property
          change q.1.2 ∈ exposedEdge K.val (((q.1.1 : I) : ℝ) : Real.Angle) at hqG
          simpa [hqt] using hqG
        let x : E := ⟨q.1.2, hqx⟩
        refine ⟨x, Set.mem_univ x, ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · exact hqt.symm
        · rfl
    rw [← himage]
    let _ : ConnectedSpace E :=
      Subtype.connectedSpace (isConnected_exposedEdge K.val ((t : ℝ) : Real.Angle))
    exact isConnected_univ.image e hecont.continuousOn
  have hGconn : IsConnected (Set.univ : Set G) := by
    exact hπquot.isCoinducing.isConnected_preimage_of_isClosed hfiber isClosed_univ
      isConnected_univ
  have himage : (fun q : G ↦ q.1.2) '' Set.univ = capUpperBoundary K := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, capUpperBoundary, Set.mem_iUnion]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1.1, q.1.1.property, q.property⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨⟨(⟨t, ht⟩, x), hx⟩, rfl⟩
  rw [← himage]
  exact hGconn.image _ (continuous_snd.comp continuous_subtype_val).continuousOn

private theorem CapSpace.mem_interior_of_mem_not_upperBoundary {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hpK : p ∈ (K.val : Set Point))
    (hpδ : p ∉ ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2),
      exposedEdge K.val (t : Real.Angle)) :
    (⟨p, K.subset_capFan hpK⟩ : capFan ω) ∈
      interior {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
  let I := Set.Icc 0 (ω + Real.pi / 2)
  let gap : ℝ → ℝ := fun t ↦
    supportValue K.val (t : Real.Angle) - inner ℝ p (normalVector (t : Real.Angle))
  have hgap_cont : Continuous gap := (continuous_supportValue_real K.val).sub
    (continuous_const.inner continuous_normalVector_real)
  have hgap_pos : ∀ t ∈ I, 0 < gap t := by
    intro t ht
    have hle := inner_le_supportValue K.val hpK (t : Real.Angle)
    have hne : inner ℝ p (normalVector (t : Real.Angle)) ≠
        supportValue K.val (t : Real.Angle) := by
      intro heq
      apply hpδ
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht,
        ⟨hpK, by simpa [supportingLineHalfPlane, normalLine]⟩⟩⟩
    dsimp [gap]
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)
  have hIne : I.Nonempty := ⟨0, by
    change 0 ∈ Set.Icc 0 (ω + Real.pi / 2)
    exact ⟨le_rfl, by linarith [K.property.1, Real.pi_pos]⟩⟩
  have hIcompact : IsCompact I := by
    dsimp [I]
    exact isCompact_Icc
  obtain ⟨m, hm, hmle⟩ := IsCompact.exists_pos_forall_le hIcompact hIne
    hgap_cont.continuousOn hgap_pos
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (half_pos hm)) ?_
  intro q hq
  change (q : Point) ∈ (K.val : Set Point)
  apply K.mem_of_mem_capFan_of_lt_supportValue q.property
  intro t ht
  have hdist : ‖(q : Point) - p‖ < m / 2 := by
    change dist (q : Point) p < m / 2 at hq
    simpa [dist_eq_norm] using hq
  have hnorm := norm_normalVector_real t
  have hinner : inner ℝ ((q : Point) - p) (normalVector (t : Real.Angle)) < m / 2 := by
    calc
      inner ℝ ((q : Point) - p) (normalVector (t : Real.Angle))
          ≤ ‖(q : Point) - p‖ * ‖normalVector (t : Real.Angle)‖ := real_inner_le_norm _ _
      _ < m / 2 := by simpa [hnorm] using hdist
  have := hmle t ht
  dsimp [gap] at this
  rw [inner_sub_left] at hinner
  linarith

private theorem CapSpace.mem_frontier_of_mem_upperBoundary {ω : ℝ}
    (K : CapSpace ω) {p : Point}
    (hp : p ∈ ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2), exposedEdge K.val (t : Real.Angle)) :
    ∃ z : capFan ω, (z : Point) = p ∧
      z ∈ frontier {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
  obtain ⟨t, hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨htI, hpedge⟩ := Set.mem_iUnion.mp hp
  let z : capFan ω := ⟨p, K.subset_capFan hpedge.1⟩
  have hzK : z ∈ {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := hpedge.1
  refine ⟨z, rfl, (mem_frontier_iff_notMem_interior hzK).2 ?_⟩
  intro hzint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzint
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let q : Point := p + e • normalVector (t : Real.Angle)
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1
    (htI.2.trans (by linarith [K.property.2.1, Real.pi_pos]))
  have hcos : 0 ≤ Real.cos (t - ω) := Real.cos_nonneg_of_mem_Icc ⟨by
    linarith [htI.1, K.property.2.1, Real.pi_pos], by linarith [htI.2]⟩
  have hqfan : q ∈ capFan ω := by
    constructor
    · change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle))
      dsimp [q]
      rw [inner_add_left, inner_smul_left, inner_normalVector_normalVector]
      have hpω := (K.subset_capFan hpedge.1).1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      simp at *
      nlinarith
    · change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      dsimp [q]
      rw [inner_add_left, inner_smul_left, inner_normalVector_normalVector]
      have hpT := (K.subset_capFan hpedge.1).2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
      rw [Real.cos_sub]
      simp
      nlinarith
  have hqball : (⟨q, hqfan⟩ : capFan ω) ∈ Metric.ball z ε := by
    change dist q p < ε
    simp only [q, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_normalVector_real,
      mul_one]
    rw [Real.norm_eq_abs, abs_of_pos he]
    dsimp [e]
    linarith
  have hqK := interior_subset (hball hqball)
  change q ∈ (K.val : Set Point) at hqK
  have hqle := inner_le_supportValue K.val hqK (t : Real.Angle)
  have hpedge_eq := hpedge.2
  change inner ℝ p (normalVector (t : Real.Angle)) = supportValue K.val (t : Real.Angle)
    at hpedge_eq
  dsimp [q] at hqle
  rw [inner_add_left, inner_smul_left, inner_normalVector_self, hpedge_eq] at hqle
  simp at hqle
  nlinarith

theorem capUpperBoundary_relativeBoundary {ω : ℝ} (K : CapSpace ω) :
    capUpperBoundary K =
      Subtype.val '' frontier {p : capFan ω | (p : Point) ∈ (K.val : Set Point)} := by
  ext p
  constructor
  · intro hp
    obtain ⟨z, rfl, hz⟩ := K.mem_frontier_of_mem_upperBoundary hp
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hzfront, rfl⟩
    let S : Set (capFan ω) := {p | (p : Point) ∈ (K.val : Set Point)}
    have hSclosed : IsClosed S := K.val.isClosed.preimage continuous_subtype_val
    have hzS : z ∈ S := by
      apply hSclosed.closure_subset
      exact frontier_subset_closure hzfront
    by_contra hzupper
    have hzint := K.mem_interior_of_mem_not_upperBoundary hzS hzupper
    exact ((mem_frontier_iff_notMem_interior hzS).1 hzfront) hzint

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Bounds.Niche`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Bounds / Niche
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- The infimum of the set’s horizontal coordinates. -/
@[expose]
def horizontalMin (S : Set Point) : ℝ := sInf ((fun p ↦ p 0) '' S)

/-- The supremum of the set’s horizontal coordinates. -/
@[expose]
def horizontalMax (S : Set Point) : ℝ := sSup ((fun p ↦ p 0) '' S)

/-- The niche is measurable, finite-area and enclosed by the specified horizontal-span
rectangle. -/
@[expose]
def HasNicheRectangleBounds (S N : Set Point) : Prop :=
  MeasurableSet N ∧
  N ⊆ {p | horizontalMin S < p 0 ∧ p 0 < horizontalMax S ∧
    0 ≤ p 1 ∧ p 1 < (horizontalMax S - horizontalMin S) / 2} ∧
  volume N < ⊤ ∧
  (horizontalMax S - horizontalMin S = 0 → ClassicalResults.area N = 0)

private theorem niche_coordinate_bounds {c s l r x y : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hcircle : s ^ 2 + c ^ 2 = 1)
    (hlr : l ≤ r) (hy : 0 ≤ y)
    (hx : c * x + s * y < c * r + s - 1)
    (hz : -s * x + c * y < -s * l + c - 1) :
    l < x ∧ x < r ∧ y < (r - l) / 2 := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
  have hsc : s * c ≤ 1 / 2 := by nlinarith [sq_nonneg (s - c)]
  have hsum : 1 ≤ s + c := by nlinarith [mul_pos hs hc]
  have hxlo : l < x := by nlinarith [mul_nonneg hc.le hy]
  have hxhi : x < r := by nlinarith [mul_nonneg hs.le hy]
  have h₁ := mul_lt_mul_of_pos_left hx hs
  have h₂ := mul_lt_mul_of_pos_left hz hc
  have hcomb : y < s * c * (r - l) + 1 - s - c := by
    nlinarith [show s ^ 2 * y + c ^ 2 * y = y by nlinarith [hcircle]]
  refine ⟨hxlo, hxhi, hcomb.trans_le ?_⟩
  have := mul_le_mul_of_nonneg_right hsc (sub_nonneg.mpr hlr)
  linarith

theorem horizontalMin_le (K : ConvexBody Point) {p : Point} (hp : p ∈ K) :
    horizontalMin K ≤ p 0 := by
  apply csInf_le ((K.isCompact.image (by fun_prop : Continuous (fun p : Point ↦ p 0))).bddBelow)
  exact ⟨p, hp, rfl⟩

theorem le_horizontalMax (K : ConvexBody Point) {p : Point} (hp : p ∈ K) :
    p 0 ≤ horizontalMax K := by
  apply le_csSup ((K.isCompact.image (by fun_prop : Continuous (fun p : Point ↦ p 0))).bddAbove)
  exact ⟨p, hp, rfl⟩

theorem horizontalMin_le_horizontalMax (K : ConvexBody Point) :
    horizontalMin K ≤ horizontalMax K := by
  obtain ⟨p, hp⟩ := K.nonempty
  exact (horizontalMin_le K hp).trans (le_horizontalMax K hp)

/-- The support value at the horizontal normal is the horizontal maximum. -/
theorem supportValue_zero_eq_horizontalMax (S : Set Point) :
    supportValue S ((0 : ℝ) : Real.Angle) = horizontalMax S := by
  rw [supportValue, horizontalMax]
  congr 1
  refine Set.image_congr fun p _ ↦ ?_
  rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero]

/-- The support value at the straight angle negates the horizontal minimum. -/
theorem supportValue_pi_eq_neg_horizontalMin (S : Set Point) :
    supportValue S ((Real.pi : ℝ) : Real.Angle) = -horizontalMin S := by
  have himage : (fun p : Point ↦ -p 0) '' S = -((fun p : Point ↦ p 0) '' S) := by
    ext x
    simp [neg_eq_iff_eq_neg]
  rw [supportValue, horizontalMin, ← Real.sSup_neg, ← himage]
  congr 1
  refine Set.image_congr fun p _ ↦ ?_
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi, mul_neg_one, mul_zero, add_zero]

/-- Both horizontal extrema of a compact convex body are attained. -/
theorem exists_horizontal_extrema (K : ConvexBody Point) :
    ∃ l r : Point, l ∈ (K : Set Point) ∧ r ∈ (K : Set Point) ∧
      l 0 = horizontalMin K ∧ r 0 = horizontalMax K := by
  obtain ⟨l, hlK, hl⟩ := K.isCompact.exists_isMinOn K.nonempty
    (by fun_prop : Continuous (fun p : Point ↦ p 0)).continuousOn
  obtain ⟨r, hrK, hr⟩ := K.isCompact.exists_isMaxOn K.nonempty
    (by fun_prop : Continuous (fun p : Point ↦ p 0)).continuousOn
  refine ⟨l, r, hlK, hrK, ?_, ?_⟩
  · apply le_antisymm
    · apply le_csInf (K.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact hl hp
    · exact horizontalMin_le K hlK
  · apply le_antisymm
    · exact le_horizontalMax K hrK
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact hr hp

theorem CapSpace.mem_horizontalStrip {ω : ℝ} (K : CapSpace ω)
    {p : Point} (hp : p ∈ K.val) : 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  have hupper := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
  have hlower := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.property.2.2.2.1] at hupper
  rw [K.property.2.2.2.2.2.1] at hlower
  rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring] at hlower
  simp only [normalVector, frame, Real.Angle.cos_coe, Real.cos_pi_div_two, Real.Angle.sin_coe,
    Real.sin_pi_div_two, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_mul, zero_add, Real.cos_add, Real.cos_pi, mul_zero, Real.sin_pi, mul_one, sub_self,
    Real.sin_add, neg_neg, neg_mul, Left.neg_nonpos_iff] at hupper hlower
  exact ⟨by linarith, hupper⟩

/-- A cap has area at most its horizontal width. -/
theorem CapSpace.area_le_horizontalWidth {ω : ℝ} (K : CapSpace ω) :
    ClassicalResults.area (K.val : Set Point) ≤ horizontalMax K.val - horizontalMin K.val := by
  let R : Set Point := {p | p 0 ∈ Set.Icc (horizontalMin K.val) (horizontalMax K.val) ∧
    p 1 ∈ Set.Icc 0 1}
  have hsub : (K.val : Set Point) ⊆ R := fun p hp ↦
    ⟨⟨horizontalMin_le K.val hp, le_horizontalMax K.val hp⟩, K.mem_horizontalStrip hp⟩
  have hvol : volume R = ENNReal.ofReal (horizontalMax K.val - horizontalMin K.val) := by
    rw [EuclideanSpace.volume_setOf_apply_mem_Icc]
    simp
  have hfinite : volume R ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  calc
    ClassicalResults.area (K.val : Set Point) ≤ ClassicalResults.area R :=
      ENNReal.toReal_mono hfinite (measure_mono hsub)
    _ = horizontalMax K.val - horizontalMin K.val := by
      change (volume R).toReal = _
      rw [hvol, ENNReal.toReal_ofReal (sub_nonneg.mpr (horizontalMin_le_horizontalMax K.val))]

/-- Upper support bounds from the horizontal extrema and the unit-height strip. -/
theorem CapSpace.supportValue_horizontal_bounds {ω t : ℝ} (K : CapSpace ω)
    (ht : t ∈ Set.Ioo 0 ω) :
    supportValue K.val (t : Real.Angle) ≤
      Real.cos t * horizontalMax K.val + Real.sin t ∧
    supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
      -Real.sin t * horizontalMin K.val + Real.cos t := by
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩).le
  have hs : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])).le
  constructor
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx := mul_le_mul_of_nonneg_left (le_horizontalMax K.val hp) hc
    have hy := mul_le_mul_of_nonneg_left (K.mem_horizontalStrip hp).2 hs
    simp [normalVector, frame, PiLp.inner_apply]
    nlinarith
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx := mul_le_mul_of_nonneg_left (horizontalMin_le K.val hp) hs
    have hy := mul_le_mul_of_nonneg_left (K.mem_horizontalStrip hp).2 hc
    simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
      -Real.Angle.coe_add]
    nlinarith

/-- Lower support bounds from the horizontal extrema and the nonnegative heights of a cap. -/
theorem CapSpace.horizontal_le_supportValue {ω t : ℝ} (K : CapSpace ω)
    (hs : 0 ≤ Real.sin t) (hc : 0 ≤ Real.cos t) :
    Real.cos t * horizontalMax K.val ≤ supportValue K.val (t : Real.Angle) ∧
    -Real.sin t * horizontalMin K.val ≤
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  have hcompact := K.val.isCompact.image (by fun_prop : Continuous (fun p : Point ↦ p 0))
  have hne := K.val.nonempty.image (fun p : Point ↦ p 0)
  constructor
  · obtain ⟨p, hp, hpmax⟩ := hcompact.sSup_mem hne
    have hinner := inner_le_supportValue K.val hp (t : Real.Angle)
    have hy := (K.mem_horizontalStrip hp).1
    simp [normalVector, frame, PiLp.inner_apply] at hinner
    change p 0 = horizontalMax K.val at hpmax
    rw [← hpmax]
    nlinarith [mul_nonneg hs hy]
  · obtain ⟨p, hp, hpmin⟩ := hcompact.sInf_mem hne
    have hinner := inner_le_supportValue K.val hp ((t + Real.pi / 2 : ℝ) : Real.Angle)
    have hy := (K.mem_horizontalStrip hp).1
    simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
      -Real.Angle.coe_add] at hinner
    change p 0 = horizontalMin K.val at hpmin
    rw [← hpmin]
    nlinarith [mul_nonneg hc hy]

private theorem mem_niche_rectangle {ω t : ℝ} (K : CapSpace ω)
    (ht : t ∈ Set.Ioo 0 ω) {p : Point}
    (hf : p ∈ capFan ω) (hq : p ∈ innerQuadrant K.val t) :
    horizontalMin K.val < p 0 ∧ p 0 < horizontalMax K.val ∧
      0 ≤ p 1 ∧ p 1 < (horizontalMax K.val - horizontalMin K.val) / 2 := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])
  have hy : 0 ≤ p 1 := by
    have := hf.2
    simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using this
  obtain ⟨h₁, h₂⟩ := hq
  change inner ℝ p (normalVector (t : Real.Angle)) < supportValue K.val _ - 1 at h₁
  change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
    supportValue K.val _ - 1 at h₂
  have hbounds := K.supportValue_horizontal_bounds ht
  have hx : Real.cos t * p 0 + Real.sin t * p 1 <
      Real.cos t * horizontalMax K.val + Real.sin t - 1 := by
    have := h₁.trans_le (sub_le_sub_right hbounds.1 1)
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using this
  have hz : -Real.sin t * p 0 + Real.cos t * p 1 <
      -Real.sin t * horizontalMin K.val + Real.cos t - 1 := by
    have := h₂.trans_le (sub_le_sub_right hbounds.2 1)
    simpa [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
      -Real.Angle.coe_add, mul_comm] using this
  obtain ⟨hl, hr, hh⟩ := niche_coordinate_bounds hc hs (Real.sin_sq_add_cos_sq t)
    (horizontalMin_le_horizontalMax K.val) hy hx hz
  exact ⟨hl, hr, hy, hh⟩

theorem capNiche_subset_rectangle {ω : ℝ} (K : CapSpace ω) :
    capNiche K ⊆ {p | horizontalMin K.val < p 0 ∧ p 0 < horizontalMax K.val ∧
      0 ≤ p 1 ∧ p 1 < (horizontalMax K.val - horizontalMin K.val) / 2} := by
  rintro p ⟨hf, hq⟩
  obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hq
  exact mem_niche_rectangle K ht hf hq

theorem polygonNiche_subset_capNiche (Θ : AngleSet) (K : CapSpace Θ.angle) :
    polygonNiche Θ K ⊆ capNiche K := by
  rintro p ⟨hf, hq⟩
  obtain ⟨t, ht, hq⟩ := Set.mem_iUnion₂.mp hq
  exact ⟨hf, Set.mem_iUnion₂.mpr ⟨t, Θ.interior t ht, hq⟩⟩

private theorem isBounded_coordinate_rectangle (l r h : ℝ) :
    Bornology.IsBounded {p : Point | l < p 0 ∧ p 0 < r ∧ 0 ≤ p 1 ∧ p 1 < h} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|l| + |r| + |h|, ?_⟩
  rintro p ⟨hl, hr, hy, hh⟩
  have hx : |p 0| ≤ |l| + |r| := abs_le.mpr ⟨by
    have := neg_abs_le l
    linarith [abs_nonneg r], by linarith [le_abs_self r, abs_nonneg l]⟩
  have hy' : |p 1| ≤ |h| := by rw [abs_of_nonneg hy]; exact hh.le.trans (le_abs_self h)
  have hx2 := sq_le_sq₀ (abs_nonneg (p 0)) (by positivity : 0 ≤ |l| + |r|) |>.mpr hx
  have hy2 := sq_le_sq₀ (abs_nonneg (p 1)) (abs_nonneg h) |>.mpr hy'
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2 hy2
  nlinarith [mul_nonneg (by positivity : 0 ≤ |l| + |r|) (abs_nonneg h), norm_nonneg p,
    abs_nonneg l, abs_nonneg r, abs_nonneg h, sq_abs h]

private theorem isClosed_capFan (ω : ℝ) : IsClosed (capFan ω) := by
  apply IsClosed.inter
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_le continuous_const (by fun_prop)

private theorem isOpen_innerQuadrant (S : Set Point) (t : ℝ) :
    IsOpen (innerQuadrant S t) := by
  apply IsOpen.inter
  · exact isOpen_lt (by fun_prop) continuous_const
  · exact isOpen_lt (by fun_prop) continuous_const

theorem measurableSet_capNiche {ω : ℝ} (K : CapSpace ω) : MeasurableSet (capNiche K) :=
  (isClosed_capFan ω).measurableSet.inter
    (isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦ isOpen_innerQuadrant K.val t).measurableSet

theorem measurableSet_polygonNiche (Θ : AngleSet) (K : CapSpace Θ.angle) :
    MeasurableSet (polygonNiche Θ K) :=
  (isClosed_capFan Θ.angle).measurableSet.inter
    (isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦ isOpen_innerQuadrant K.val t).measurableSet

private theorem hasNicheRectangleBounds_of_subset {ω : ℝ} (K : CapSpace ω)
    {N : Set Point} (hm : MeasurableSet N) (hN : N ⊆ capNiche K) :
    HasNicheRectangleBounds K.val N := by
  have hb := hN.trans (capNiche_subset_rectangle K)
  refine ⟨hm, hb, (isBounded_coordinate_rectangle _ _ _).subset hb |>.measure_lt_top, ?_⟩
  intro hd
  have he : N = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have := hb hp
    linarith [this.1, this.2.1]
  simp [he, ClassicalResults.area]

private theorem niche_subset_uniform_rectangle {ω R : ℝ} (K : CapSpace ω)
    (hR : ∀ p ∈ (K.val : Set Point), |p 0| ≤ R) :
    capNiche K ⊆ {p | |p 0| ≤ R ∧ 0 ≤ p 1 ∧ p 1 ≤ R} := by
  have hlo : -R ≤ horizontalMin K.val := by
    apply le_csInf (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact (abs_le.mp (hR p hp)).1
  have hhi : horizontalMax K.val ≤ R := by
    apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact (abs_le.mp (hR p hp)).2
  intro p hp
  obtain ⟨hl, hr, hy, hh⟩ := capNiche_subset_rectangle K hp
  exact ⟨abs_le.mpr ⟨hlo.trans hl.le, hr.le.trans hhi⟩, hy, by linarith⟩

theorem niche_uniform_bounds :
    (∀ (ω : ℝ) (K : CapSpace ω),
      HasNicheRectangleBounds (K.val : Set Point) (capNiche K)) ∧
    (∀ (Θ : AngleSet) (K : CapSpace Θ.angle),
      HasNicheRectangleBounds (K.val : Set Point) (polygonNiche Θ K)) ∧
    (∀ (ω : ℕ → ℝ) (K : ∀ i, CapSpace (ω i)) (L : ConvexBody Point),
      Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point) (L : Set Point))
        atTop (𝓝 0) →
      ∃ R : ℝ, 0 ≤ R ∧
        (∀ i, capNiche (K i) ⊆ {p | |p 0| ≤ R ∧ 0 ≤ p 1 ∧ p 1 ≤ R}) ∧
        (∀ i (Θ : AngleSet) (P : CapSpace Θ.angle),
          (P.val : Set Point) = ((K i).val : Set Point) →
          polygonNiche Θ P ⊆ {p | |p 0| ≤ R ∧ 0 ≤ p 1 ∧ p 1 ≤ R})) := by
  refine ⟨fun _ K ↦ hasNicheRectangleBounds_of_subset K (measurableSet_capNiche K) Set.Subset.rfl,
    fun Θ K ↦ hasNicheRectangleBounds_of_subset K (measurableSet_polygonNiche Θ K)
      (polygonNiche_subset_capNiche Θ K), ?_⟩
  intro ω K L hlim
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto _ hlim).exists_norm_le
  obtain ⟨B, hB⟩ := L.isCompact.isBounded.exists_norm_le
  let R := |A| + |B| + 1
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hcarriers : ∀ i p, p ∈ ((K i).val : Set Point) → |p 0| ≤ R := by
    intro i p hp
    have hdist : Metric.hausdorffDist ((K i).val : Set Point) (L : Set Point) < |A| + 1 := by
      have := hA _ (Set.mem_range_self i)
      rw [Real.norm_eq_abs] at this
      exact lt_of_le_of_lt ((le_abs_self _).trans (this.trans (le_abs_self A))) (by linarith)
    obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp hdist
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K i).val.nonempty L.nonempty (K i).val.isCompact.isBounded L.isCompact.isBounded)
    have hnorm : ‖p‖ ≤ R := by
      have ht := norm_add_le (p - q) q
      rw [sub_add_cancel] at ht
      rw [dist_eq_norm] at hpq
      have hb := (hB q hq).trans (le_abs_self B)
      dsimp [R]
      linarith
    have hc : |p 0| ≤ ‖p‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le p 0)
    exact hc.trans hnorm
  refine ⟨R, hR0, fun i ↦ niche_subset_uniform_rectangle (K i) (hcarriers i), ?_⟩
  intro i Θ P hP
  apply (polygonNiche_subset_capNiche Θ P).trans
  apply niche_subset_uniform_rectangle P
  intro p hp
  exact hcarriers i p (hP ▸ hp)

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Geometry.ContactGeometry`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Contact Geometry
-/

public section

noncomputable section

open Filter
open scoped Topology unitInterval

namespace MovingSofa

private theorem inner_tangent_le_fst (K : ConvexBody Point) (t : Real.Angle)
    {p : Point} (hp : p ∈ exposedEdge K t) :
    inner ℝ p (tangentVector t) ≤ inner ℝ (edgeVertices K t).1 (tangentVector t) := by
  rw [inner_edgeVertices_fst_tangent]
  exact le_csSup ((isCompact_exposedEdge K t).image
    (continuous_id.inner continuous_const)).bddAbove ⟨p, hp, rfl⟩

private theorem snd_le_inner_tangent (K : ConvexBody Point) (t : Real.Angle)
    {p : Point} (hp : p ∈ exposedEdge K t) :
    inner ℝ (edgeVertices K t).2 (tangentVector t) ≤ inner ℝ p (tangentVector t) := by
  rw [inner_edgeVertices_snd_tangent]
  exact csInf_le ((isCompact_exposedEdge K t).image
    (continuous_id.inner continuous_const)).bddBelow ⟨p, hp, rfl⟩

private theorem fst_tangent_le_of_mem_exposedEdge_add (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤
      inner ℝ q (tangentVector (t : Real.Angle)) := by
  have hcomp := inner_le_supportValue K (edgeVertices_fst_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqnormal : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  rw [← hqnormal, normalVector_add_real] at hcomp
  simp only [inner_add_right, inner_smul_right] at hcomp
  have hpnormal : inner ℝ (edgeVertices K (t : Real.Angle)).1
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_fst_mem K (t : Real.Angle)).2
  rw [hpnormal] at hcomp
  have hqle := inner_le_supportValue K hq.1 (t : Real.Angle)
  have hsin := Real.sin_pos_of_pos_of_lt_pi hδ.1 (hδ.2.trans (by linarith [Real.pi_pos]))
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hδ.1], hδ.2⟩
  nlinarith

private theorem tendsto_facePoint_right (K : ConvexBody Point) (t : ℝ) (q : ℝ → Point)
    (hq : ∀ s : ℝ, q s ∈ exposedEdge K (s : Real.Angle)) :
    Tendsto q (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) := by
  apply K.isCompact.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun s ↦ (hq s).1)
  intro p hp hcluster
  obtain ⟨s, hqs, hs⟩ := hcluster.exists_seq_tendsto
  have hst : Tendsto s atTop (𝓝 t) := hs.mono_right nhdsWithin_le_nhds
  have hnormal := hqs.inner (𝕜 := ℝ) (continuous_normalVector_real.continuousAt.tendsto.comp hst)
  have hsupport := (continuous_supportValue_real K).continuousAt.tendsto.comp hst
  have hpnormal : inner ℝ p (normalVector (t : Real.Angle)) =
      supportValue K (t : Real.Angle) := by
    apply tendsto_nhds_unique hnormal
    exact hsupport.congr (fun n ↦ (hq (s n)).2.symm)
  have hpface : p ∈ exposedEdge K (t : Real.Angle) := ⟨hp, hpnormal⟩
  have hnear : ∀ᶠ n in atTop, s n ∈ Set.Ioo t (t + Real.pi / 2) :=
    hs.eventually (Ioo_mem_nhdsGT (by linarith [Real.pi_pos]))
  have hle : inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) := by
    apply ge_of_tendsto (hqs.inner tendsto_const_nhds)
    filter_upwards [hnear] with n hn
    have hn' : s n - t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [hn.1, hn.2]
    simpa only [add_sub_cancel, Function.comp_apply] using
      fst_tangent_le_of_mem_exposedEdge_add K t (s n - t) hn'
        (by simpa only [add_sub_cancel, Function.comp_apply] using hq (s n))
  have heq := le_antisymm (inner_tangent_le_fst K (t : Real.Angle) hpface) hle
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle), hpnormal, heq]
  rw [← (edgeVertices_fst_mem K (t : Real.Angle)).2]
  exact inner_normalVector_smul_add_inner_tangentVector_smul _ _

private theorem tangent_le_snd_of_mem_exposedEdge_add (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) := by
  have hcomp := inner_le_supportValue K (edgeVertices_snd_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqnormal : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  rw [← hqnormal, normalVector_add_real] at hcomp
  simp only [inner_add_right, inner_smul_right] at hcomp
  have hpnormal : inner ℝ (edgeVertices K (t : Real.Angle)).2
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_snd_mem K (t : Real.Angle)).2
  rw [hpnormal] at hcomp
  have hqle := inner_le_supportValue K hq.1 (t : Real.Angle)
  have hsin : Real.sin δ < 0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ.2] : 0 < -δ)
      (by linarith [Real.pi_pos, hδ.1] : -δ < Real.pi)
    simpa using h
  have hcos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨hδ.1, by linarith [Real.pi_pos, hδ.2]⟩
  nlinarith

private theorem tendsto_facePoint_left (K : ConvexBody Point) (t : ℝ) (q : ℝ → Point)
    (hq : ∀ s : ℝ, q s ∈ exposedEdge K (s : Real.Angle)) :
    Tendsto q (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  apply K.isCompact.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun s ↦ (hq s).1)
  intro p hp hcluster
  obtain ⟨s, hqs, hs⟩ := hcluster.exists_seq_tendsto
  have hst : Tendsto s atTop (𝓝 t) := hs.mono_right nhdsWithin_le_nhds
  have hnormal := hqs.inner (𝕜 := ℝ) (continuous_normalVector_real.continuousAt.tendsto.comp hst)
  have hsupport := (continuous_supportValue_real K).continuousAt.tendsto.comp hst
  have hpnormal : inner ℝ p (normalVector (t : Real.Angle)) =
      supportValue K (t : Real.Angle) := by
    apply tendsto_nhds_unique hnormal
    exact hsupport.congr (fun n ↦ (hq (s n)).2.symm)
  have hpface : p ∈ exposedEdge K (t : Real.Angle) := ⟨hp, hpnormal⟩
  have hnear : ∀ᶠ n in atTop, s n ∈ Set.Ioo (t - Real.pi / 2) t :=
    hs.eventually (Ioo_mem_nhdsLT (by linarith [Real.pi_pos]))
  have hle : inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) := by
    apply le_of_tendsto (hqs.inner tendsto_const_nhds)
    filter_upwards [hnear] with n hn
    have hn' : s n - t ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ) := by
      constructor <;> linarith [hn.1, hn.2]
    simpa only [add_sub_cancel, Function.comp_apply] using
      tangent_le_snd_of_mem_exposedEdge_add K t (s n - t) hn'
        (by simpa only [add_sub_cancel, Function.comp_apply] using hq (s n))
  have heq := le_antisymm hle (snd_le_inner_tangent K (t : Real.Angle) hpface)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle), hpnormal, heq]
  rw [← (edgeVertices_snd_mem K (t : Real.Angle)).2]
  exact inner_normalVector_smul_add_inner_tangentVector_smul _ _

private theorem intersection_tangent_bounds_right (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤
        (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ ∧
      (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ ≤
        inner ℝ q (tangentVector (t : Real.Angle)) := by
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ.1
    (by linarith [hδ.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos δ := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδ.1, Real.pi_pos], hδ.2⟩).le
  have hp := inner_le_supportValue K (edgeVertices_fst_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqn : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  have hpn : inner ℝ (edgeVertices K (t : Real.Angle)).1
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_fst_mem K (t : Real.Angle)).2
  rw [normalVector_add_real] at hp hqn
  simp only [inner_add_right, inner_smul_right] at hp hqn
  rw [hpn] at hp
  have hqle := mul_le_mul_of_nonneg_left (inner_le_supportValue K hq.1 (t : Real.Angle)) hc
  constructor
  · rw [le_div_iff₀ hs]
    linarith
  · rw [div_le_iff₀ hs]
    linarith

private theorem tendsto_supportingIntersection_right (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) := by
  let r (s : ℝ) := (supportValue K (s : Real.Angle) -
    supportValue K (t : Real.Angle) * Real.cos (s - t)) / Real.sin (s - t)
  have hr : Tendsto r (𝓝[>] t)
      (𝓝 (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)))) := by
    have hq := (tendsto_facePoint_right K t
      (fun s ↦ (edgeVertices K (s : Real.Angle)).1) (fun s ↦ edgeVertices_fst_mem K _)).inner
      (𝕜 := ℝ) (tendsto_const_nhds (x := tangentVector (t : Real.Angle)))
    have hbounds : ∀ᶠ s in 𝓝[>] t,
        inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ≤ r s ∧
        r s ≤ inner ℝ (edgeVertices K (s : Real.Angle)).1 (tangentVector (t : Real.Angle)) := by
      filter_upwards [Ioo_mem_nhdsGT (show t < t + Real.pi / 2 by linarith [Real.pi_pos])]
        with s hs
      have hδ : s - t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        constructor <;> linarith [hs.1, hs.2]
      simpa only [add_sub_cancel, r] using intersection_tangent_bounds_right K t (s - t) hδ
        (by simpa only [add_sub_cancel] using edgeVertices_fst_mem K (s : Real.Angle))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
      (hbounds.mono fun _ h ↦ h.1) (hbounds.mono fun _ h ↦ h.2)
  have hz := (tendsto_const_nhds
    (x := supportValue K (t : Real.Angle) • normalVector (t : Real.Angle))).add (hr.smul
    (tendsto_const_nhds (x := tangentVector (t : Real.Angle))))
  have hpnormal := (edgeVertices_fst_mem K (t : Real.Angle)).2
  change inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) =
    supportValue K (t : Real.Angle) at hpnormal
  have heq := inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K (t :
    Real.Angle)).1 (t : Real.Angle)
  rw [hpnormal] at heq
  simpa only [supportingIntersection, ← Real.Angle.coe_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe, heq, r] using hz

private theorem intersection_tangent_bounds_left (K : ConvexBody Point) (t δ : ℝ)
    (hδ : δ ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ)) {q : Point}
    (hq : q ∈ exposedEdge K ((t + δ : ℝ) : Real.Angle)) :
    (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ ≤
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) ∧
      inner ℝ q (tangentVector (t : Real.Angle)) ≤
        (supportValue K ((t + δ : ℝ) : Real.Angle) -
          supportValue K (t : Real.Angle) * Real.cos δ) / Real.sin δ := by
  have hs : Real.sin δ < 0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ.2] : 0 < -δ)
      (by linarith [hδ.1, Real.pi_pos] : -δ < Real.pi)
    simpa using h
  have hc : 0 ≤ Real.cos δ := (Real.cos_pos_of_mem_Ioo
    ⟨hδ.1, by linarith [hδ.2, Real.pi_pos]⟩).le
  have hp := inner_le_supportValue K (edgeVertices_snd_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hqn : inner ℝ q (normalVector ((t + δ : ℝ) : Real.Angle)) =
      supportValue K ((t + δ : ℝ) : Real.Angle) := hq.2
  have hpn : inner ℝ (edgeVertices K (t : Real.Angle)).2
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) :=
    (edgeVertices_snd_mem K (t : Real.Angle)).2
  rw [normalVector_add_real] at hp hqn
  simp only [inner_add_right, inner_smul_right] at hp hqn
  rw [hpn] at hp
  have hqle := mul_le_mul_of_nonneg_left (inner_le_supportValue K hq.1 (t : Real.Angle)) hc
  constructor
  · rw [div_le_iff_of_neg hs]
    linarith
  · rw [le_div_iff_of_neg hs]
    linarith

private theorem tendsto_supportingIntersection_left_aux (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  let r (s : ℝ) := (supportValue K (s : Real.Angle) -
    supportValue K (t : Real.Angle) * Real.cos (s - t)) / Real.sin (s - t)
  have hr : Tendsto r (𝓝[<] t)
      (𝓝 (inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)))) := by
    have hq := (tendsto_facePoint_left K t
      (fun s ↦ (edgeVertices K (s : Real.Angle)).2) (fun s ↦ edgeVertices_snd_mem K _)).inner
      (𝕜 := ℝ) (tendsto_const_nhds (x := tangentVector (t : Real.Angle)))
    have hbounds : ∀ᶠ s in 𝓝[<] t,
        r s ≤ inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) ∧
        inner ℝ (edgeVertices K (s : Real.Angle)).2 (tangentVector (t : Real.Angle)) ≤ r s := by
      filter_upwards [Ioo_mem_nhdsLT (show t - Real.pi / 2 < t by linarith [Real.pi_pos])]
        with s hs
      have hδ : s - t ∈ Set.Ioo (-(Real.pi / 2)) (0 : ℝ) := by
        constructor <;> linarith [hs.1, hs.2]
      simpa only [add_sub_cancel, r] using intersection_tangent_bounds_left K t (s - t) hδ
        (by simpa only [add_sub_cancel] using edgeVertices_snd_mem K (s : Real.Angle))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hq tendsto_const_nhds
      (hbounds.mono fun _ h ↦ h.2) (hbounds.mono fun _ h ↦ h.1)
  have hz := (tendsto_const_nhds
    (x := supportValue K (t : Real.Angle) • normalVector (t : Real.Angle))).add (hr.smul
    (tendsto_const_nhds (x := tangentVector (t : Real.Angle))))
  have hpnormal := (edgeVertices_snd_mem K (t : Real.Angle)).2
  change inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
    supportValue K (t : Real.Angle) at hpnormal
  have heq := inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K (t :
    Real.Angle)).2 (t : Real.Angle)
  rw [hpnormal] at heq
  simpa only [supportingIntersection, ← Real.Angle.coe_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe, heq, r] using hz

/-- Both face endpoints and the supporting intersections have the stated one-sided limits. -/
theorem contact_oneSided_limits (K : ConvexBody Point) (t : ℝ) :
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1)
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) ∧
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).2)
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) ∧
    Tendsto (fun s : ℝ ↦ supportingIntersection K (t : Real.Angle) (s : Real.Angle))
      (𝓝[>] t) (𝓝 (edgeVertices K (t : Real.Angle)).1) ∧
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1)
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) ∧
    Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).2)
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) ∧
    Tendsto (fun s : ℝ ↦ supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (𝓝[<] t) (𝓝 (edgeVertices K (t : Real.Angle)).2) := by
  refine ⟨tendsto_facePoint_right K t _ (fun s ↦ edgeVertices_fst_mem K _),
    tendsto_facePoint_right K t _ (fun s ↦ edgeVertices_snd_mem K _),
    tendsto_supportingIntersection_right K t,
    tendsto_facePoint_left K t _ (fun s ↦ edgeVertices_fst_mem K _),
    tendsto_facePoint_left K t _ (fun s ↦ edgeVertices_snd_mem K _), ?_⟩
  apply (tendsto_supportingIntersection_left_aux K t).congr'
  filter_upwards [Ioo_mem_nhdsLT (show t - Real.pi / 2 < t by linarith [Real.pi_pos])]
    with s hs
  apply supportingIntersection_comm
  have hpos : 0 < Real.sin (t - s) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hs.2]) (by linarith [hs.1, Real.pi_pos])
  rw [show s - t = -(t - s) by ring, Real.sin_neg]
  exact neg_ne_zero.mpr hpos.ne'

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.Stieltjes.ConvexBoundary`.
* `Analysis.SurfaceMeasure.Polygon`.
* `Analysis.SurfaceMeasure.BoundaryLimit`.
* `Analysis.SurfaceMeasure.DiscreteBounds`.
* `Analysis.SurfaceMeasure.Integrals`.
* `Analysis.SurfaceMeasure.VertexBoundary`.
* `Analysis.SurfaceMeasure.AngularDensity`.
* `Analysis.SurfaceMeasure.FrameProducts`.
* `Analysis.SurfaceMeasure.Boundary`.
* `Analysis.SurfaceMeasure.Linearity`.
* `Analysis.SurfaceMeasure.OppositeDensity`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Convex Boundary
-/

public section

noncomputable section

open scoped Topology

namespace MovingSofa

/-- Each coordinate of the positive vertex is right-continuous and has bounded
variation on its closed interval domain. -/
theorem exists_positiveVertex_intervalBV (K : ConvexBody Point) {a b : ℝ} (hab : a ≤ b) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      ∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i := by
  have hv : BoundedVariationOn
      (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) Set.univ := by
    exact ne_top_of_le_ne_top (positiveVertex_boundedVariation K a b hab)
      (eVariationOn.comp_le_of_monotoneOn
        (fun t : ℝ ↦ (edgeVertices K (t : Real.Angle)).1)
        (s := Set.Icc a b) (t := Set.univ) (fun t : Set.Icc a b ↦ (t : ℝ))
        (fun _ _ _ _ h ↦ h) (fun t _ ↦ t.property))
  have hc (i : Fin 2) : IsIntervalBoundedVariation a b
      (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) := by
    change BoundedVariationOn ((fun p : Point ↦ p i) ∘
      fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) Set.univ
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).lipschitzWith.comp_boundedVariationOn
      (g := fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) hv
  have hr (i : Fin 2) (t : Set.Icc a b) : ContinuousWithinAt
      (fun s : Set.Icc a b ↦ (edgeVertices K ((s : ℝ) : Real.Angle)).1 i)
      (Set.Ici t) t := by
    have h : ContinuousWithinAt (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1)
        (Set.Ici (t : ℝ)) (t : ℝ) :=
      continuousWithinAt_Ioi_iff_Ici.mp (contact_oneSided_limits K (t : ℝ)).1
    have hcomp : ContinuousWithinAt
        (fun s : Set.Icc a b ↦ (edgeVertices K ((s : ℝ) : Real.Angle)).1)
        (Set.Ici t) t := h.comp
      (show ContinuousWithinAt (fun s : Set.Icc a b ↦ (s : ℝ)) (Set.Ici t) t from
        continuous_subtype_val.continuousWithinAt) (fun _ hy ↦ hy)
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.continuousAt
      |>.comp_continuousWithinAt hcomp
  exact ⟨fun i ↦ ⟨_, hc i, hr i⟩, fun _ _ ↦ rfl⟩

/-- Each coordinate of the positive vertex is measurable on the closed parameter interval,
being the difference of two monotone functions by bounded variation. -/
theorem measurable_positiveVertex_coordinate (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Icc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab
  have hfun : (fun t : Set.Icc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i) =
      (f i).toFun := by
    funext t
    exact (hf i t).symm
  have hbv : LocallyBoundedVariationOn (f i).toFun (Set.univ : Set (Set.Icc a b)) :=
    (f i).boundedVariation.locallyBoundedVariationOn
  obtain ⟨p, q, hp, hq, hpq⟩ := hbv.exists_monotoneOn_sub_monotoneOn
  rw [hfun, hpq]
  exact (monotoneOn_univ.mp hp).measurable.sub (monotoneOn_univ.mp hq).measurable

/-- Each coordinate of the positive vertex is measurable on the half-open parameter
interval. -/
theorem measurable_positiveVertex_coordinate_Ioc (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
  have hpos := measurable_positiveVertex_coordinate K hab i
  have hmem (t : Set.Ioc a b) : (t : ℝ) ∈ Set.Icc a b := ⟨t.property.1.le, t.property.2⟩
  have hcont : Continuous fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b) :=
    Continuous.subtype_mk continuous_subtype_val hmem
  have hcomp : Measurable
      ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
        fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b)) :=
    hpos.comp hcont.measurable
  have hfun : ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
      fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b)) =
      fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
    funext t
    rfl
  rwa [hfun] at hcomp

/-- Each coordinate of the negative vertex is measurable on the half-open parameter interval,
being the pointwise left limit of the positive vertex. -/
theorem measurable_negativeVertex_coordinate (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).2 i := by
  have hpos := measurable_positiveVertex_coordinate K hab i
  have hmem (n : ℕ) (t : Set.Ioc a b) :
      max a ((t : ℝ) - 1 / (n + 1 : ℝ)) ∈ Set.Icc a b := by
    refine ⟨le_max_left _ _, max_le hab ?_⟩
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith [t.property.2]
  set g : ℕ → Set.Ioc a b → ℝ := fun n t ↦
    (edgeVertices K ((max a ((t : ℝ) - 1 / (n + 1 : ℝ)) : ℝ) : Real.Angle)).1 i
  have hgmeas (n : ℕ) : Measurable (g n) := by
    have hcont : Continuous fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
        hmem n t⟩ : Set.Icc a b) :=
      Continuous.subtype_mk
        (continuous_const.max (continuous_subtype_val.sub continuous_const)) (hmem n)
    have hcomp : Measurable
        ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
          fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
            hmem n t⟩ : Set.Icc a b)) :=
      hpos.comp hcont.measurable
    have hfun :
        ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
          fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
            hmem n t⟩ : Set.Icc a b)) = g n := by
      funext t
      rfl
    rwa [hfun] at hcomp
  refine measurable_of_tendsto_metrizable hgmeas (tendsto_pi_nhds.2 fun t ↦ ?_)
  have hta : a < (t : ℝ) := t.property.1
  have hlim := (contact_oneSided_limits K (t : ℝ)).2.2.2.1
  have hlimi : Filter.Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1 i)
      (𝓝[<] (t : ℝ)) (𝓝 ((edgeVertices K ((t : ℝ) : Real.Angle)).2 i)) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.tendsto _).comp hlim
  refine hlimi.comp ?_
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h0 : Filter.Tendsto (fun n : ℕ ↦ (t : ℝ) - 1 / (n + 1 : ℝ))
        Filter.atTop (𝓝 (t : ℝ)) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_sub ((t : ℝ))
    have hconst : Filter.Tendsto (fun _ : ℕ ↦ a) Filter.atTop (𝓝 a) := tendsto_const_nhds
    have h1 := hconst.max h0
    rwa [max_eq_right hta.le] at h1
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / ((t : ℝ) - a))
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hpos : (0 : ℝ) < (t : ℝ) - a := by linarith
    have hNle : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hlt : 1 / (n + 1 : ℝ) < (t : ℝ) - a := by
      have h1 : 1 / ((t : ℝ) - a) < (n + 1 : ℝ) := by linarith
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℝ))]
      rw [div_lt_iff₀ hpos] at h1
      linarith
    have hmaxeq : max a ((t : ℝ) - 1 / (n + 1 : ℝ)) = (t : ℝ) - 1 / (n + 1 : ℝ) :=
      max_eq_right (by linarith)
    rw [Set.mem_Iio, hmaxeq]
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Polygon
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private def quarterTurn (p : Point) : Point := !₂[-p 1, p 0]

private theorem quarterTurn_ne_zero {p : Point} (hp : p ≠ 0) : quarterTurn p ≠ 0 := by
  intro h
  apply hp
  ext i
  fin_cases i
  · exact congrFun (congrArg WithLp.ofLp h) 1
  · simpa [quarterTurn] using congrFun (congrArg WithLp.ofLp h) 0

private theorem inner_quarterTurn (p : Point) : inner ℝ p (quarterTurn p) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [quarterTurn, dotProduct, Fin.sum_univ_two]
  ring

private theorem inner_normalVector_vectorNormalAngle_quarterTurn {p : Point} (hp : p ≠ 0) :
    inner ℝ p (normalVector (vectorNormalAngle (quarterTurn p))) = 0 := by
  rw [normalVector_vectorNormalAngle (quarterTurn_ne_zero hp), inner_smul_right,
    inner_quarterTurn, mul_zero]

/-- A nonzero planar direction has only finitely many perpendicular angular normals. -/
theorem finite_orthogonalNormal_angles {p : Point} (hp : p ≠ 0) :
    Set.Finite {t : Real.Angle | inner ℝ p (normalVector t) = 0} := by
  let t₀ := vectorNormalAngle (quarterTurn p)
  apply Set.Finite.subset
    ((Set.finite_singleton (t₀ + (Real.pi : Real.Angle))).insert t₀)
  intro t ht
  have h := normalVector_eq_or_eq_add_pi_of_orthogonal hp ht
    (inner_normalVector_vectorNormalAngle_quarterTurn hp)
  rcases h with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))

/-- The possible normals perpendicular to differences of points in a finite set are finite. -/
theorem finite_pairDifferenceNormal_angles (V : Finset Point) :
    Set.Finite {t : Real.Angle | ∃ p ∈ V, ∃ q ∈ V,
      p ≠ q ∧ inner ℝ (p - q) (normalVector t) = 0} := by
  classical
  let N : Point → Point → Set Real.Angle := fun p q ↦
    if h : p = q then ∅ else {t | inner ℝ (p - q) (normalVector t) = 0}
  have hN (p q : Point) : Set.Finite (N p q) := by
    by_cases h : p = q
    · simp [N, h]
    · simpa [N, h] using finite_orthogonalNormal_angles (sub_ne_zero.mpr h)
  apply Set.Finite.subset (V.finite_toSet.biUnion fun p _ ↦
    V.finite_toSet.biUnion fun q _ ↦ hN p q)
  rintro t ⟨p, hp, q, hq, hpq, ht⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨p, hp, Set.mem_iUnion₂.mpr ⟨q, hq, ?_⟩⟩
  simp [N, hpq, ht]

/-- The support edge of a convex body is an exposed face. -/
theorem isExposed_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsExposed ℝ (K : Set Point) (exposedEdge K t) := by
  intro _
  refine ⟨innerSL ℝ (normalVector t), ?_⟩
  ext p
  simp only [Set.mem_ofPred_eq, innerSL_apply_apply, real_inner_comm]
  constructor
  · intro hp
    refine ⟨hp.1, fun q hq ↦ ?_⟩
    rw [hp.2]
    exact inner_le_supportValue K hq t
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact hmax q hq

private theorem isExposed_singleton_edgeVertices_fst (K : ConvexBody Point)
    (t : Real.Angle) :
    IsExposed ℝ (exposedEdge K t) {(edgeVertices K t).1} := by
  intro _
  refine ⟨innerSL ℝ (tangentVector t), ?_⟩
  ext p
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, innerSL_apply_apply,
    real_inner_comm]
  constructor
  · rintro rfl
    refine ⟨edgeVertices_fst_mem K t, fun q hq ↦ ?_⟩
    rw [inner_edgeVertices_fst_tangent]
    exact le_csSup ((isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const)).bddAbove ⟨q, hq, rfl⟩
  · rintro ⟨hp, hmax⟩
    have htangent : inner ℝ p (tangentVector t) =
        inner ℝ (edgeVertices K t).1 (tangentVector t) := by
      apply le_antisymm
      · rw [inner_edgeVertices_fst_tangent]
        exact le_csSup ((isCompact_exposedEdge K t).image
          (continuous_id.inner continuous_const)).bddAbove ⟨p, hp, rfl⟩
      · exact hmax _ (edgeVertices_fst_mem K t)
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K t).1 t,
      hp.2, (edgeVertices_fst_mem K t).2, htangent]

private theorem isExposed_singleton_edgeVertices_snd (K : ConvexBody Point)
    (t : Real.Angle) :
    IsExposed ℝ (exposedEdge K t) {(edgeVertices K t).2} := by
  intro _
  refine ⟨innerSL ℝ (-tangentVector t), ?_⟩
  ext p
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, innerSL_apply_apply,
    real_inner_comm, inner_neg_left]
  constructor
  · rintro rfl
    refine ⟨edgeVertices_snd_mem K t, fun q hq ↦ neg_le_neg ?_⟩
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le ((isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const)).bddBelow ⟨q, hq, rfl⟩
  · rintro ⟨hp, hmax⟩
    have htangent : inner ℝ p (tangentVector t) =
        inner ℝ (edgeVertices K t).2 (tangentVector t) := by
      apply le_antisymm
      · exact neg_le_neg_iff.mp (hmax _ (edgeVertices_snd_mem K t))
      · rw [inner_edgeVertices_snd_tangent]
        exact csInf_le ((isCompact_exposedEdge K t).image
          (continuous_id.inner continuous_const)).bddBelow ⟨p, hp, rfl⟩
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K t).2 t,
      hp.2, (edgeVertices_snd_mem K t).2, htangent]

/-- Both endpoints of a polygon's exposed edge belong to its finite generating set. -/
theorem edgeVertices_mem_of_eq_convexHull (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ V ∧ (edgeVertices K t).2 ∈ V := by
  have hedge := (isExposed_exposedEdge K t).isExtreme
  constructor
  · have hext : (edgeVertices K t).1 ∈ Set.extremePoints ℝ (K : Set Point) :=
      (hedge.trans (isExposed_singleton_edgeVertices_fst K t).isExtreme).mem_extremePoints
    rw [hKV] at hext
    exact Finset.mem_coe.mp (extremePoints_convexHull_subset hext)
  · have hext : (edgeVertices K t).2 ∈ Set.extremePoints ℝ (K : Set Point) :=
      (hedge.trans (isExposed_singleton_edgeVertices_snd K t).isExtreme).mem_extremePoints
    rw [hKV] at hext
    exact Finset.mem_coe.mp (extremePoints_convexHull_subset hext)

/-- Every proper edge normal of a finite convex hull is one of finitely many pair normals. -/
theorem finite_properEdgeNormal_angles (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    Set.Finite {t : Real.Angle | (edgeVertices K t).1 ≠ (edgeVertices K t).2} := by
  apply (finite_pairDifferenceNormal_angles V).subset
  intro t ht
  refine ⟨(edgeVertices K t).1, (edgeVertices_mem_of_eq_convexHull K V hKV t).1,
    (edgeVertices K t).2, (edgeVertices_mem_of_eq_convexHull K V hKV t).2, ht, ?_⟩
  rw [inner_sub_left, (edgeVertices_fst_mem K t).2, (edgeVertices_snd_mem K t).2,
    sub_self]

private theorem continuousAt_positiveVertex_of_eq_negativeVertex (K : ConvexBody Point)
    (t : ℝ) (ht : (edgeVertices K (t : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).2) :
    ContinuousAt (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1) t := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · change Tendsto _ (𝓝[<] t) _
    simpa only [ht] using (contact_oneSided_limits K t).2.2.2.1
  · change Tendsto _ (𝓝[>] t) _
    exact (contact_oneSided_limits K t).1

/-- Away from a proper-edge normal, the positive vertex of a finite convex hull is locally
constant. -/
theorem eventuallyEq_positiveVertex_of_eq_convexHull (K : ConvexBody Point)
    (V : Finset Point) (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (t : ℝ) (ht : (edgeVertices K (t : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).2) :
    ∀ᶠ s : ℝ in 𝓝 t, (edgeVertices K (s : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).1 := by
  classical
  let v := (edgeVertices K (t : Real.Angle)).1
  let W : Set Point := (↑(V.erase v) : Set Point)
  have hvV : v ∈ V := (edgeVertices_mem_of_eq_convexHull K V hKV _).1
  have hvW : v ∈ Wᶜ := by simp [W, hvV]
  have hopen : IsOpen Wᶜ := (V.erase v).finite_toSet.isClosed.isOpen_compl
  have hnhds : Wᶜ ∈ 𝓝 v := hopen.mem_nhds hvW
  have htend :=
    (continuousAt_positiveVertex_of_eq_negativeVertex K t ht).eventually hnhds
  exact htend.mono (by
    intro s hs
    have hsV : (edgeVertices K (s : Real.Angle)).1 ∈ V :=
      (edgeVertices_mem_of_eq_convexHull K V hKV _).1
    by_contra hne
    have hnev : (edgeVertices K (s : Real.Angle)).1 ≠ v := by simpa [v] using hne
    exact hs (by simp [W, hsV, hnev]))

/-- For a two-dimensional finite convex hull, surface measure is supported on its finite set of
proper-edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (hint : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hmeas : MeasurableSet Nᶜ := hNfinite.measurableSet.compl
  have hface := (surfaceAreaMeasure_face_union K).2.2.2.2 Nᶜ hmeas (Or.inl hint)
  have hunion : (⋃ t ∈ Nᶜ, exposedEdge K t) ⊆ (V : Set Point) := by
    intro p hp
    obtain ⟨t, htN, hpt⟩ := Set.mem_iUnion₂.mp hp
    have ht : (edgeVertices K t).1 = (edgeVertices K t).2 := by
      simpa only [N, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using htN
    have hp' : p = (edgeVertices K t).1 := by
      rw [exposedEdge_eq_segment_edgeVertices, ← ht] at hpt
      simpa using hpt
    rw [hp']
    exact (edgeVertices_mem_of_eq_convexHull K V hKV t).1
  rw [show {t | (edgeVertices K t).1 = (edgeVertices K t).2} = Nᶜ by
    ext t
    simp [N], hface]
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact measure_mono_null hunion
    (V.finite_toSet.measure_zero (Measure.hausdorffMeasure 1))

/-- Surface measure of any finite convex hull, including a point or segment, is supported on its
finite set of proper-edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  by_cases hsub : (K : Set Point).Subsingleton
  · rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hsub]
    simp
  by_cases hint : (interior (K : Set Point)).Nonempty
  · exact surfaceAreaMeasure_compl_properEdgeNormals_eq_zero K V hKV hint
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  have hproper (u : Real.Angle)
      (hu : inner ℝ (d.2.1 - d.1) (normalVector u) = 0) :
      (edgeVertices K u).1 ≠ (edgeVertices K u).2 := by
    intro heq
    have hedge := exposedEdge_eq_segment_of_orthogonal K d hd u hu
    have hsingle : (K : Set Point).Subsingleton := by
      rw [← hedge, exposedEdge_eq_segment_edgeVertices, heq]
      simp
    exact hsub hsingle
  have hpi : inner ℝ (d.2.1 - d.1)
      (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    have hn : normalVector (d.2.2 + (Real.pi : Real.Angle)) =
        -normalVector d.2.2 := by
      induction d.2.2 using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hn, inner_neg_right, hd.2.2, neg_zero]
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  simp [hproper d.2.2 hd.2.2, hproper _ hpi]

/-- Surface measure is carried by the proper edge normals as soon as these are finitely many
and the degenerate faces lie in a one-dimensional null set. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_carrier
    (K : ConvexBody Point)
    (hN : {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}.Finite)
    (V : Set Point) (hV : Measure.hausdorffMeasure 1 V = 0)
    (hcarrier : (⋃ t ∈ {t | (edgeVertices K t).1 = (edgeVertices K t).2},
      exposedEdge K t) ⊆ V) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hset : {t | (edgeVertices K t).1 = (edgeVertices K t).2} = Nᶜ := by
    ext t
    simp [N]
  by_cases hsub : (K : Set Point).Subsingleton
  · rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hsub]
    simp
  by_cases hint : (interior (K : Set Point)).Nonempty
  · rw [hset, (surfaceAreaMeasure_face_union K).2.2.2.2 Nᶜ
      hN.measurableSet.compl (Or.inl hint)]
    exact measure_mono_null (by simpa only [hset] using hcarrier) hV
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  have hproper (u : Real.Angle)
      (hu : inner ℝ (d.2.1 - d.1) (normalVector u) = 0) :
      (edgeVertices K u).1 ≠ (edgeVertices K u).2 := by
    intro heq
    have hedge := exposedEdge_eq_segment_of_orthogonal K d hd u hu
    have hsingle : (K : Set Point).Subsingleton := by
      rw [← hedge, exposedEdge_eq_segment_edgeVertices, heq]
      simp
    exact hsub hsingle
  have hpi : inner ℝ (d.2.1 - d.1)
      (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    rw [normalVector_add_pi_angle, inner_neg_right, hd.2.2, neg_zero]
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  simp [hproper d.2.2 hd.2.2, hproper _ hpi]

/-- The surface integral of an arbitrary integrand over a finite convex hull is the sum of its
proper-edge atoms, including the point and segment cases. No regularity of the integrand is
needed: the measure is carried by a finite set. -/
theorem integral_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (φ : Real.Angle → ℝ) (E : Set Real.Angle) (hE : MeasurableSet E) :
    ∫ t in E, φ t ∂surfaceAreaMeasure K =
      Finset.sum ((finite_properEdgeNormal_angles K V hKV).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * φ t) := by
  classical
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hae : ∀ᵐ t ∂surfaceAreaMeasure K, t ∈ N := by
    rw [ae_iff]
    simpa only [N, Set.mem_ofPred_eq, not_ne_iff] using
      surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull K V hKV
  have hrestrict : (surfaceAreaMeasure K).restrict N = surfaceAreaMeasure K :=
    Measure.restrict_eq_self_of_ae_mem hae
  let _ := (surfaceAreaMeasure_face_union K).1
  have hEN : E ∩ N = ↑(hNfinite.inter_of_left E).toFinset := by
    ext t
    simp [N, and_comm]
  calc
    ∫ t in E, φ t ∂surfaceAreaMeasure K =
        ∫ t in E, φ t ∂(surfaceAreaMeasure K).restrict N := by rw [hrestrict]
    _ = ∫ t in E ∩ N, φ t ∂surfaceAreaMeasure K := by
      rw [Measure.restrict_restrict hE]
    _ = _ := by
      rw [hEN]
      exact MeasureTheory.setIntegral_finset _
        (μ := surfaceAreaMeasure K) (f := φ) IntegrableOn.finset

/-- The coordinate tangent integral of a finite convex hull is the sum of its proper-edge atoms,
including the point and segment cases. -/
theorem integral_tangentCoordinate_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (i : Fin 2) (E : Set Real.Angle) (hE : MeasurableSet E) :
    ∫ t in E, tangentVector t i ∂surfaceAreaMeasure K =
      Finset.sum ((finite_properEdgeNormal_angles K V hKV).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * tangentVector t i) :=
  integral_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV
    (fun t ↦ tangentVector t i) E hE

/-- On a real interval, the coordinate Stieltjes measure of a polygon's positive vertex is
supported at proper-edge normals (apart from the excluded left endpoint). -/
theorem intervalStieltjesMeasure_variation_eq_zero_off_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i) (i : Fin 2) :
    (intervalStieltjesMeasure (f i)).variation
      {t | a < (t : ℝ) ∧ (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 =
        (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2} = 0 := by
  let T : Set (Set.Icc a b) :=
    {t | a < (t : ℝ) ∧ (edgeVertices K ((t : ℝ) : Real.Angle)).1 =
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  change (f i).boundedVariation.vectorMeasure.variation T = 0
  apply measure_null_of_locally_null T
  intro x hx
  have hconst := eventuallyEq_positiveVertex_of_eq_convexHull K V hKV (x : ℝ) hx.2
  have hconst' : (f i).toFun =ᶠ[𝓝 x] fun _ ↦ (f i).toFun x := by
    filter_upwards [continuousAt_subtype_val.eventually hconst] with y hy
    rw [hf i y, hf i x, hy]
  obtain ⟨U, hU, hUzero⟩ :=
    BoundedVariationOn.exists_nhds_variation_vectorMeasure_eq_zero_of_eventuallyEq_const
    hab (f i).boundedVariation (f i).right_continuous x hx.1 hconst'
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUzero⟩

/-- The left limit of a positive-vertex coordinate at a noninitial parameter is the corresponding
coordinate of the negative vertex. -/
theorem leftLim_positiveVertex_coordinate
    (K : ConvexBody Point) {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (t : Set.Icc a b) (ht : a < (t : ℝ)) :
    Function.leftLim (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2 i := by
  have hab : a < b := ht.trans_le t.property.2
  let _ : Fact (a ≤ b) := ⟨hab.le⟩
  let _ : Nontrivial (Set.Icc a b) :=
    ⟨⟨⟨a, le_rfl, hab.le⟩, ⟨b, hab.le, le_rfl⟩, fun h ↦
      hab.ne (congrArg Subtype.val h)⟩⟩
  have hcoe : Tendsto (fun s : Set.Icc a b ↦ (s : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
    rw [nhdsWithin_subtype, Set.image_subtype_val_Icc_Iio,
      nhdsWithin_Ico_eq_nhdsLT ht]
    exact tendsto_comap
  have hcontact := ((contact_oneSided_limits K (t : ℝ)).2.2.2.1).comp hcoe
  have hcoord := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.continuousAt
    |>.tendsto.comp hcontact
  have hfleft := (f i).boundedVariation.tendsto_leftLim t
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨⊥, ht⟩
  apply tendsto_nhds_unique hfleft
  apply hcoord.congr
  intro s
  simpa [Function.comp_apply] using (hf i s).symm

/-- Each noninitial Stieltjes atom of a positive-vertex coordinate is the corresponding
coordinate of the tangent-weighted surface-measure atom. -/
theorem intervalStieltjesMeasure_singleton_positiveVertex
    (K : ConvexBody Point) {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (t : Set.Icc a b) (ht : a < (t : ℝ)) :
    intervalStieltjesMeasure (f i) {t} =
      (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
        tangentVector ((t : ℝ) : Real.Angle) i := by
  rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
    (f i).right_continuous t |>.rightLim_eq,
    leftLim_positiveVertex_coordinate K f hf i t ht, hf]
  have h := congrArg (fun p : Point ↦ p i)
    (surfaceAreaMeasure_atom_length K ((t : ℝ) : Real.Angle)).2.2
  simpa [PiLp.smul_apply] using congrArg (fun z : ℝ ↦
    z - (edgeVertices K ((t : ℝ) : Real.Angle)).2 i) h

/-- A proper-edge normal has only finitely many lifts in a half-open interval of length at most one
full turn. -/
theorem finite_properEdgeNormal_lifts (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) :
    Set.Finite {t : Set.Icc a b | a < (t : ℝ) ∧
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2} := by
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let N : Set Real.Angle :=
    {u | (edgeVertices K u).1 ≠ (edgeVertices K u).2}
  let c : Set.Icc a b → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let _ : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  change S.Finite
  apply Set.Finite.of_finite_image (f := c)
  · apply (finite_properEdgeNormal_angles K V hKV).subset
    rintro _ ⟨t, ht, rfl⟩
    exact ht.2
  · intro x hx y hy hxy
    apply Subtype.ext
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := 2 * Real.pi) ⟨hx.1, x.property.2.trans hturn⟩
      ⟨hy.1, y.property.2.trans hturn⟩).mp
    change ((x : ℝ) : Real.Angle) = ((y : ℝ) : Real.Angle)
    simpa [c] using hxy

/-- On a polygon, every measurable noninitial set has Stieltjes mass equal to the finite sum of
its proper-edge atoms. -/
theorem intervalStieltjesMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesMeasure (f i) E =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K
          {(((t : Set.Icc a b) : ℝ) : Real.Angle)}).toReal *
            tangentVector (((t : Set.Icc a b) : ℝ) : Real.Angle) i) := by
  classical
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let T : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 =
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let μ := intervalStieltjesMeasure (f i)
  change μ E = _
  have hSfinite : S.Finite := finite_properEdgeNormal_lifts K V hKV hturn
  have hTzero : μ.variation T = 0 :=
    intervalStieltjesMeasure_variation_eq_zero_off_properEdgeNormals K V hKV hab f hf i
  have hdiffsub : E \ S ⊆ T := by
    intro t ht
    exact ⟨hEa t ht.1, not_ne_iff.mp (fun hne ↦ ht.2 ⟨hEa t ht.1, hne⟩)⟩
  have hdiffzero : μ (E \ S) = 0 := by
    rw [← enorm_eq_zero, ← le_zero_iff]
    exact (μ.enorm_measure_le_variation (E \ S)).trans
      (by rw [measure_mono_null hdiffsub hTzero])
  have hsplit : E = S ∩ E ∪ (E \ S) := by
    ext t
    constructor
    · intro ht
      by_cases htS : t ∈ S
      · exact Or.inl ⟨htS, ht⟩
      · exact Or.inr ⟨ht, htS⟩
    · rintro (ht | ht)
      · exact ht.2
      · exact ht.1
  have hfinite : S ∩ E =
      ↑((hSfinite.inter_of_left E).toFinset) := by
    exact (hSfinite.inter_of_left E).coe_toFinset.symm
  have hES : MeasurableSet (S ∩ E) := hSfinite.measurableSet.inter hE
  have hEdiff : MeasurableSet (E \ S) := hE.diff hSfinite.measurableSet
  have hdisj : Disjoint (S ∩ E) (E \ S) :=
    Set.disjoint_of_subset_left Set.inter_subset_left Set.disjoint_sdiff_right
  have hreduce : μ E = μ (S ∩ E) := calc
    μ E = μ (S ∩ E ∪ (E \ S)) := congrArg μ hsplit
    _ = μ (S ∩ E) + μ (E \ S) := μ.of_union hdisj hES hEdiff
    _ = μ (S ∩ E) := by rw [hdiffzero, add_zero]
  rw [hreduce]
  conv_lhs => rw [hfinite]
  let F := (hSfinite.inter_of_left E).toFinset
  have hU : (↑F : Set (Set.Icc a b)) = ⋃ t ∈ F, {t} := by
    ext t
    simp only [Finset.mem_coe, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨u, hu, _, rfl⟩
      exact hu
  rw [hU, μ.of_biUnion_finset (by
    intro x hx y hy hxy
    simpa [Set.disjoint_singleton] using hxy) (by simp)]
  calc
    Finset.sum F (fun t ↦ μ {t}) =
        Finset.sum F (fun t ↦
          (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
            tangentVector ((t : ℝ) : Real.Angle) i) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ∈ S ∩ E := by simpa [F] using ht
      exact intervalStieltjesMeasure_singleton_positiveVertex K f hf i t
        (by simpa [S] using ht'.1.1)
    _ = _ := by
      exact congrArg (fun G : Finset (Set.Icc a b) ↦
        Finset.sum G (fun t ↦
          (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
            tangentVector ((t : ℝ) : Real.Angle) i)) (by
              apply Finset.ext
              intro t
              simp [F, S])

/-- The surface integral of an arbitrary integrand over the angular image of a measurable
interval set, as a finite sum indexed by the angular lifts carrying a proper edge. The left
endpoint `a` is excluded from `E` so that each angle has at most one lift in `E`. -/
theorem integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) (φ : Real.Angle → ℝ)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
      φ u ∂surfaceAreaMeasure K) =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {((t : ℝ) : Real.Angle)} *
          φ ((t : ℝ) : Real.Angle)) := by
  classical
  let c : Set.Icc a b → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  have hinj : Set.InjOn c E := by
    intro x hx y hy hxy
    apply Subtype.ext
    let _ : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := 2 * Real.pi) ⟨hEa x hx, x.property.2.trans hturn⟩
      ⟨hEa y hy, y.property.2.trans hturn⟩).mp
    change c x = c y
    exact hxy
  have hAmeas : MeasurableSet (c '' E) :=
    hE.image_of_continuousOn_injOn
      ((Real.Angle.continuous_coe : Continuous fun x : ℝ ↦ (x : Real.Angle)).comp
        continuous_subtype_val).continuousOn hinj
  rw [integral_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV φ (c '' E) hAmeas]
  let F := ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
  let G := ((finite_properEdgeNormal_angles K V hKV).inter_of_left (c '' E)).toFinset
  have hG : G = F.image c := by
    ext u
    simp only [G, F, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_image,
      Finset.mem_image]
    constructor
    · rintro ⟨huN, t, htE, rfl⟩
      exact ⟨t, ⟨⟨hEa t htE, huN⟩, htE⟩, rfl⟩
    · rintro ⟨t, ⟨⟨hta, htN⟩, htE⟩, rfl⟩
      exact ⟨htN, t, htE, rfl⟩
  change Finset.sum G (fun u ↦ (surfaceAreaMeasure K).real {u} * φ u) = _
  rw [hG, Finset.sum_image]
  · intro x hx y hy hxy
    have hx' : x ∈ S ∩ E := by
      change (a < (x : ℝ) ∧ (edgeVertices K ((x : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((x : ℝ) : Real.Angle)).2) ∧ x ∈ E
      simpa [F] using hx
    have hy' : y ∈ S ∩ E := by
      change (a < (y : ℝ) ∧ (edgeVertices K ((y : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((y : ℝ) : Real.Angle)).2) ∧ y ∈ E
      simpa [F] using hy
    exact hinj hx'.2 hy'.2 hxy

/-- The tangent-coordinate surface integral over the angular image of a measurable interval set is
the same finite proper-edge sum as the positive-vertex Stieltjes measure. -/
theorem integral_tangentCoordinate_image_eq_sum_properEdgeNormal_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) (i : Fin 2)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
      tangentVector u i ∂surfaceAreaMeasure K) =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
          tangentVector ((t : ℝ) : Real.Angle) i) :=
  integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts K V hKV hturn
    (fun u ↦ tangentVector u i) E hE hEa

/-- Polygon case of the positive-vertex Stieltjes/surface-measure identity, including degenerate
point and segment convex hulls. -/
theorem positiveVertex_stieltjes_surface_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (a b : ℝ) (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      (∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
        (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure (f i) E =
          ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
            tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab.le
  refine ⟨f, hf, fun i E hE hEa ↦ ?_⟩
  rw [intervalStieltjesMeasure_eq_sum_properEdgeNormals K V hKV hab hturn f hf i E hE hEa,
    integral_tangentCoordinate_image_eq_sum_properEdgeNormal_lifts
      K V hKV hturn i E hE hEa]

/-- The positive vertex increment of a polygon is the tangent-coordinate surface integral over
the corresponding angular interval. -/
theorem positiveVertex_sub_eq_integral_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i -
        (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf, hmeasure⟩ :=
    positiveVertex_stieltjes_surface_of_eq_convexHull K V hKV a b hab hturn
  let aa : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let bb : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  have hangularImage :
      (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Set.Ioc aa bb =
        (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ⟨ht.1, ht.2⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1.le, ht.2⟩, ⟨ht.1, ht.2⟩, rfl⟩
  have hstieltjes := hmeasure i (Set.Ioc aa bb) measurableSet_Ioc
    (fun t ht ↦ ht.1)
  rw [intervalStieltjesMeasure_Ioc (f i) aa bb hab.le] at hstieltjes
  rw [hf i bb, hf i aa, hangularImage] at hstieltjes
  exact hstieltjes

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Boundary Limit
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace MovingSofa

/-- Face-preserving polygon approximation transfers the boundary increment identity. -/
private theorem positiveVertex_sub_eq_integral_of_polygon_identity
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (hpoly : ∀ (P : ConvexBody Point) (V : Finset Point),
      (P : Set Point) = convexHull ℝ (V : Set Point) → ∀ i : Fin 2,
      (edgeVertices P (b : Real.Angle)).1 i - (edgeVertices P (a : Real.Angle)).1 i =
        ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
          tangentVector u i ∂surfaceAreaMeasure P) (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  classical
  obtain ⟨V, P, hP, hdist⟩ := exists_facePreserving_polygonApproximation K
    {(a : Real.Angle), (b : Real.Angle)}
  have ha (n : ℕ) : exposedEdge (P n) (a : Real.Angle) = exposedEdge K (a : Real.Angle) :=
    (hP n).2.2.2 _ (by simp)
  have hb (n : ℕ) : exposedEdge (P n) (b : Real.Angle) = exposedEdge K (b : Real.Angle) :=
    (hP n).2.2.2 _ (by simp)
  have hlim : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hcontinuous : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hint := tendsto_integral_surfaceAreaMeasure_Ioc_of_preserves_faces
    P K hlim hab hturn ha hb (fun u ↦ tangentVector u i) hcontinuous
  have hvalue (n : ℕ) :
      (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure (P n)) =
      (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i := by
    rw [← hpoly (P n) (V n) (hP n).2.1 i,
      edgeVertices_eq_of_exposedEdge_eq (P n) K _ (ha n),
      edgeVertices_eq_of_exposedEdge_eq (P n) K _ (hb n)]
  simp only [hvalue] at hint
  exact tendsto_nhds_unique tendsto_const_nhds hint

/-- The positive vertex increment is the tangent-coordinate surface integral over
the corresponding half-open angular interval. -/
theorem positiveVertex_sub_eq_integral
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  exact positiveVertex_sub_eq_integral_of_polygon_identity K hab hturn
    (fun P V hPV i ↦ positiveVertex_sub_eq_integral_of_eq_convexHull P V hPV hab hturn i) i

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Discrete Bounds
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The integral of tangent vectors gives the increment of the positive supporting vertex. -/
theorem integral_tangentVector_surfaceAreaMeasure (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b,
      tangentVector u ∂surfaceAreaMeasure K) =
      (edgeVertices K (b : Real.Angle)).1 - (edgeVertices K (a : Real.Angle)).1 := by
  let A := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  ext i
  have hi := ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
  change (∫ u in A, tangentVector u i ∂surfaceAreaMeasure K) =
    (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) i at hi
  rw [← hi]
  exact (positiveVertex_sub_eq_integral K hab hturn i).symm

/-- The projected boundary integral computes the support value relative to the initial vertex. -/
theorem integral_inner_tangentVector_eq_support_sub (K : ConvexBody Point)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi) :
    (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s,
      inner ℝ (normalVector (s : Real.Angle)) (tangentVector u) ∂surfaceAreaMeasure K) =
      supportValue K (s : Real.Angle) -
        inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  let A := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hi := ContinuousLinearMap.integral_comp_comm
    (innerSL ℝ (normalVector (s : Real.Angle))) hu
  change (∫ u in A, inner ℝ (normalVector (s : Real.Angle)) (tangentVector u)
    ∂surfaceAreaMeasure K) = inner ℝ (normalVector (s : Real.Angle))
      (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) at hi
  rw [show (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) =
      (edgeVertices K (s : Real.Angle)).1 - (edgeVertices K 0).1 from
        integral_tangentVector_surfaceAreaMeasure K hs.1 (by linarith [hs.2, Real.pi_pos]),
    inner_sub_right,
    real_inner_comm (edgeVertices K (s : Real.Angle)).1 (normalVector (s : Real.Angle)),
    (edgeVertices_fst_mem K (s : Real.Angle)).2] at hi
  exact hi

/-- Positive atomic sine contributions are bounded by the corresponding support increment. -/
theorem sum_surfaceAreaMeasure_mul_pos_sin_le (K : ConvexBody Point)
    (D : Finset ℝ) (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi) :
    ∑ t ∈ D, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
      max (Real.sin (s - t)) 0 ≤ supportValue K (s : Real.Angle) -
        inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  classical
  let F := D.filter (fun t ↦ t ≤ s)
  let E := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s
  let g : Real.Angle → ℝ :=
    fun u ↦ inner ℝ (normalVector (s : Real.Angle)) (tangentVector u)
  have hcoe : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Set.Ioc 0 s) :=
    Real.Angle.injOn_coe_Ioc (by linarith [hs.2, Real.pi_pos])
  have hE : MeasurableSet E := measurableSet_Ioc.image_of_continuousOn_injOn
    Real.Angle.continuous_coe.continuousOn hcoe
  have hF (t : ℝ) (ht : t ∈ F) : t ∈ Set.Ioc 0 s :=
    ⟨(hD t (Finset.mem_filter.mp ht).1).1, (Finset.mem_filter.mp ht).2⟩
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hgcont : Continuous g := by
    apply Continuous.inner continuous_const
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hg : IntegrableOn g E (surfaceAreaMeasure K) :=
    by
    have hall : Integrable g (surfaceAreaMeasure K) := by
      rw [← integrableOn_univ]
      exact hgcont.continuousOn.integrableOn_compact isCompact_univ
    exact hall.integrableOn
  have hgnonneg : ∀ u ∈ E, 0 ≤ g u := by
    rintro u ⟨t, ht, rfl⟩
    change 0 ≤ inner ℝ (normalVector (s : Real.Angle)) (tangentVector (t : Real.Angle))
    rw [real_inner_comm (tangentVector (t : Real.Angle)), inner_tangentVector_normalVector_real]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [ht.2], by linarith [ht.1, hs.2]⟩
  have hb := sum_measureReal_mul_le_setIntegral (surfaceAreaMeasure K)
    (F.image fun t : ℝ ↦ (t : Real.Angle)) hE
    (by rintro u hu; obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu; exact ⟨t, hF t ht, rfl⟩)
    hg hgnonneg
  rw [Finset.sum_image (fun x hx y hy hxy ↦ hcoe (hF x hx) (hF y hy) hxy)] at hb
  have heval (t : ℝ) : g (t : Real.Angle) = Real.sin (s - t) := by
    dsimp [g]
    rw [real_inner_comm (tangentVector (t : Real.Angle)), inner_tangentVector_normalVector_real]
  simp_rw [heval] at hb
  change (∑ t ∈ F, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
    Real.sin (s - t)) ≤ _ at hb
  have hsum : (∑ t ∈ D, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
      max (Real.sin (s - t)) 0) =
      ∑ t ∈ F, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal * Real.sin (s - t) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hts : t ≤ s
    · rw [ite_eq_left hts, max_eq_left (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith, by linarith [(hD t ht).1, hs.2]⟩)]
    · have hsin : Real.sin (s - t) ≤ 0 := by
        have h := Real.sin_nonneg_of_mem_Icc
          (show t - s ∈ Set.Icc 0 Real.pi from
            ⟨by linarith, by linarith [(hD t ht).2, hs.1]⟩)
        rw [show s - t = -(t - s) by ring, Real.sin_neg]
        linarith
      rw [ite_eq_right hts, max_eq_right hsin, mul_zero]
  rw [hsum]
  exact hb.trans_eq (integral_inner_tangentVector_eq_support_sub K hs)

/-- For upper normals, the negative zero-angle vertex projects below the positive vertex. -/
theorem inner_negativeVertex_zero_le_positiveVertex (K : ConvexBody Point)
    {s : ℝ} (hs : s ∈ Set.Icc 0 Real.pi) :
    inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).2 ≤
      inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  have hy : inner ℝ (edgeVertices K 0).2 (tangentVector 0) ≤
      inner ℝ (edgeVertices K 0).1 (tangentVector 0) := by
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le ((isCompact_exposedEdge K 0).image
      (continuous_id.inner continuous_const)).bddBelow
      ⟨(edgeVertices K 0).1, edgeVertices_fst_mem K 0, rfl⟩
  have hx := (edgeVertices_fst_mem K 0).2.trans (edgeVertices_snd_mem K 0).2.symm
  simp only [normalVector, frame, Real.Angle.cos_zero, Real.Angle.sin_zero, neg_zero,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul,
    add_zero, tangentVector, zero_add, Real.Angle.cos_coe, Real.Angle.sin_coe, ge_iff_le] at hx hy ⊢
  have hsin := Real.sin_nonneg_of_mem_Icc hs
  rw [hx]
  linarith [mul_le_mul_of_nonneg_right hy hsin]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Integrals
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- A sine convolution of tangent directions is the negative normal projection of their
Bochner integral. -/
private theorem integral_sin_sub_eq_neg_inner_integral_tangentVector
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (u : α → Real.Angle) (t : Real.Angle)
    (hu : Integrable (fun x ↦ tangentVector (u x)) (μ.restrict s)) :
    (∫ x in s, (u x - t).sin ∂μ) =
      -inner ℝ (normalVector t) (∫ x in s, tangentVector (u x) ∂μ) := by
  let L : Point →L[ℝ] ℝ := innerSL ℝ (normalVector t)
  calc
    (∫ x in s, (u x - t).sin ∂μ) =
        ∫ x in s, -L (tangentVector (u x)) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact sin_sub_eq_neg_inner_normalVector_tangentVector t (u x)
    _ = -(∫ x in s, L (tangentVector (u x)) ∂μ) := integral_neg _
    _ = -L (∫ x in s, tangentVector (u x) ∂μ) := by
      rw [ContinuousLinearMap.integral_comp_comm L hu]
    _ = -inner ℝ (normalVector t) (∫ x in s, tangentVector (u x) ∂μ) := rfl

theorem tangentArm_convolution (K : RightAngleCapSpace) (t : ℝ) :
    (tangentArmLengths K t).2.1 =
      ∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2),
        (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure K.val := by
  let A := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2)
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K.val).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hvec : (∫ u in A, tangentVector u ∂surfaceAreaMeasure K.val) =
      (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
        (edgeVertices K.val (t : Real.Angle)).1 := by
    ext i
    have hi := ContinuousLinearMap.integral_comp_comm
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
    change (∫ u in A, tangentVector u i ∂surfaceAreaMeasure K.val) =
      (∫ u in A, tangentVector u ∂surfaceAreaMeasure K.val) i at hi
    rw [← hi]
    symm
    simpa [A] using positiveVertex_sub_eq_integral K.val (a := t)
      (b := t + Real.pi / 2) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) i
  have harm : (tangentArmLengths K t).2.1 =
      -inner ℝ (normalVector (t : Real.Angle))
        ((edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
          (edgeVertices K.val (t : Real.Angle)).1) := by
    obtain ⟨hA, _, hC, _⟩ := capTangentArm_identities K t
    have hnt : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector t
    have hnn : inner ℝ (normalVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 1 := inner_normalVector_self t
    rw [hA] at hC
    have hproj := congrArg (fun p : Point ↦ inner ℝ p (normalVector (t : Real.Angle))) hC
    simp only [inner_add_left, real_inner_smul_left, hnt, hnn, mul_zero, add_zero,
      mul_one] at hproj
    simp only [capVertices] at hproj
    rw [inner_sub_right]
    rw [real_inner_comm
      (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
      (normalVector (t : Real.Angle)),
      real_inner_comm (edgeVertices K.val (t : Real.Angle)).1
        (normalVector (t : Real.Angle))]
    linarith
  have hkernel := integral_sin_sub_eq_neg_inner_integral_tangentVector
    (surfaceAreaMeasure K.val) A id (t : Real.Angle) hu
  simp only [id_eq] at hkernel
  rw [show (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2) = A from rfl,
    hkernel, hvec, harm]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Vertex Boundary
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem positiveVertex_stieltjes_surface (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      (∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
        (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure (f i) E =
          ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
            tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab.le
  refine ⟨f, hf, ?_⟩
  apply intervalStieltjesMeasure_eq_surfaceIntegral_of_increment K hab hturn f hf
  intro c d hcd i
  have hcdturn : (d : ℝ) ≤ (c : ℝ) + 2 * Real.pi :=
    d.property.2.trans (hturn.trans (by linarith [c.property.1]))
  exact positiveVertex_sub_eq_integral K hcd hcdturn i

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Angular densities of the surface-area measure

On an angular window of at most one turn the positive vertex of a convex body is a function of
bounded variation whose Stieltjes measure, paired with the moving tangent, is the surface-area
measure (`sum_intervalStieltjesIntegral_positiveVertex_tangent`).  If on such a window the
positive vertex happens to be a differentiable curve with derivative `g s • tangentVector s`,
this identifies the surface-area measure with the Lebesgue density `g`.

This file records that identification (`surfaceAreaMeasure_angleImage_eq_setLIntegral`,
`surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt`), and the bookkeeping that glues
finitely many or countably many such windows together (`measure_angleImage_eq_of_union`,
`measure_angleImage_eq_of_iUnion`) and turns the resulting set-level identities into the
`Measure.restrict = Measure.map (Measure.withDensity …)` form used by cap-density statements
(`measure_restrict_eq_map_withDensity`, `surfaceAreaMeasure_restrict_eq_map_withDensity`,
`surfaceAreaMeasure_restrict_eq_map_add_withDensity`).

The gluing lemmas are stated for an arbitrary pair of measures on `Real.Angle` and on `ℝ`,
since they only use additivity and the injectivity of the angular projection on a window of at
most one turn.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MovingSofa

/-- Pairing the frame tangent with a multiple of itself, in coordinates. -/
private theorem sum_mul_tangentVector_sq (c s : ℝ) :
    tangentVector (s : Real.Angle) 0 * (c * tangentVector (s : Real.Angle) 0) +
      tangentVector (s : Real.Angle) 1 * (c * tangentVector (s : Real.Angle) 1) = c := by
  have h : tangentVector (s : Real.Angle) 0 ^ 2 + tangentVector (s : Real.Angle) 1 ^ 2 = 1 := by
    have h := inner_tangentVector_self s
    rw [PiLp.inner_apply] at h
    simpa [Fin.sum_univ_two] using h
  linear_combination c * h

/-! ### The surface measure of an arc with a differentiable positive vertex -/

/-- Suppose that on the angular window `Ioc a b`, of at most one turn, the positive vertex of `K`
is traced by a curve `F` with derivative `g s • tangentVector s`, where `g` is continuous and
nonnegative.  Then the surface-area measure of the angular image of a measurable
`S ⊆ Ioc a b` is the Lebesgue integral of `g` over `S`. -/
theorem surfaceAreaMeasure_angleImage_eq_setLIntegral (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (g s • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Ioc a b, 0 ≤ g s)
    (hvertex : ∀ s ∈ Icc a b, (edgeVertices K (s : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      ∫⁻ s in S, ENNReal.ofReal (g s) := by
  have hfin : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hSIcc : S ⊆ Icc a b := hSsub.trans Ioc_subset_Icc_self
  obtain ⟨f, hftoFun, hfmeas⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  have hcontT : ∀ i : Fin 2, Continuous fun s : ℝ ↦ tangentVector (s : Real.Angle) i :=
    fun i ↦ (continuous_tangentVector_coordinate i).comp Real.Angle.continuous_coe
  -- the coordinate functions of the differentiable vertex curve and their derivatives
  set φ : Fin 2 → ℝ → ℝ := fun i s ↦ F s i with hφ
  set ψ : Fin 2 → ℝ → ℝ := fun i s ↦ g s * tangentVector (s : Real.Angle) i with hψ
  have hderiv : ∀ (i : Fin 2) (s : ℝ), HasDerivAt (φ i) (ψ i s) s := by
    intro i s
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt s (hF s)
    simpa [φ, ψ, Function.comp_def] using h
  have hcontψ : ∀ i : Fin 2, Continuous (ψ i) := fun i ↦ hg.mul (hcontT i)
  -- the Stieltjes density of each vertex coordinate
  have hdens : ∀ i : Fin 2, HasIntervalStieltjesDensity (f i) (ψ i) := by
    intro i
    obtain ⟨G, hGfun, hGdens⟩ :=
      exists_intervalBV_of_hasDerivAt hab.le (φ i) (ψ i) (hderiv i) (hcontψ i)
    have hfe : f i = G := by
      refine RightContinuousIntervalBV.toFun_injective (funext fun t ↦ ?_)
      rw [hftoFun i t, hGfun t, hvertex (t : ℝ) t.2]
    rw [hfe]
    exact hGdens
  -- the sum over the two coordinates of the Stieltjes integrals
  set E : Set (Icc a b) := {x : Icc a b | (x : ℝ) ∈ S} with hE
  have hEmeas : MeasurableSet E := hS.preimage measurable_subtype_coe
  have hEa : ∀ t ∈ E, a < (t : ℝ) := fun t ht ↦ (hSsub ht).1
  have himage : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E =
      (fun s : ℝ ↦ (s : Real.Angle)) '' S := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hSIcc hs⟩, hs, rfl⟩
  have hsum := sum_intervalStieltjesIntegral_positiveVertex_tangent K hab hturn f hfmeas
    E hEmeas hEa
  rw [himage] at hsum
  -- each Stieltjes integral is an ordinary set integral
  have hstep : ∀ i : Fin 2,
      intervalStieltjesIntegral (f i) (fun t ↦ tangentVector ((t : ℝ) : Real.Angle) i) E =
        ∫ s in S, tangentVector (s : Real.Angle) i * ψ i s := by
    intro i
    have hq : Continuous fun t : Icc a b ↦ tangentVector ((t : ℝ) : Real.Angle) i :=
      (hcontT i).comp continuous_subtype_val
    rw [intervalStieltjesIntegral_eq_integral_mul_of_density (f i) (hdens i) hq E hEmeas]
    rw [MeasureTheory.integral_subtype_preimage measurableSet_Icc hS
      (fun s ↦ tangentVector (s : Real.Angle) i * ψ i s)]
    rw [Measure.restrict_restrict_of_subset hSIcc]
  simp only [hstep] at hsum
  -- integrability of the two summands and of the density
  have hintegrand : ∀ i : Fin 2,
      IntegrableOn (fun s : ℝ ↦ tangentVector (s : Real.Angle) i * ψ i s) S volume := by
    intro i
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set hSIcc
    exact ((hcontT i).mul (hcontψ i)).continuousOn
  have hgint : IntegrableOn g S volume :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hg.continuousOn).mono_set hSIcc
  have hsum2 : (surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S)).toReal =
      ∫ s in S, g s := by
    rw [← hsum, Fin.sum_univ_two, ← integral_add (hintegrand 0) (hintegrand 1)]
    refine setIntegral_congr_fun hS fun s _ ↦ ?_
    exact sum_mul_tangentVector_sq (g s) s
  rw [← ENNReal.ofReal_toReal (measure_ne_top (surfaceAreaMeasure K) _), hsum2]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint]
  filter_upwards [ae_restrict_mem hS] with s hs
  exact hgnn s (hSsub hs)

/-- The same identification as `surfaceAreaMeasure_angleImage_eq_setLIntegral`, phrased as
agreement with a `Measure.withDensity` for any nonnegative weight `w` that agrees with the
derivative factor `g` on the window. -/
theorem surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (g w : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (g s • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hvertex : ∀ s ∈ Icc a b, (edgeVertices K (s : Real.Angle)).1 = F s)
    (hw : ∀ s ∈ Ioc a b, w s = g s) (hwnn : ∀ s ∈ Ioc a b, 0 ≤ w s)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (w s)) S := by
  have hgnn : ∀ s ∈ Ioc a b, 0 ≤ g s := fun s hs ↦ (hw s hs) ▸ hwnn s hs
  rw [withDensity_apply _ hS, surfaceAreaMeasure_angleImage_eq_setLIntegral K hab hturn F g hF hg
    hgnn hvertex hS hSsub]
  exact setLIntegral_congr_fun hS fun s hs ↦ by rw [hw s (hSsub hs)]

/-! ### Gluing angular density identities -/

/-- Two measures that read one another through the angular projection on each of two disjoint
measurable subsets of a window of at most one turn do so on their union. -/
theorem measure_angleImage_eq_of_union {μ : Measure Real.Angle} {ν : Measure ℝ} {c d : ℝ}
    (hturn : d ≤ c + 2 * Real.pi) {I J : Set ℝ}
    (hI : I ⊆ Ioc c d) (hJ : J ⊆ Ioc c d)
    (hImeas : MeasurableSet I) (hJmeas : MeasurableSet J) (hdisj : Disjoint I J)
    (hA : ∀ S, MeasurableSet S → S ⊆ I → μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (hB : ∀ S, MeasurableSet S → S ⊆ J → μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ I ∪ J) :
    μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S := by
  have hsplit : S = S ∩ I ∪ S ∩ J := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.2 hSsub]
  have hSI : MeasurableSet (S ∩ I) := hS.inter hImeas
  have hSJ : MeasurableSet (S ∩ J) := hS.inter hJmeas
  have hdisj' : Disjoint (S ∩ I) (S ∩ J) :=
    hdisj.mono Set.inter_subset_right Set.inter_subset_right
  have hinj := Real.Angle.injOn_coe_Ioc hturn
  have himdisj : Disjoint ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I))
      ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := by
    rw [Set.disjoint_left]
    rintro u ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyx : y = x := hinj (hJ hy.2) (hI hx.2) hxy
    exact (Set.disjoint_left.1 hdisj' hx) (hyx ▸ hy)
  have himmeas : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hSJ (Set.inter_subset_right.trans hJ)
  calc μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S)
      = μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I) ∪
          (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := by
        rw [← Set.image_union, ← hsplit]
    _ = μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I)) +
          μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := measure_union himdisj himmeas
    _ = ν (S ∩ I) + ν (S ∩ J) := by
        rw [hA _ hSI Set.inter_subset_right, hB _ hSJ Set.inter_subset_right]
    _ = ν S := by rw [← measure_union hdisj' hSJ, ← hsplit]

/-- Two measures that read one another through the angular projection on each member of a
monotone sequence of measurable sets do so on the union of that sequence. -/
theorem measure_angleImage_eq_of_iUnion {μ : Measure Real.Angle} {ν : Measure ℝ}
    {J : ℕ → Set ℝ} (hmono : Monotone J) (hJmeas : ∀ n, MeasurableSet (J n))
    (hA : ∀ (n : ℕ) (S : Set ℝ), MeasurableSet S → S ⊆ J n →
      μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ ⋃ n, J n) :
    μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S := by
  have hSeq : S = ⋃ n, S ∩ J n := by
    rw [← Set.inter_iUnion, Set.inter_eq_left.2 hSsub]
  have hmono' : Monotone fun n ↦ S ∩ J n := fun m n h ↦
    Set.inter_subset_inter_right _ (hmono h)
  have hmonoimg : Monotone fun n ↦ (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n) :=
    fun m n h ↦ Set.image_mono (hmono' h)
  calc μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S)
      = μ (⋃ n, (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n)) := by
        rw [← Set.image_iUnion, ← hSeq]
    _ = ⨆ n, μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n)) := hmonoimg.measure_iUnion
    _ = ⨆ n, ν (S ∩ J n) :=
        iSup_congr fun n ↦ hA n _ (hS.inter (hJmeas n)) Set.inter_subset_right
    _ = ν S := by rw [← hmono'.measure_iUnion, ← hSeq]

/-! ### From set-level identities to restricted measures -/

/-- A set-level angular density identity on a measurable parameter set `I` says exactly that the
measure restricted to the angular image of `I` is the pushforward of the weighted Lebesgue
measure on `I`. -/
theorem measure_restrict_eq_map_withDensity {μ : Measure Real.Angle} {I : Set ℝ}
    {w : ℝ → ℝ≥0∞} (hImeas : MeasurableSet I)
    (hagree : ∀ S, MeasurableSet S → S ⊆ I →
      μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = volume.withDensity w S) :
    μ.restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' I) =
      Measure.map (fun s : ℝ ↦ (s : Real.Angle)) ((volume.restrict I).withDensity w) := by
  have hmeas : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  ext B hB
  have hpre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B) := hB.preimage hmeas
  have hset : B ∩ (fun s : ℝ ↦ (s : Real.Angle)) '' I =
      (fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ I) := by
    ext u
    constructor
    · rintro ⟨hu, s, hs, rfl⟩
      exact ⟨s, ⟨hu, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      exact ⟨hs1, s, hs2, rfl⟩
  rw [Measure.restrict_apply hB, hset, hagree _ (hpre.inter hImeas) Set.inter_subset_right,
    Measure.map_apply hmeas hB, withDensity_apply _ hpre,
    withDensity_apply _ (hpre.inter hImeas), Measure.restrict_restrict hpre]

/-- The surface-area measure instance of `measure_restrict_eq_map_withDensity`. -/
theorem surfaceAreaMeasure_restrict_eq_map_withDensity {K : ConvexBody Point}
    {I : Set ℝ} {w : ℝ → ℝ≥0∞} (hImeas : MeasurableSet I)
    (hagree : ∀ S, MeasurableSet S → S ⊆ I →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = volume.withDensity w S) :
    (surfaceAreaMeasure K).restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' I) =
      Measure.map (fun s : ℝ ↦ (s : Real.Angle)) ((volume.restrict I).withDensity w) :=
  measure_restrict_eq_map_withDensity hImeas hagree

/-- The shifted form of `surfaceAreaMeasure_restrict_eq_map_withDensity`: an angular density
identity on the translated window `Ioc c (c + T)` with the translated weight `u ↦ w (u - c)`
says that the surface-area measure restricted to that angular arc is the pushforward of the
`w`-weighted Lebesgue measure on `Ioc 0 T` along `t ↦ ↑(t + c)`. -/
theorem surfaceAreaMeasure_restrict_eq_map_add_withDensity {K : ConvexBody Point}
    {c T : ℝ} {w : ℝ → ℝ≥0∞}
    (hagree : ∀ S, MeasurableSet S → S ⊆ Ioc c (c + T) →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun u ↦ w (u - c)) S) :
    (surfaceAreaMeasure K).restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc c (c + T)) =
      Measure.map (fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle))
        ((volume.restrict (Ioc 0 T)).withDensity w) := by
  have hmeas : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  have hmeas' : Measurable fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle) :=
    Real.Angle.continuous_coe.measurable.comp (measurable_id.add_const c)
  ext B hB
  have hpre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B) := hB.preimage hmeas
  have hpre' : MeasurableSet ((fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle)) ⁻¹' B) :=
    hB.preimage hmeas'
  have hset : B ∩ (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc c (c + T) =
      (fun s : ℝ ↦ (s : Real.Angle)) ''
        ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ Ioc c (c + T)) := by
    ext u
    constructor
    · rintro ⟨hu, s, hs, rfl⟩
      exact ⟨s, ⟨hu, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      exact ⟨hs1, s, hs2, rfl⟩
  have hpreimage : (fun t : ℝ ↦ t + c) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ Ioc c (c + T)) =
      (fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle)) ⁻¹' B ∩ Ioc 0 T := by
    ext t
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  rw [Measure.restrict_apply hB, hset,
    hagree _ (hpre.inter measurableSet_Ioc) Set.inter_subset_right,
    withDensity_apply _ (hpre.inter measurableSet_Ioc), setLIntegral_comp_sub_right, hpreimage,
    Measure.map_apply hmeas' hB, withDensity_apply _ hpre',
    Measure.restrict_restrict hpre']

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Frame Products
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- The normal and tangent projections of the positive vertex, with their Stieltjes measures. -/
theorem exists_positiveVertex_frame_products
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ H P : RightContinuousIntervalBV a b,
      (∀ t, H.toFun t = inner ℝ (edgeVertices K (((t : ℝ) : Real.Angle))).1
        (normalVector (((t : ℝ) : Real.Angle)))) ∧
      (∀ t, P.toFun t = inner ℝ (edgeVertices K (((t : ℝ) : Real.Angle))).1
        (tangentVector (((t : ℝ) : Real.Angle)))) ∧
      ∀ E : Set (Icc a b), MeasurableSet E → (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure H E =
          ∫ t in (Subtype.val : Icc a b → ℝ) '' E,
            inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ∧
        intervalStieltjesMeasure P E =
          (surfaceAreaMeasure K
              ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal -
            ∫ t in (Subtype.val : Icc a b → ℝ) '' E,
              inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) := by
  obtain ⟨v, hv, hvm⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  choose n hn hnd using fun i : Fin 2 ↦ exists_normalVector_coordinate_intervalBV hab.le i
  choose τ hτ hτd using fun i : Fin 2 ↦ exists_tangentVector_coordinate_intervalBV hab.le i
  have hnc (i : Fin 2) : Continuous (n i).toFun := by
    convert ((by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin :
          Continuous (fun u : Real.Angle ↦ normalVector u i))).comp
          (Real.Angle.continuous_coe.comp continuous_subtype_val) using 1
    funext t
    exact hn i t
  have hτc (i : Fin 2) : Continuous (τ i).toFun := by
    convert ((by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos :
          Continuous (fun u : Real.Angle ↦ tangentVector u i))).comp
          (Real.Angle.continuous_coe.comp continuous_subtype_val) using 1
    funext t
    exact hτ i t
  obtain ⟨H, hH, hHm⟩ := intervalStieltjes_inner_fin_two v n hnc
  obtain ⟨P, hP, hPm⟩ := intervalStieltjes_inner_fin_two v τ hτc
  refine ⟨H, P, ?_, ?_, ?_⟩
  · intro t
    rw [hH]
    simp_rw [hv, hn]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  · intro t
    rw [hP]
    simp_rw [hv, hτ]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  · intro E hE hEa
    have hnormal := sum_intervalStieltjesIntegral_positiveVertex_normal
      K hab hturn v hvm E hE hEa
    have htangent := sum_intervalStieltjesIntegral_positiveVertex_tangent
      K hab hturn v hvm E hE hEa
    have hnfun (i : Fin 2) : (n i).toFun =
        fun t : Icc a b ↦ normalVector (((t : ℝ) : Real.Angle)) i :=
      funext (hn i)
    have hτfun (i : Fin 2) : (τ i).toFun =
        fun t : Icc a b ↦ tangentVector (((t : ℝ) : Real.Angle)) i :=
      funext (hτ i)
    have hnormal' :
        (∑ i : Fin 2, intervalStieltjesIntegral (v i) (n i).toFun E) = 0 := by
      simpa only [hnfun] using hnormal
    have htangent' :
        (∑ i : Fin 2, intervalStieltjesIntegral (v i) (τ i).toFun E) =
          (surfaceAreaMeasure K
            ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal := by
      simpa only [hτfun] using htangent
    have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
      ⟨by
        rw [comap_subtype_coe_apply measurableSet_Icc]
        simp only [image_univ, Subtype.range_val]
        exact measure_Icc_lt_top⟩
    let _ := hfinite
    have hsmoothN (i : Fin 2) :
        intervalStieltjesIntegral (n i) (v i).toFun E =
          ∫ t in E, (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ) :=
      intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (n i) (hnd i)
        (v i).boundedVariation E hE
    have hsmoothT (i : Fin 2) :
        intervalStieltjesIntegral (τ i) (v i).toFun E =
          ∫ t in E, (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ) :=
      intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (τ i) (hτd i)
        (v i).boundedVariation E hE
    have hintN (i : Fin 2) : Integrable
        (fun t : Icc a b ↦ (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i)
        (volume.comap (Subtype.val : Icc a b → ℝ)) := by
      apply (v i).boundedVariation.integrable.mul_bdd
      · exact ((by
          fin_cases i
          · exact Real.Angle.continuous_sin.neg
          · exact Real.Angle.continuous_cos :
              Continuous (fun u : Real.Angle ↦ tangentVector u i))).comp
              (Real.Angle.continuous_coe.comp continuous_subtype_val) |>.aestronglyMeasurable
      · filter_upwards with t
        fin_cases i
        · simpa [tangentVector, frame] using Real.abs_sin_le_one (t : ℝ)
        · simpa [tangentVector, frame] using Real.abs_cos_le_one (t : ℝ)
    have hintT (i : Fin 2) : Integrable
        (fun t : Icc a b ↦ (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i)
        (volume.comap (Subtype.val : Icc a b → ℝ)) := by
      apply (v i).boundedVariation.integrable.mul_bdd
      · exact ((by
          fin_cases i
          · exact Real.Angle.continuous_cos.neg
          · exact Real.Angle.continuous_sin.neg :
              Continuous (fun u : Real.Angle ↦ -normalVector u i))).comp
              (Real.Angle.continuous_coe.comp continuous_subtype_val) |>.aestronglyMeasurable
      · filter_upwards with t
        fin_cases i
        · simpa [normalVector, frame] using Real.abs_cos_le_one (t : ℝ)
        · simpa [normalVector, frame] using Real.abs_sin_le_one (t : ℝ)
    let R := (Subtype.val : Icc a b → ℝ) '' E
    have hR : MeasurableSet R :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hE
    have hRsub : R ⊆ Icc a b := by
      rintro x ⟨t, -, rfl⟩
      exact t.property
    have hpre : {t : Icc a b | (t : ℝ) ∈ R} = E :=
      Set.preimage_image_eq E Subtype.val_injective
    have hsubN :
        (∑ i : Fin 2, ∫ t in E,
          (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ)) =
          ∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (tangentVector (t : Real.Angle)) := by
      rw [Fin.sum_univ_two, ← integral_add (hintN 0).integrableOn (hintN 1).integrableOn]
      have hsubtype := integral_subtype_preimage (μ := volume) (s := Icc a b) (t := R)
        measurableSet_Icc hR
        (fun t : ℝ ↦ inner ℝ (edgeVertices K (t : Real.Angle)).1
          (tangentVector (t : Real.Angle)))
      rw [hpre, Measure.restrict_restrict_of_subset hRsub] at hsubtype
      rw [← hsubtype]
      apply integral_congr_ae
      filter_upwards with t
      rw [hv 0 t, hv 1 t]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
      ring
    have hsubT :
        (∑ i : Fin 2, ∫ t in E,
          (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ)) =
          -(∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) := by
      rw [Fin.sum_univ_two, ← integral_add (hintT 0).integrableOn (hintT 1).integrableOn]
      have hsubtype := integral_subtype_preimage (μ := volume) (s := Icc a b) (t := R)
        measurableSet_Icc hR
        (fun t : ℝ ↦ inner ℝ (edgeVertices K (t : Real.Angle)).1
          (normalVector (t : Real.Angle)))
      rw [hpre, Measure.restrict_restrict_of_subset hRsub] at hsubtype
      rw [← hsubtype, ← integral_neg]
      apply integral_congr_ae
      filter_upwards with t
      rw [hv 0 t, hv 1 t]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
      ring
    constructor
    · rw [hHm E hE, Finset.sum_add_distrib, hnormal']
      simp only [zero_add]
      simpa only [hsmoothN] using hsubN
    · rw [hPm E hE, Finset.sum_add_distrib, htangent']
      rw [show (∑ i : Fin 2, intervalStieltjesIntegral (τ i) (v i).toFun E) =
          -(∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) by simpa only [hsmoothT] using hsubT]
      ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Boundary
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem positiveArm_stieltjes_surface (K : RightAngleCapSpace) :
    ∃ f : RightContinuousIntervalBV 0 (Real.pi / 2),
      (∀ t, f.toFun t = (tangentArmLengths K t).1.1) ∧
      ∀ E : Set (Set.Icc (0 : ℝ) (Real.pi / 2)), MeasurableSet E →
        (∀ t ∈ E, 0 < (t : ℝ)) →
        intervalStieltjesMeasure f E =
          (∫ t in (fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ (s : ℝ)) '' E,
            (tangentArmLengths K t).2.1) -
          (surfaceAreaMeasure K.val
            ((fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ ((s : ℝ) : Real.Angle)) '' E)).toReal := by
  have hT : 0 < (Real.pi / 2) := by positivity
  obtain ⟨HA, PA, hHA, hPA, hmA⟩ := exists_positiveVertex_frame_products K.val hT
    (by linarith [Real.pi_pos])
  obtain ⟨HC, PC, hHC, hPC, hmC⟩ := exists_positiveVertex_frame_products K.val
    (a := 0 + (Real.pi / 2)) (b := (Real.pi / 2) + (Real.pi / 2)) (by linarith)
    (by linarith [Real.pi_pos])
  have hHC_support (t : Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2))) :
      HC.toFun t = supportValue K.val (((t : ℝ) : Real.Angle)) := by
    rw [hHC, (edgeVertices_fst_mem K.val (((t : ℝ) : Real.Angle))).2]
  have hHCc : Continuous HC.toFun := by
    convert (continuous_supportValue_real K.val).comp continuous_subtype_val using 1
    funext t
    exact hHC_support t
  obtain ⟨Hs, hHs, hHsm⟩ := exists_intervalBV_shift_from_zero hT.le HC hHCc
  obtain ⟨f, hf, hfm⟩ := intervalStieltjes_linear_combination 0 (Real.pi / 2) Hs PA 1 (-1)
  refine ⟨f, ?_, ?_⟩
  · intro t
    rw [hf, hHs, hHC_support, hPA, (tangentArmLengths_positive_frame K t).1]
    simp only [one_mul, neg_mul, one_mul]
    ring
  · intro E hE hE0
    change Set (Icc 0 (Real.pi / 2)) at E
    let φ : Icc 0 (Real.pi / 2) →
        Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) := fun t ↦
      ⟨(t : ℝ) + (Real.pi / 2), by constructor <;> linarith [t.property.1, t.property.2]⟩
    let R := (Subtype.val : Icc 0 (Real.pi / 2) → ℝ) '' E
    have hR : MeasurableSet R :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hE
    have hφE : MeasurableSet (φ '' E) := by
      let ψ : Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) →
          Icc 0 (Real.pi / 2) := fun t ↦
        ⟨(t : ℝ) - (Real.pi / 2), by
          constructor
          · linarith [t.property.1]
          · linarith [t.property.2]⟩
      let e : Icc 0 (Real.pi / 2) ≃ₜ
          Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) :=
        { toFun := φ
          invFun := ψ
          left_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
          right_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
          continuous_toFun := (continuous_subtype_val.add_const (Real.pi / 2)).subtype_mk _
          continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _ }
      exact e.measurableEmbedding.measurableSet_image' hE
    have hφleft : ∀ t ∈ φ '' E, 0 + (Real.pi / 2) < (t : ℝ) := by
      rintro t ⟨s, hs, rfl⟩
      dsimp [φ]
      linarith [hE0 s hs]
    have hreal : (Subtype.val :
        Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) → ℝ) '' (φ '' E) =
        (fun x : ℝ ↦ x + (Real.pi / 2)) '' R := by
      ext x
      constructor
      · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, ⟨s, hs, rfl⟩, rfl⟩
      · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
    have hHs_measure : intervalStieltjesMeasure Hs E =
        ∫ t in R, inner ℝ
          (edgeVertices K.val (((t + (Real.pi / 2) : ℝ) : Real.Angle))).1
          (tangentVector (((t + (Real.pi / 2) : ℝ) : Real.Angle))) := by
      rw [hHsm E hE, (hmC (φ '' E) hφE hφleft).1, hreal,
        integral_image_add_right_eq (Real.pi / 2) R hR]
    have hPA_measure := (hmA E hE hE0).2
    have hlin : intervalStieltjesMeasure f E =
        intervalStieltjesMeasure Hs E - intervalStieltjesMeasure PA E := by
      have := congrArg (fun m : SignedMeasure (Icc 0 (Real.pi / 2)) ↦ m E) hfm
      rw [add_apply, _root_.smul_apply, _root_.smul_apply] at this
      simpa only [smul_eq_mul, one_mul, neg_one_mul, sub_eq_add_neg] using this
    change intervalStieltjesMeasure f E = _
    rw [hlin, hHs_measure, hPA_measure]
    have hAint : IntegrableOn
        (fun t : ℝ ↦ inner ℝ (edgeVertices K.val (t : Real.Angle)).1
          (normalVector (t : Real.Angle))) R := by
      have hAIcc := HA.integrableOn_Icc_of_eq
        (fun t : ℝ ↦ inner ℝ (edgeVertices K.val (t : Real.Angle)).1
          (normalVector (t : Real.Angle))) (fun t ↦ (hHA t).symm)
      apply hAIcc.mono_set
      rintro x ⟨t, -, rfl⟩
      exact t.property
    have hCint : IntegrableOn
        (fun t : ℝ ↦ inner ℝ
          (edgeVertices K.val (((t + (Real.pi / 2) : ℝ) : Real.Angle))).1
          (tangentVector (((t + (Real.pi / 2) : ℝ) : Real.Angle)))) R := by
      let q : ℝ → ℝ := fun s ↦ inner ℝ (edgeVertices K.val (s : Real.Angle)).1
        (tangentVector (s : Real.Angle))
      have hqIcc := PC.integrableOn_Icc_of_eq q (fun t ↦ (hPC t).symm)
      have hqshift : IntegrableOn q
          ((fun x : ℝ ↦ x + Real.pi / 2) '' R) := by
        apply hqIcc.mono_set
        rintro x ⟨-, ⟨t, -, rfl⟩, rfl⟩
        constructor <;> linarith [t.property.1, t.property.2]
      exact (integrableOn_comp_add_right_iff (Real.pi / 2) R hR q).2 hqshift
    rw [show (∫ t in R, inner ℝ
          (edgeVertices K.val (((t + Real.pi / 2 : ℝ) : Real.Angle))).1
          (tangentVector (((t + Real.pi / 2 : ℝ) : Real.Angle)))) -
        ((surfaceAreaMeasure K.val
          ((fun t : Icc 0 (Real.pi / 2) ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal -
          ∫ t in R, inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) =
        ((∫ t in R, inner ℝ
            (edgeVertices K.val (((t + Real.pi / 2 : ℝ) : Real.Angle))).1
            (tangentVector (((t + Real.pi / 2 : ℝ) : Real.Angle)))) +
          ∫ t in R, inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) -
        (surfaceAreaMeasure K.val
          ((fun t : Icc 0 (Real.pi / 2) ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal by ring]
    rw [← integral_add hCint hAint]
    apply congrArg (fun z : ℝ ↦ z -
      (surfaceAreaMeasure K.val
        ((fun s : Icc (0 : ℝ) (Real.pi / 2) ↦ ((s : ℝ) : Real.Angle)) '' E)).toReal)
    apply integral_congr_ae
    filter_upwards with t
    rw [(tangentArmLengths_positive_frame K t).2]
    ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Linearity
-/

public section

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace MovingSofa

private theorem intervalStieltjesMeasure_congr {a b : ℝ}
    (f g : RightContinuousIntervalBV a b) (h : ∀ x, f.toFun x = g.toFun x) :
    intervalStieltjesMeasure f = intervalStieltjesMeasure g := by
  have hfun : f.toFun = g.toFun := funext h
  cases f with
  | mk ff hfb hfr =>
    cases g with
    | mk gf hgb hgr =>
      simp only at hfun ⊢
      subst gf
      rfl

/-- Planar surface area measures commute with convex combinations. -/
theorem surfaceAreaMeasure_convexBodyCombination (t : I)
    (K L : ConvexBody Point) :
    surfaceAreaMeasure (convexBodyCombination t K L) =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L := by
  let r : ℝ := 1 - (t : ℝ)
  let s : ℝ := t
  let M := convexBodyCombination t K L
  have hvertex (u : Real.Angle) :
      (edgeVertices M u).1 = r • (edgeVertices K u).1 + s • (edgeVertices L u).1 :=
    (edgeVertices_convexBodyCombination t K L u).1
  have hab : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hturn : 2 * Real.pi ≤ (0 : ℝ) + 2 * Real.pi := by simp
  obtain ⟨fM, hfM, hmM⟩ := positiveVertex_stieltjes_surface M 0 (2 * Real.pi) hab hturn
  obtain ⟨fK, hfK, hmK⟩ := positiveVertex_stieltjes_surface K 0 (2 * Real.pi) hab hturn
  obtain ⟨fL, hfL, hmL⟩ := positiveVertex_stieltjes_surface L 0 (2 * Real.pi) hab hturn
  have hmeasure (i : Fin 2) : intervalStieltjesMeasure (fM i) =
      r • intervalStieltjesMeasure (fK i) + s • intervalStieltjesMeasure (fL i) := by
    obtain ⟨f, hfun, hfm⟩ := intervalStieltjes_linear_combination
      0 (2 * Real.pi) (fK i) (fL i) r s
    have heq : intervalStieltjesMeasure f = intervalStieltjesMeasure (fM i) := by
      apply intervalStieltjesMeasure_congr
      intro x
      rw [hfun, hfK, hfL, hfM]
      have hv := congrArg (fun p : Point ↦ p i)
        (hvertex (((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) : Real.Angle))
      simpa [r, s] using hv.symm
    rwa [← heq]
  ext A hA
  let E : Set (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    {x | 0 < (x : ℝ) ∧ (((x : ℝ) : Real.Angle)) ∈ A}
  have hE : MeasurableSet E := by
    exact (measurableSet_Ioi.preimage measurable_subtype_coe).inter
      (hA.preimage (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable)
  have hEa : ∀ x ∈ E, 0 < (x : ℝ) := fun _ hx ↦ hx.1
  have himage : (fun x : Set.Icc (0 : ℝ) (2 * Real.pi) ↦
      (((x : ℝ) : Real.Angle))) '' E = A := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hu
      let _ : Fact (0 < 2 * Real.pi) := ⟨hab⟩
      let x := AddCircle.equivIoc (2 * Real.pi) 0 u
      have hx : (x : ℝ) ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by simpa using x.property
      let y : Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨x, hx.1.le, hx.2⟩
      have hxu : (((x : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
      refine ⟨y, ⟨hx.1, ?_⟩, ?_⟩
      · simpa [y, hxu] using hu
      · simpa [y] using hxu
  have hmassM := sum_intervalStieltjesIntegral_positiveVertex_tangent
    M hab hturn fM hmM E hE hEa
  have hmassK := sum_intervalStieltjesIntegral_positiveVertex_tangent
    K hab hturn fK hmK E hE hEa
  have hmassL := sum_intervalStieltjesIntegral_positiveVertex_tangent
    L hab hturn fL hmL E hE hEa
  rw [himage] at hmassM hmassK hmassL
  have hstieltjes (i : Fin 2) :
      intervalStieltjesIntegral (fM i)
          (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
            Real.Angle)) i) E =
        r * intervalStieltjesIntegral (fK i)
            (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
              Real.Angle)) i) E +
          s * intervalStieltjesIntegral (fL i)
            (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
              Real.Angle)) i) E := by
    have hq : Continuous (fun x : Set.Icc (0 : ℝ) (2 * Real.pi) ↦
        tangentVector (((x : ℝ) : Real.Angle)) i) := by
      have hi : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
        fin_cases i
        · exact Real.Angle.continuous_sin.neg
        · exact Real.Angle.continuous_cos
      exact hi.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)
    have hrint : (r • VectorMeasure.restrict (intervalStieltjesMeasure (fK i)) E).Integrable
        (fun x ↦ tangentVector (((x : ℝ) : Real.Angle)) i) :=
      ((fK i).integrable_of_continuous hq).integrableOn.smul_vectorMeasure r
    have hsint : (s • VectorMeasure.restrict (intervalStieltjesMeasure (fL i)) E).Integrable
        (fun x ↦ tangentVector (((x : ℝ) : Real.Angle)) i) :=
      ((fL i).integrable_of_continuous hq).integrableOn.smul_vectorMeasure s
    unfold intervalStieltjesIntegral
    rw [hmeasure i, VectorMeasure.restrict_add, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_smul, VectorMeasure.integral_add_vectorMeasure hrint hsint,
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure]
    rfl
  have hreal : (surfaceAreaMeasure M A).toReal =
      r * (surfaceAreaMeasure K A).toReal + s * (surfaceAreaMeasure L A).toReal := by
    rw [← hmassM, ← hmassK, ← hmassL, Fin.sum_univ_two]
    rw [hstieltjes 0, hstieltjes 1]
    simp only [Fin.sum_univ_two]
    ring
  let _ : IsFiniteMeasure (surfaceAreaMeasure M) := (surfaceAreaMeasure_face_union M).1
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
  have hKtop : surfaceAreaMeasure K A ≠ ⊤ := measure_ne_top _ A
  have hLtop : surfaceAreaMeasure L A ≠ ⊤ := measure_ne_top _ A
  have hright :
      (ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L) A ≠ ⊤ := by
    rw [Measure.add_apply]
    simp only [Measure.smul_apply]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ A) hright).mp
  rw [show convexBodyCombination t K L = M from rfl, hreal]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr t.2.2), ENNReal.toReal_ofReal t.2.1]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Angular densities of the opposite surface measure

The opposite surface measure `(oppositeSurfaceData K).1` is the surface-area measure of `K`
translated by `π`, so it reads the *negative* vertex data of `K` at the angle `s` as the positive
vertex data at `π + s`.  Transporting `surfaceAreaMeasure_angleImage_eq_setLIntegral` along that
translation identifies it with a Lebesgue density whenever the positive vertex of `K` at normal
`π + s` is traced by a differentiable curve `F` with derivative `-(g s) • tangentVector s`
(`oppositeSurfaceData_angleImage_eq_withDensity`); the extra minus sign is exactly
`tangentVector_add_pi`.

The two variants `oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft` and
`…_of_openRight` drop the vertex information at one endpoint of the window by exhausting the
window from the other side with `measure_angleImage_eq_of_iUnion`.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- An Archimedean step used to exhaust an open interval endpoint. -/
private theorem exists_nat_div_add_two_lt {d e : ℝ} (he : 0 < e) :
    ∃ n : ℕ, d / (n + 2) < e := by
  obtain ⟨n, hn⟩ := exists_nat_gt (d / e)
  refine ⟨n, ?_⟩
  have hpos : (0 : ℝ) < n + 2 := by positivity
  rw [div_lt_iff₀ hpos]
  have h : d / e < n + 2 := by linarith
  rw [div_lt_iff₀ he] at h
  linarith

/-- The angular projection reads the opposite surface measure through the `π`-shifted window. -/
theorem oppositeSurfaceData_angleImage (K : ConvexBody Point) {S : Set ℝ}
    (hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      surfaceAreaMeasure K
        ((fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ s + Real.pi) '' S)) := by
  have hm : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  have hpre : (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      (fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ s + Real.pi) '' S) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hsx⟩
      refine ⟨s + Real.pi, ⟨s, hs, rfl⟩, ?_⟩
      rw [Real.Angle.coe_add, hsx]
      abel
    · rintro ⟨r, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [Real.Angle.coe_add]
      abel
  change Measure.map (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle))
    (surfaceAreaMeasure K) _ = _
  rw [Measure.map_apply hm hS, hpre]

/-- Suppose that on the angular window `(π + a, π + b]`, of at most one turn, the positive vertex
of `K` at normal `π + s` is traced by a curve `F` with derivative `-(g s) • v_s`, where `g` is
continuous and nonnegative.  Then the opposite surface measure of the angular image of a
measurable `S ⊆ (a, b]` is the weighted Lebesgue measure of `S` for any weight `f` agreeing with
`g` on the open window. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioc a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Icc a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hemb : MeasurableEmbedding fun s : ℝ ↦ s + Real.pi :=
    (MeasurableEquiv.addRight Real.pi).measurableEmbedding
  have himg : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hS hSsub
  have hSmeas : MeasurableSet ((fun s : ℝ ↦ s + Real.pi) '' S) := hemb.measurableSet_image' hS
  have hSsub' : (fun s : ℝ ↦ s + Real.pi) '' S ⊆ Set.Ioc (a + Real.pi) (b + Real.pi) := by
    rintro r ⟨s, hs, rfl⟩
    exact ⟨by linarith [(hSsub hs).1], by linarith [(hSsub hs).2]⟩
  -- the vertex curve of the shifted window and its derivative
  have hshift : ∀ r : ℝ, tangentVector ((r - Real.pi : ℝ) : Real.Angle) =
      -tangentVector (r : Real.Angle) := by
    intro r
    have h := tangentVector_add_pi (r - Real.pi)
    rw [show r - Real.pi + Real.pi = r from by ring] at h
    rw [h, neg_neg]
  have hF' : ∀ r : ℝ, HasDerivAt (fun r : ℝ ↦ F (r - Real.pi))
      (g (r - Real.pi) • tangentVector (r : Real.Angle)) r := by
    intro r
    have h := (hF (r - Real.pi)).scomp r ((hasDerivAt_id r).sub_const Real.pi)
    rw [hshift r] at h
    refine h.congr_deriv ?_
    module
  have hvertex' : ∀ r ∈ Set.Icc (a + Real.pi) (b + Real.pi),
      (edgeVertices K (r : Real.Angle)).1 = F (r - Real.pi) := by
    intro r hr
    have h := hvertex (r - Real.pi) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rw [show Real.pi + (r - Real.pi) = r from by ring] at h
    exact h
  have hmain := surfaceAreaMeasure_angleImage_eq_setLIntegral K (a := a + Real.pi)
    (b := b + Real.pi) (by linarith) (by linarith) (fun r ↦ F (r - Real.pi))
    (fun r ↦ g (r - Real.pi)) hF' (hg.comp (continuous_id.sub continuous_const))
    (fun r hr ↦ hgnn (r - Real.pi) ⟨by linarith [hr.1], by linarith [hr.2]⟩) hvertex'
    hSmeas hSsub'
  -- change variables back to the unshifted window
  rw [oppositeSurfaceData_angleImage K himg, hmain,
    setLIntegral_comp_sub_right (fun s ↦ ENNReal.ofReal (g s)) Real.pi,
    hemb.injective.preimage_image, withDensity_apply _ hS]
  -- the two densities agree off the right endpoint
  refine (lintegral_congr_ae ?_).symm
  have hne : ∀ᵐ s ∂volume.restrict S, s ∈ Set.Ioo a b := by
    refine ae_restrict_mem_of_countable_diff hS (Set.countable_singleton b) ?_
    rintro s ⟨hs, hsA⟩
    have h := hSsub hs
    rcases eq_or_lt_of_le h.2 with heq | hlt
    · exact heq
    · exact absurd (Set.mem_Ioo.2 ⟨h.1, hlt⟩) hsA
  filter_upwards [hne] with s hs
  rw [hfg s hs]

/-- The variant of `oppositeSurfaceData_angleImage_eq_withDensity` whose left endpoint carries no
vertex information: the window is exhausted from the right. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point)
    (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioc a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Ioc a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hba : 0 < b - a := by linarith
  have hpos : ∀ n : ℕ, 0 < (b - a) / (n + 2) := fun n ↦ by positivity
  have hlt : ∀ n : ℕ, a + (b - a) / (n + 2) < b := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / 2 := by gcongr; linarith
    linarith
  refine measure_angleImage_eq_of_iUnion (μ := (oppositeSurfaceData K).1)
    (J := fun n : ℕ ↦ Set.Ioc (a + (b - a) / (n + 2)) b)
    (ν := volume.withDensity (fun s ↦ ENNReal.ofReal (f s))) ?_ (fun n ↦ measurableSet_Ioc) ?_
    S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc ?_ le_rfl
    have hmn' : ((m : ℝ)) ≤ n := Nat.cast_le.2 hmn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / ((m : ℝ) + 2) := by gcongr
    linarith
  · intro n T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity K (hlt n) (by linarith [hpos n])
      F f g hF hg (fun s hs ↦ hgnn s ⟨by linarith [hs.1, hpos n], hs.2⟩)
      (fun s hs ↦ hfg s ⟨by linarith [hs.1, hpos n], hs.2⟩)
      (fun s hs ↦ hvertex s ⟨by linarith [hs.1, hpos n], hs.2⟩) hT hTsub
  · intro s hs
    obtain ⟨n, hn⟩ := exists_nat_div_add_two_lt (d := b - a) (e := s - a)
      (by linarith [(hSsub hs).1])
    exact Set.mem_iUnion.2 ⟨n, ⟨by linarith, (hSsub hs).2⟩⟩

/-- The variant of `oppositeSurfaceData_angleImage_eq_withDensity` whose right endpoint carries no
vertex information: the window is exhausted from the left. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity_of_openRight (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point)
    (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioo a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Ico a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hba : 0 < b - a := by linarith
  have hpos : ∀ n : ℕ, 0 < (b - a) / (n + 2) := fun n ↦ by positivity
  have hlt : ∀ n : ℕ, a < b - (b - a) / (n + 2) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / 2 := by gcongr; linarith
    linarith
  refine measure_angleImage_eq_of_iUnion (μ := (oppositeSurfaceData K).1)
    (J := fun n : ℕ ↦ Set.Ioc a (b - (b - a) / (n + 2)))
    (ν := volume.withDensity (fun s ↦ ENNReal.ofReal (f s))) ?_ (fun n ↦ measurableSet_Ioc) ?_
    S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc le_rfl ?_
    have hmn' : ((m : ℝ)) ≤ n := Nat.cast_le.2 hmn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / ((m : ℝ) + 2) := by gcongr
    linarith
  · intro n T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity K (hlt n) (by linarith [hpos n])
      F f g hF hg (fun s hs ↦ hgnn s ⟨hs.1, by linarith [hs.2, hpos n]⟩)
      (fun s hs ↦ hfg s ⟨hs.1, by linarith [hs.2, hpos n]⟩)
      (fun s hs ↦ hvertex s ⟨hs.1, by linarith [hs.2, hpos n]⟩) hT hTsub
  · intro s hs
    obtain ⟨n, hn⟩ := exists_nat_div_add_two_lt (d := b - a) (e := b - s)
      (by linarith [(hSsub hs).2])
    exact Set.mem_iUnion.2 ⟨n, ⟨(hSsub hs).1, by linarith⟩⟩

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Convex.SupportArea`.
* `Convex.Linearity`.
* `Convex.MixedArea`.
* `Convex.TangentLinePath`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The area of a convex body as a support-function surface integral

The planar area of a nonempty compact convex set is one half of the integral of its support
function against its surface area measure. The identity is proved for finite convex hulls by
fanning the polygon into triangles over an interior base point, and then transported to an
arbitrary body by polygon approximation and weak convergence of surface measures. The same
integral, taken with the two bodies decoupled, is convex-bilinear.
-/

public section

noncomputable section

open scoped unitInterval Pointwise Topology
open MeasureTheory Filter

namespace MovingSofa

private theorem one_lt_finrank_point : 1 < Module.finrank ℝ Point := by
  simp [Point]

private theorem normalVector_ne_zero (t : Real.Angle) : normalVector t ≠ 0 := by
  intro h
  have hone := norm_normalVector t
  rw [h, norm_zero] at hone
  exact zero_ne_one hone

/-- The ordered endpoints of an exposed edge differ by its length in the positive tangent
direction. -/
theorem edgeVertices_fst_sub_snd_eq_dist_smul_tangentVector
    (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 - (edgeVertices K t).2 =
      dist (edgeVertices K t).1 (edgeVertices K t).2 • tangentVector t := by
  let a := (edgeVertices K t).1
  let b := (edgeVertices K t).2
  let r := inner ℝ (a - b) (tangentVector t)
  have hnormal : inner ℝ (a - b) (normalVector t) = 0 := by
    dsimp only [a, b]
    rw [inner_sub_left]
    rw [(edgeVertices_fst_mem K t).2, (edgeVertices_snd_mem K t).2, sub_self]
  have hdecomp := inner_normalVector_smul_add_inner_tangentVector_smul (a - b) t
  have hvec : r • tangentVector t = a - b := by
    simpa only [r, hnormal, zero_smul, zero_add] using hdecomp
  have hr : 0 ≤ r := by
    let S : Set ℝ :=
      (fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t
    simp only [r, inner_sub_left, a, b, inner_edgeVertices_fst_tangent,
      inner_edgeVertices_snd_tangent]
    have hcompact : IsCompact S :=
      (isCompact_exposedEdge K t).image (continuous_id.inner continuous_const)
    apply sub_nonneg.mpr
    simpa only [S] using
      (csInf_le_csSup (s := S) ((exposedEdge_nonempty K t).image _)
        (hb := hcompact.bddBelow) (ha := hcompact.bddAbove))
  have htangent : ‖tangentVector t‖ = 1 := by
    induction t using Real.Angle.induction_on with
    | _ t =>
      rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
      rw [EuclideanSpace.norm_sq_eq]
      simp [tangentVector, frame, Fin.sum_univ_two]
  have hnorm := congrArg norm hvec
  have hre : r = dist a b := by
    simpa only [norm_smul, htangent, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hr, dist_eq_norm] using hnorm
  simpa only [a, b, ← hre] using hvec.symm

/-- The half support integral is convex-bilinear in the two body arguments. -/
theorem supportIntegral_bilinear :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) * ∫ t,
          supportValue K t ∂surfaceAreaMeasure L) := by
  have hcont (K : ConvexBody Point) : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint (K L : ConvexBody Point) :
      Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure L) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
    exact (hcont K).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  constructor
  · intro K t L M
    have hmeasure := surfaceAreaMeasure_convexBodyCombination t L M
    change (1 / 2 : ℝ) * (∫ u, supportValue K u ∂surfaceAreaMeasure
        (convexBodyCombination t L M)) = _
    simp only [realCombination]
    rw [hmeasure, integral_add_measure
      ((hint K L).smul_measure ENNReal.ofReal_ne_top)
      ((hint K M).smul_measure ENNReal.ofReal_ne_top)]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal,
      sub_nonneg.mpr (show (t : ℝ) ≤ 1 from t.property.2), t.property.1]
    ring
  · intro L t K M
    change (1 / 2 : ℝ) * (∫ u, supportValue (convexBodyCombination t K M) u
      ∂surfaceAreaMeasure L) = _
    simp only [realCombination]
    have hfun : (fun u : Real.Angle ↦ supportValue (convexBodyCombination t K M) u) =
        fun u ↦ (1 - (t : ℝ)) * supportValue K u + (t : ℝ) * supportValue M u := by
      funext u
      exact supportValue_convexBodyCombination t K M u
    rw [hfun, integral_add ((hint K L).const_mul _) ((hint M L).const_mul _),
      integral_const_mul, integral_const_mul]
    ring

/-- The mixed support integral is Hausdorff continuous in the two bodies simultaneously. -/
theorem tendsto_integral_supportValue_of_hausdorff_pair
    (P Q : ℕ → ConvexBody Point) (K L : ConvexBody Point)
    (hPK : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0))
    (hQL : Tendsto (fun n ↦ Metric.hausdorffDist (Q n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ u, supportValue (P n) u ∂surfaceAreaMeasure (Q n)) atTop
      (𝓝 (∫ u, supportValue K u ∂surfaceAreaMeasure L)) := by
  have hcont (M : ConvexBody Point) : Continuous (supportValue M) :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hint (M N : ConvexBody Point) : Integrable (supportValue M) (surfaceAreaMeasure N) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure N) := (surfaceAreaMeasure_face_union N).1
    exact (hcont M).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hmass : Tendsto (fun n ↦ (surfaceAreaMeasure (Q n)).real Set.univ) atTop
      (𝓝 ((surfaceAreaMeasure L).real Set.univ)) := by
    simpa using surfaceAreaMeasure_weak_continuity Q L hQL (fun _ ↦ (1 : ℝ)) continuous_const
  have hbound (n : ℕ) :
      ‖∫ u, supportValue (P n) u - supportValue K u ∂surfaceAreaMeasure (Q n)‖ ≤
        Metric.hausdorffDist (P n : Set Point) (K : Set Point) *
          (surfaceAreaMeasure (Q n)).real Set.univ := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure (Q n)) :=
      (surfaceAreaMeasure_face_union (Q n)).1
    apply norm_integral_le_of_norm_le_const
    filter_upwards [] with u
    simpa only [Real.norm_eq_abs, vectorSupport, supportValue] using
      (compactSet_support_continuity (P n) K (P n).nonempty
        (P n).isCompact K.nonempty K.isCompact).2.1 (normalVector u) (norm_normalVector u)
  have herror : Tendsto
      (fun n ↦ ∫ u, supportValue (P n) u - supportValue K u ∂surfaceAreaMeasure (Q n))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hbound (by simpa using hPK.mul hmass)
  have hfixed := surfaceAreaMeasure_weak_continuity Q L hQL (supportValue K) (hcont K)
  have hsum := herror.add hfixed
  simp only [zero_add] at hsum
  convert hsum using 1
  funext n
  rw [integral_sub (hint (P n) (Q n)) (hint K (Q n)), sub_add_cancel]

/-- The support integral of a body against its own surface measure is Hausdorff continuous. -/
theorem tendsto_integral_supportValue_of_hausdorff
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ u, supportValue (K n) u ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ u, supportValue L u ∂surfaceAreaMeasure L)) :=
  tendsto_integral_supportValue_of_hausdorff_pair K K L L hlim hlim

/-- For a finite convex hull, the support integral is the finite sum over its proper edges. -/
private theorem integral_supportValue_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    ∫ t, supportValue K t ∂surfaceAreaMeasure K =
      Finset.sum (finite_properEdgeNormal_angles K V hKV).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * supportValue K t) := by
  classical
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hae : ∀ᵐ t ∂surfaceAreaMeasure K, t ∈ N := by
    rw [ae_iff]
    simpa only [N, Set.mem_ofPred_eq, not_ne_iff] using
      surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull K V hKV
  have hrestrict : (surfaceAreaMeasure K).restrict N = surfaceAreaMeasure K :=
    Measure.restrict_eq_self_of_ae_mem hae
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  calc
    ∫ t, supportValue K t ∂surfaceAreaMeasure K =
        ∫ t in N, supportValue K t ∂surfaceAreaMeasure K := by
          rw [hrestrict]
    _ = _ := by
      rw [show N = ↑hNfinite.toFinset by ext t; simp [N]]
      exact MeasureTheory.setIntegral_finset _
        (μ := surfaceAreaMeasure K) (f := supportValue K) IntegrableOn.finset

/-- On a finite convex hull, each coefficient in the support sum is the corresponding edge
length. -/
theorem integral_supportValue_surfaceAreaMeasure_eq_sum_edgeLength
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    ∫ t, supportValue K t ∂surfaceAreaMeasure K =
      Finset.sum (finite_properEdgeNormal_angles K V hKV).toFinset
        (fun t ↦ dist (edgeVertices K t).1 (edgeVertices K t).2 * supportValue K t) := by
  rw [integral_supportValue_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV]
  apply Finset.sum_congr rfl
  intro t _
  change (surfaceAreaMeasure K {t}).toReal * supportValue K t = _
  rw [(surfaceAreaMeasure_atom_length K t).2.1, ENNReal.toReal_ofReal dist_nonneg]

/-- The total tangent vector of the surface-area measure vanishes. -/
theorem integral_tangentVector_surfaceAreaMeasure_eq_zero (K : ConvexBody Point) :
    ∫ t, tangentVector t ∂surfaceAreaMeasure K = 0 := by
  have himage :
      (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 (2 * Real.pi) = Set.univ := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioc, Set.mem_univ, iff_true]
    let _ : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
    let s := AddCircle.equivIoc (2 * Real.pi) 0 u
    have hs : (s : ℝ) ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      simpa using s.property
    exact ⟨s, hs, AddCircle.coe_equivIoc⟩
  rw [← setIntegral_univ, ← himage,
    integral_tangentVector_surfaceAreaMeasure K Real.two_pi_pos (by simp)]
  simp

/-- Every non-generating boundary point of a two-dimensional finite convex hull lies on a
proper exposed edge. -/
theorem exists_mem_properExposedEdge_of_mem_frontier
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (hK : (interior (K : Set Point)).Nonempty) {p : Point}
    (hp : p ∈ frontier (K : Set Point)) (hpV : p ∉ V) :
    ∃ t : Real.Angle,
      (edgeVertices K t).1 ≠ (edgeVertices K t).2 ∧ p ∈ exposedEdge K t := by
  obtain ⟨t, hpt⟩ := exists_mem_exposedEdge_of_mem_frontier K hK hp
  refine ⟨t, ?_, hpt⟩
  intro heq
  rw [exposedEdge_eq_segment_edgeVertices, heq, segment_same] at hpt
  apply hpV
  simpa only [Set.mem_singleton_iff] using
    hpt.symm ▸ (edgeVertices_mem_of_eq_convexHull K V hKV t).2

/-- The support-area identity holds for a singleton convex body. -/
theorem convexBody_area_support_integral_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  obtain ⟨p, hp⟩ := K.nonempty
  have hsingleton : (K : Set Point) = {p} := hK.eq_singleton_of_mem hp
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK, integral_zero_measure, mul_zero]
  simp [ClassicalResults.area, hsingleton]

/-- The support-area identity holds for a nondegenerate segment presentation. -/
theorem convexBody_area_support_integral_of_segmentPresentation
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  have hline : (K : Set Point) ⊆
      {p | inner ℝ p (normalVector d.2.2) = inner ℝ d.1 (normalVector d.2.2)} := by
    intro p hp
    rw [hd.2.1, segment_eq_image'] at hp
    obtain ⟨s, _, rfl⟩ := hp
    change inner ℝ (d.1 + s • (d.2.1 - d.1)) (normalVector d.2.2) = _
    rw [inner_add_left, inner_smul_left, hd.2.2, mul_zero, add_zero]
  have hvolume : volume (K : Set Point) = 0 :=
    measure_mono_null hline
      (volume.addHaar_setOf_real_inner_eq (normalVector_ne_zero d.2.2) _)
  have hnormalPi : normalVector (d.2.2 + (Real.pi : Real.Angle)) =
      -normalVector d.2.2 := by
    induction d.2.2 using Real.Angle.induction_on with
    | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
  have hdmem : d.1 ∈ exposedEdge K d.2.2 := by
    rw [exposedEdge_eq_segment_of_orthogonal K d hd d.2.2 hd.2.2, hd.2.1]
    exact left_mem_segment ℝ _ _
  have hpimem : d.1 ∈ exposedEdge K (d.2.2 + (Real.pi : Real.Angle)) := by
    rw [exposedEdge_eq_segment_of_orthogonal K d hd _ (by
      rw [hnormalPi, inner_neg_right, hd.2.2, neg_zero]), hd.2.1]
    exact left_mem_segment ℝ _ _
  have hsupport : supportValue K d.2.2 +
      supportValue K (d.2.2 + (Real.pi : Real.Angle)) = 0 := by
    rw [← hdmem.2, ← hpimem.2, hnormalPi, inner_neg_right, add_neg_cancel]
  have hint₁ : Integrable (supportValue K) (Measure.dirac d.2.2) :=
    integrable_dirac (by simp)
  have hint₂ : Integrable (supportValue K)
      (Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) := integrable_dirac (by simp)
  rw [show ClassicalResults.area (K : Set Point) = 0 by
    simp [ClassicalResults.area, hvolume],
    surfaceAreaMeasure_eq_segmentPresentation K d hd]
  rw [integral_smul_measure, integral_add_measure hint₁ hint₂]
  simp [hsupport]

/-- The support-area identity for finite convex hulls extends to every convex body. -/
theorem convexBody_area_support_integral_of_finiteHull
    (hpolygon : ∀ (P : ConvexBody Point) (V : Finset Point), V.Nonempty →
      (P : Set Point) = convexHull ℝ (V : Set Point) →
      ClassicalResults.area (P : Set Point) =
        (1 / 2 : ℝ) * ∫ t, supportValue P t ∂surfaceAreaMeasure P) :
    ∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  intro K
  obtain ⟨V, P, hP, hdist⟩ := exists_facePreserving_polygonApproximation K ∅
  have hlim : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  have harea := convexArea_hausdorff_continuity P K hlim
  have hintegral := (tendsto_integral_supportValue_of_hausdorff P K hlim).const_mul (1 / 2)
  have heq (n : ℕ) : ClassicalResults.area (P n : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue (P n) t ∂surfaceAreaMeasure (P n) :=
    hpolygon (P n) (V n) (hP n).1 (hP n).2.1
  exact tendsto_nhds_unique harea
    (hintegral.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm))

/-- The area identity and the explicit support integral's bilinearity give quadraticity. -/
theorem convexBody_area_support_integral_of_area_identity
    (harea : ∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K) :
    (∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K) ∧
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦
        (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure L) ∧
    IsQuadraticFunctional convexBodyCombination
      (fun K : ConvexBody Point ↦ ClassicalResults.area (K : Set Point)) := by
  refine ⟨harea, supportIntegral_bilinear, ?_⟩
  exact ⟨_, supportIntegral_bilinear, harea⟩

/-- An exposed-edge point realizes the support value. -/
theorem inner_eq_supportValue_of_mem_exposedEdge (K : ConvexBody Point) (t : Real.Angle)
    {p : Point} (hp : p ∈ exposedEdge K t) :
    inner ℝ p (normalVector t) = supportValue K t := hp.2

/-- An interior base point lies strictly inside every supporting line. -/
theorem inner_lt_supportValue_of_mem_interior (K : ConvexBody Point) {o : Point}
    (ho : o ∈ interior (K : Set Point)) (t : Real.Angle) :
    inner ℝ o (normalVector t) < supportValue K t := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior o ho
  have hnorm : inner ℝ (normalVector t) (normalVector t) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_normalVector]
    norm_num
  have hpball : o + (ε / 2) • normalVector t ∈ Metric.ball o ε := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      norm_normalVector, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hle := inner_le_supportValue K (interior_subset (hball hpball)) t
  rw [inner_add_left, real_inner_smul_left, hnorm, mul_one] at hle
  linarith

/-- The oriented determinant of a triangle with one side in the positive tangent direction. -/
private theorem planeCrossProduct_add_smul_tangentVector (w : Point) (d : ℝ)
    (t : Real.Angle) :
    planeCrossProduct w (w + d • tangentVector t) = d * inner ℝ w (normalVector t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp [planeCrossProduct, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.inner_apply, Fin.sum_univ_two, normalVector, tangentVector, frame,
      Real.Angle.cos_coe, Real.Angle.sin_coe]
    ring

/-- Each exposed-edge summand is the oriented determinant of its triangle over the base
point. -/
theorem edgeLength_mul_supportValue_sub_eq_planeCrossProduct
    (K : ConvexBody Point) (o : Point) (t : Real.Angle) :
    dist (edgeVertices K t).1 (edgeVertices K t).2 *
        (supportValue K t - inner ℝ o (normalVector t)) =
      planeCrossProduct ((edgeVertices K t).2 - o) ((edgeVertices K t).1 - o) := by
  have hedge := edgeVertices_fst_sub_snd_eq_dist_smul_tangentVector K t
  have ha : (edgeVertices K t).1 - o =
      ((edgeVertices K t).2 - o) +
        dist (edgeVertices K t).1 (edgeVertices K t).2 • tangentVector t := by
    rw [← hedge]
    abel
  rw [ha, planeCrossProduct_add_smul_tangentVector, inner_sub_left,
    inner_eq_supportValue_of_mem_exposedEdge K t (edgeVertices_snd_mem K t)]

/-- The fan triangle over an exposed edge, based at a chosen interior point. -/
private def edgeTriangle (K : ConvexBody Point) (o : Point) (t : Real.Angle) : Set Point :=
  convexHull ℝ ({o, (edgeVertices K t).2, (edgeVertices K t).1} : Set Point)

/-- The finitely many rays from a base point through the generating vertices. -/
private def vertexRayUnion (o : Point) (V : Finset Point) : Set Point :=
  ⋃ v : ↥V, (o +ᵥ (ℝ ∙ ((v : Point) - o) : Set Point))

/-- The vertex rays through a base point have planar area zero. -/
private theorem volume_vertexRayUnion (o : Point) (V : Finset Point) :
    volume (vertexRayUnion o V) = 0 := by
  exact volume.addHaar_iUnion_vadd_span_singleton one_lt_finrank_point o _

/-- Away from the finitely many vertex rays, every polygon point lies in a proper-edge fan
triangle over the base point. -/
private theorem exists_mem_edgeTriangle_of_notMem_vertexRayUnion
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {o : Point} (ho : o ∈ interior (K : Set Point)) {x : Point}
    (hx : x ∈ (K : Set Point)) (hxline : x ∉ vertexRayUnion o V) :
    ∃ t : Real.Angle,
      (edgeVertices K t).1 ≠ (edgeVertices K t).2 ∧ x ∈ edgeTriangle K o t := by
  obtain ⟨p, hpfront, hxp⟩ := K.convex.exists_mem_frontier_mem_segment K.isCompact ho hx
  have hpV : p ∉ V := by
    intro hpV
    apply hxline
    refine Set.mem_iUnion.2 ⟨⟨p, hpV⟩, ?_⟩
    rw [segment_eq_image'] at hxp
    obtain ⟨c, _, hc⟩ := hxp
    have hc' : o + c • (p - o) = x := hc
    refine ⟨x - o, ?_, by simp only [vadd_eq_add]; abel⟩
    exact Submodule.mem_span_singleton.2 ⟨c, by rw [← hc']; abel⟩
  obtain ⟨t, htproper, hpt⟩ :=
    exists_mem_properExposedEdge_of_mem_frontier K V hKV ⟨o, ho⟩ hpfront hpV
  refine ⟨t, htproper, ?_⟩
  have hpT : p ∈ edgeTriangle K o t := by
    rw [exposedEdge_eq_segment_edgeVertices] at hpt
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) hpt
  exact (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (by simp)) hpT hxp

/-- Two unit normals annihilating a common nonzero vector have vanishing angular sine. -/
private theorem sin_sub_eq_zero_of_inner_normalVector_eq_zero {u : Point} (hu : u ≠ 0)
    {s t : Real.Angle} (h1 : inner ℝ u (normalVector s) = 0)
    (h2 : inner ℝ u (normalVector t) = 0) : (t - s).sin = 0 := by
  induction s using Real.Angle.induction_on with
  | _ s =>
    induction t using Real.Angle.induction_on with
    | _ t =>
      have hu' : ¬(u 0 = 0 ∧ u 1 = 0) := by
        rintro ⟨ha, hb⟩
        refine hu ?_
        ext i
        fin_cases i <;> simpa
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
        normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
        Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
      rw [← Real.Angle.coe_sub, Real.Angle.sin_coe, Real.sin_sub]
      have hd0 : (Real.sin t * Real.cos s - Real.cos t * Real.sin s) * u 0 = 0 := by
        linear_combination Real.sin t * h1 - Real.sin s * h2
      have hd1 : (Real.sin t * Real.cos s - Real.cos t * Real.sin s) * u 1 = 0 := by
        linear_combination (-Real.cos t) * h1 + Real.cos s * h2
      rcases mul_eq_zero.mp hd0 with hD | hu0
      · exact hD
      rcases mul_eq_zero.mp hd1 with hD | hu1
      · exact hD
      exact absurd ⟨hu0, hu1⟩ hu'

/-- Distinct normal directions share at most one exposed-edge point. -/
theorem subsingleton_exposedEdge_inter (K : ConvexBody Point) {o : Point}
    (ho : o ∈ interior (K : Set Point)) {s t : Real.Angle} (hst : s ≠ t) :
    (exposedEdge K s ∩ exposedEdge K t).Subsingleton := by
  intro z hz w hw
  by_contra hzw
  have h1 : inner ℝ (z - w) (normalVector s) = 0 := by
    rw [inner_sub_left, inner_eq_supportValue_of_mem_exposedEdge K s hz.1,
      inner_eq_supportValue_of_mem_exposedEdge K s hw.1, sub_self]
  have h2 : inner ℝ (z - w) (normalVector t) = 0 := by
    rw [inner_sub_left, inner_eq_supportValue_of_mem_exposedEdge K t hz.2,
      inner_eq_supportValue_of_mem_exposedEdge K t hw.2, sub_self]
  have hsin := sin_sub_eq_zero_of_inner_normalVector_eq_zero (sub_ne_zero.mpr hzw) h1 h2
  rcases Real.Angle.sin_eq_zero_iff.mp hsin with hz0 | hpi
  · exact hst (by linear_combination (norm := abel) -hz0)
  · have ht : t = s + ((Real.pi : ℝ) : Real.Angle) := by
      linear_combination (norm := abel) hpi
    have hopp : normalVector t = -normalVector s := by
      rw [ht, normalVector_add_pi_angle]
    have hsum : supportValue K s + supportValue K t = 0 := by
      rw [← inner_eq_supportValue_of_mem_exposedEdge K s hz.1,
        ← inner_eq_supportValue_of_mem_exposedEdge K t hz.2, hopp, inner_neg_right,
        add_neg_cancel]
    have hs' := inner_lt_supportValue_of_mem_interior K ho s
    have ht' := inner_lt_supportValue_of_mem_interior K ho t
    rw [hopp, inner_neg_right] at ht'
    linarith

/-- A fan triangle is the union of the segments from the base point to its exposed edge. -/
private theorem edgeTriangle_eq_iUnion_segment (K : ConvexBody Point) (o : Point)
    (t : Real.Angle) :
    edgeTriangle K o t = ⋃ z ∈ exposedEdge K t, segment ℝ o z := by
  rw [edgeTriangle, exposedEdge_eq_segment_edgeVertices,
    show ({o, (edgeVertices K t).2, (edgeVertices K t).1} : Set Point) =
      insert o {(edgeVertices K t).2, (edgeVertices K t).1} from rfl,
    convexHull_insert ⟨(edgeVertices K t).2, by simp⟩, convexHull_pair,
    convexJoin_singleton_left]

/-- Fan triangles over distinct proper edges meet in a planar null set. -/
private theorem volume_edgeTriangle_inter_eq_zero (K : ConvexBody Point) {o : Point}
    (ho : o ∈ interior (K : Set Point)) {s t : Real.Angle} (hst : s ≠ t) :
    volume (edgeTriangle K o s ∩ edgeTriangle K o t) = 0 := by
  classical
  have hsub : ∀ x ∈ edgeTriangle K o s ∩ edgeTriangle K o t,
      x = o ∨ ∃ z ∈ exposedEdge K s ∩ exposedEdge K t, x ∈ segment ℝ o z := by
    rintro x ⟨hxs, hxt⟩
    rw [edgeTriangle_eq_iUnion_segment] at hxs hxt
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxs
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxt
    by_cases hxo : x = o
    · exact Or.inl hxo
    have hzw : z = w := K.convex.eq_of_mem_frontier_of_mem_segment K.isClosed ho hxo
      (exposedEdge_subset_frontier K s hz)
      (exposedEdge_subset_frontier K t hw) hxz hxw
    exact Or.inr ⟨z, ⟨hz, hzw ▸ hw⟩, hxz⟩
  by_cases hne : (exposedEdge K s ∩ exposedEdge K t).Nonempty
  · obtain ⟨q, hq⟩ := hne
    refine measure_mono_null (t := (o +ᵥ (ℝ ∙ (q - o) : Set Point))) ?_ ?_
    · intro x hx
      rcases hsub x hx with hxo | ⟨z, hzq, hxz⟩
      · exact ⟨0, Submodule.zero_mem _, by simp only [vadd_eq_add, hxo]; abel⟩
      · have hzeq : z = q := subsingleton_exposedEdge_inter K ho hst hzq hq
        subst hzeq
        rw [segment_eq_image'] at hxz
        obtain ⟨c, _, hc⟩ := hxz
        have hc' : o + c • (z - o) = x := hc
        exact ⟨x - o, Submodule.mem_span_singleton.2 ⟨c, by rw [← hc']; abel⟩,
          by simp only [vadd_eq_add]; abel⟩
    · exact volume.addHaar_vadd_span_singleton one_lt_finrank_point o (q - o)
  · refine measure_mono_null (t := ({o} : Set Point)) ?_ (measure_singleton o)
    intro x hx
    rcases hsub x hx with hxo | ⟨z, hz, _⟩
    · exact hxo
    · exact absurd ⟨z, hz⟩ hne

/-- The coordinate tangent integral of a surface measure vanishes. -/
theorem integral_tangentCoordinate_surfaceAreaMeasure_eq_zero (K : ConvexBody Point)
    (i : Fin 2) : ∫ t, tangentVector t i ∂surfaceAreaMeasure K = 0 := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcont : Continuous (fun u : Real.Angle ↦ tangentVector u) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro j
    fin_cases j
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u) (surfaceAreaMeasure K) :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hi := ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
  change (∫ u, tangentVector u i ∂surfaceAreaMeasure K) =
    (∫ u, tangentVector u ∂surfaceAreaMeasure K) i at hi
  rw [hi, integral_tangentVector_surfaceAreaMeasure_eq_zero K]
  simp

/-- Atomic surface mass is the corresponding edge length. -/
private theorem surfaceAreaMeasure_real_singleton (K : ConvexBody Point) (t : Real.Angle) :
    (surfaceAreaMeasure K).real {t} = dist (edgeVertices K t).1 (edgeVertices K t).2 := by
  change (surfaceAreaMeasure K {t}).toReal = _
  rw [(surfaceAreaMeasure_atom_length K t).2.1, ENNReal.toReal_ofReal dist_nonneg]

/-- The proper-edge lengths of a polygon weight its tangent coordinates to zero. -/
theorem sum_edgeLength_mul_tangentCoordinate_eq_zero (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) (i : Fin 2) :
    ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      dist (edgeVertices K t).1 (edgeVertices K t).2 * tangentVector t i = 0 := by
  classical
  have h := integral_tangentCoordinate_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV i
    Set.univ MeasurableSet.univ
  rw [setIntegral_univ, integral_tangentCoordinate_surfaceAreaMeasure_eq_zero K i] at h
  rw [show (finite_properEdgeNormal_angles K V hKV).toFinset =
      ((finite_properEdgeNormal_angles K V hKV).inter_of_left Set.univ).toFinset from by
    ext u
    simp]
  refine Eq.trans (Finset.sum_congr rfl fun u _ ↦ ?_) h.symm
  rw [surfaceAreaMeasure_real_singleton]

/-- The proper-edge lengths of a polygon weight its normal directions to zero. -/
theorem sum_edgeLength_mul_inner_normalVector_eq_zero (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) (o : Point) :
    ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      dist (edgeVertices K t).1 (edgeVertices K t).2 * inner ℝ o (normalVector t) = 0 := by
  have hkey : ∀ t : Real.Angle, inner ℝ o (normalVector t) =
      o 0 * tangentVector t 1 - o 1 * tangentVector t 0 := by
    intro t
    induction t using Real.Angle.induction_on with
    | _ t =>
      simp [PiLp.inner_apply, Fin.sum_univ_two, normalVector, tangentVector, frame,
        Real.Angle.cos_coe, Real.Angle.sin_coe]
      ring
  have h0 := sum_edgeLength_mul_tangentCoordinate_eq_zero K V hKV 0
  have h1 := sum_edgeLength_mul_tangentCoordinate_eq_zero K V hKV 1
  calc ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        dist (edgeVertices K t).1 (edgeVertices K t).2 * inner ℝ o (normalVector t)
      = o 0 * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
            dist (edgeVertices K t).1 (edgeVertices K t).2 * tangentVector t 1 -
          o 1 * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
            dist (edgeVertices K t).1 (edgeVertices K t).2 * tangentVector t 0 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [hkey t]
        ring
    _ = 0 := by rw [h0, h1]; ring

/-- The support-area identity for a polygon with interior, by fan triangulation. -/
theorem convexBody_area_support_integral_of_convexHull_interior
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (hint : (interior (K : Set Point)).Nonempty) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  classical
  obtain ⟨o, ho⟩ := hint
  have hmemF : ∀ t : Real.Angle,
      t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset ↔
        (edgeVertices K t).1 ≠ (edgeVertices K t).2 := by
    intro t
    simp
  have hpos : ∀ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      0 < dist (edgeVertices K t).1 (edgeVertices K t).2 *
        (supportValue K t - inner ℝ o (normalVector t)) := by
    intro t htF
    exact mul_pos (dist_pos.mpr ((hmemF t).1 htF))
      (sub_pos.mpr (inner_lt_supportValue_of_mem_interior K ho t))
  have hTvol : ∀ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      volume (edgeTriangle K o t) = ENNReal.ofReal
        (dist (edgeVertices K t).1 (edgeVertices K t).2 *
          (supportValue K t - inner ℝ o (normalVector t)) / 2) := by
    intro t htF
    rw [edgeTriangle, EuclideanSpace.volume_convexHull_triple]
    congr 1
    rw [show ((edgeVertices K t).2 - o) 0 * ((edgeVertices K t).1 - o) 1 -
          ((edgeVertices K t).1 - o) 0 * ((edgeVertices K t).2 - o) 1 =
        planeCrossProduct ((edgeVertices K t).2 - o) ((edgeVertices K t).1 - o) from by
      simp only [planeCrossProduct]
      ring, ← edgeLength_mul_supportValue_sub_eq_planeCrossProduct K o t,
      abs_of_pos (hpos t htF)]
  have hTsubK : ∀ t : Real.Angle, edgeTriangle K o t ⊆ (K : Set Point) := by
    intro t
    rw [edgeTriangle]
    refine convexHull_min ?_ K.convex
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact interior_subset ho
    · exact (edgeVertices_snd_mem K t).1
    · exact (edgeVertices_fst_mem K t).1
  have hvolK : volume (K : Set Point) =
      ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        volume (edgeTriangle K o t) := by
    have hcover : (K : Set Point) ⊆
        (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset, edgeTriangle K o t) ∪
          vertexRayUnion o V := by
      intro x hx
      by_cases hxline : x ∈ vertexRayUnion o V
      · exact Or.inr hxline
      obtain ⟨t, htproper, hxt⟩ :=
        exists_mem_edgeTriangle_of_notMem_vertexRayUnion K V hKV ho hx hxline
      exact Or.inl (Set.mem_biUnion ((hmemF t).2 htproper) hxt)
    have hle : volume (K : Set Point) ≤
        volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
          edgeTriangle K o t) := by
      calc volume (K : Set Point)
          ≤ volume ((⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
              edgeTriangle K o t) ∪ vertexRayUnion o V) := measure_mono hcover
        _ ≤ volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
              edgeTriangle K o t) + volume (vertexRayUnion o V) := measure_union_le _ _
        _ = volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
              edgeTriangle K o t) := by rw [volume_vertexRayUnion, add_zero]
    have hge : volume (⋃ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        edgeTriangle K o t) ≤ volume (K : Set Point) :=
      measure_mono (Set.iUnion₂_subset fun t _ ↦ hTsubK t)
    rw [le_antisymm hle hge]
    refine measure_biUnion_finset₀ ?_ ?_
    · intro s _ t _ hst
      exact volume_edgeTriangle_inter_eq_zero K ho hst
    · intro t _
      exact ((Set.toFinite ({o, (edgeVertices K t).2, (edgeVertices K t).1} :
        Set Point)).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet
  have hnonneg : ∀ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
      0 ≤ dist (edgeVertices K t).1 (edgeVertices K t).2 *
        (supportValue K t - inner ℝ o (normalVector t)) / 2 := by
    intro t htF
    linarith [hpos t htF]
  have harea : ClassicalResults.area (K : Set Point) =
      ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        dist (edgeVertices K t).1 (edgeVertices K t).2 *
          (supportValue K t - inner ℝ o (normalVector t)) / 2 := by
    simp only [ClassicalResults.area]
    rw [hvolK, Finset.sum_congr rfl hTvol, ← ENNReal.ofReal_sum_of_nonneg hnonneg,
      ENNReal.toReal_ofReal (Finset.sum_nonneg hnonneg)]
  have hsplit : ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
        dist (edgeVertices K t).1 (edgeVertices K t).2 *
          (supportValue K t - inner ℝ o (normalVector t)) / 2 =
      (1 / 2 : ℝ) * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
          dist (edgeVertices K t).1 (edgeVertices K t).2 * supportValue K t -
        (1 / 2 : ℝ) * ∑ t ∈ (finite_properEdgeNormal_angles K V hKV).toFinset,
          dist (edgeVertices K t).1 (edgeVertices K t).2 * inner ℝ o (normalVector t) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    ring
  rw [harea, hsplit, sum_edgeLength_mul_inner_normalVector_eq_zero K V hKV o, mul_zero,
    sub_zero, integral_supportValue_surfaceAreaMeasure_eq_sum_edgeLength K V hKV]

/-- The support-area identity for every finite convex hull. -/
theorem convexBody_area_support_integral_of_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ t, supportValue K t ∂surfaceAreaMeasure K := by
  by_cases hsub : (K : Set Point).Subsingleton
  · exact convexBody_area_support_integral_of_subsingleton K hsub
  by_cases hint : (interior (K : Set Point)).Nonempty
  · exact convexBody_area_support_integral_of_convexHull_interior K V hKV hint
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  exact convexBody_area_support_integral_of_segmentPresentation K d hd

/-! ### Symmetry of the mixed support integral

The mixed integral `∫ h_P dσ_Q` of two finite convex hulls is computed by lifting the circle to
`(0, 2π]` and indexing by the finite set `F` of lifts carrying a proper edge of `P` or of `Q`.
The positive-vertex increment formula turns `h_P` into a partial sum along `F`, so the integral
becomes a lower-triangular double sum `∑_{t ∈ F} ∑_{u ≤ t} α_u β_t sin (t - u)`, whose symmetry
in `(α, β)` is `Finset.sum_filter_le_add_sum_filter_le_swap` together with the vanishing of the
first trigonometric moments of the edge lengths. Polygon approximation transfers the identity to
arbitrary convex bodies. -/

/-- The first tangent coordinate at a real angle lift. -/
private theorem tangentVector_coe_zero (s : ℝ) :
    tangentVector ((s : ℝ) : Real.Angle) 0 = -Real.sin s := by
  simp [tangentVector, frame, Real.Angle.sin_coe]

/-- The second tangent coordinate at a real angle lift. -/
private theorem tangentVector_coe_one (s : ℝ) :
    tangentVector ((s : ℝ) : Real.Angle) 1 = Real.cos s := by
  simp [tangentVector, frame, Real.Angle.cos_coe]

/-- A finite set of angular lifts in `(0, 2π]` covering all proper-edge normals of a polygon.
Excluding `0` makes the lift of each angle unique, so no edge atom is counted twice. -/
private def IsProperEdgeLiftIndex (K : ConvexBody Point)
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) : Prop :=
  (∀ u ∈ F, 0 < (u : ℝ)) ∧
    ∀ u : Set.Icc (0 : ℝ) (2 * Real.pi), 0 < (u : ℝ) →
      (edgeVertices K ((u : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((u : ℝ) : Real.Angle)).2 → u ∈ F

/-- The surface integral over an initial angular arc is the finite sum of its edge atoms. -/
private theorem integral_surfaceAreaMeasure_image_Ioc_eq_sum_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) (hF : IsProperEdgeLiftIndex K F)
    (φ : Real.Angle → ℝ) (t : Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc 0 (t : ℝ),
        φ u ∂surfaceAreaMeasure K) =
      ∑ u ∈ F.filter (fun u ↦ u ≤ t),
        dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * φ ((u : ℝ) : Real.Angle) := by
  classical
  have hturn : 2 * Real.pi ≤ 0 + 2 * Real.pi := le_of_eq (by ring)
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  let a' : Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨0, le_rfl, hpi⟩
  have himg : (fun s : Set.Icc (0 : ℝ) (2 * Real.pi) ↦ ((s : ℝ) : Real.Angle)) ''
      Set.Ioc a' t = (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc 0 (t : ℝ) := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(s : ℝ), ⟨hs.1, hs.2⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1.le, hs.2.trans t.property.2⟩, ⟨hs.1, hs.2⟩, rfl⟩
  rw [← himg, integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts K V hKV hturn φ
    (Set.Ioc a' t) measurableSet_Ioc (fun u hu ↦ hu.1)]
  have hatom : ∀ u : Set.Icc (0 : ℝ) (2 * Real.pi),
      (surfaceAreaMeasure K).real {((u : ℝ) : Real.Angle)} =
        dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
          (edgeVertices K ((u : ℝ) : Real.Angle)).2 := by
    intro u
    change (surfaceAreaMeasure K {((u : ℝ) : Real.Angle)}).toReal = _
    rw [(surfaceAreaMeasure_atom_length K ((u : ℝ) : Real.Angle)).2.1,
      ENNReal.toReal_ofReal dist_nonneg]
  simp only [hatom]
  refine Finset.sum_subset ?_ ?_
  · intro u hu
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff] at hu
    exact Finset.mem_filter.2 ⟨hF.2 u hu.1.1 hu.1.2, hu.2.2⟩
  · intro u hu hnot
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, not_and] at hnot
    obtain ⟨huF, hut⟩ := Finset.mem_filter.1 hu
    have hu0 : 0 < (u : ℝ) := hF.1 u huF
    have hdeg : ¬((edgeVertices K ((u : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((u : ℝ) : Real.Angle)).2) := fun hne ↦
      (hnot ⟨hu0, hne⟩) ⟨hu0, hut⟩
    rw [not_not.mp hdeg, dist_self, zero_mul]

/-- The total surface integral is the finite sum of the edge atoms of a polygon. -/
private theorem integral_surfaceAreaMeasure_eq_sum_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) (hF : IsProperEdgeLiftIndex K F)
    (φ : Real.Angle → ℝ) :
    (∫ u, φ u ∂surfaceAreaMeasure K) =
      ∑ u ∈ F,
        dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * φ ((u : ℝ) : Real.Angle) := by
  classical
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  let b' : Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨2 * Real.pi, hpi, le_rfl⟩
  have hfull : (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc 0 ((b' : ℝ)) = Set.univ := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioc, Set.mem_univ, iff_true]
    let _ : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
    refine ⟨(AddCircle.equivIoc (2 * Real.pi) 0 u : ℝ), ?_, AddCircle.coe_equivIoc⟩
    simpa using (AddCircle.equivIoc (2 * Real.pi) 0 u).property
  have hfilter : F.filter (fun u ↦ u ≤ b') = F := by
    refine Finset.filter_true_of_mem fun u _ ↦ ?_
    exact u.property.2
  have := integral_surfaceAreaMeasure_image_Ioc_eq_sum_lifts K V hKV F hF φ b'
  rw [hfull, setIntegral_univ, hfilter] at this
  exact this

/-- The edge lengths of a polygon weight the cosines and sines of its normal directions to
zero. -/
private theorem sum_edgeLength_lift_cos_sin_eq_zero
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi))) (hF : IsProperEdgeLiftIndex K F) :
    (∑ u ∈ F, dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * Real.cos (u : ℝ) = 0) ∧
      ∑ u ∈ F, dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
            (edgeVertices K ((u : ℝ) : Real.Angle)).2 * Real.sin (u : ℝ) = 0 := by
  have hzero : ∀ i : Fin 2, ∑ u ∈ F,
      dist (edgeVertices K ((u : ℝ) : Real.Angle)).1
          (edgeVertices K ((u : ℝ) : Real.Angle)).2 *
        tangentVector ((u : ℝ) : Real.Angle) i = 0 := by
    intro i
    rw [← integral_surfaceAreaMeasure_eq_sum_lifts K V hKV F hF (fun v ↦ tangentVector v i)]
    exact integral_tangentCoordinate_surfaceAreaMeasure_eq_zero K i
  refine ⟨by simpa only [tangentVector_coe_one] using hzero 1, ?_⟩
  have h := hzero 0
  simp only [tangentVector_coe_zero, mul_neg, Finset.sum_neg_distrib] at h
  linarith

/-- The mixed support integral of two polygons, as a lower-triangular double sum over a common
index set of angular lifts. -/
private theorem integral_supportValue_eq_sum_sum_lifts
    (P Q : ConvexBody Point) (VP VQ : Finset Point)
    (hP : (P : Set Point) = convexHull ℝ (VP : Set Point))
    (hQ : (Q : Set Point) = convexHull ℝ (VQ : Set Point))
    (F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi)))
    (hidxP : IsProperEdgeLiftIndex P F) (hidxQ : IsProperEdgeLiftIndex Q F) :
    (∫ t, supportValue P t ∂surfaceAreaMeasure Q) =
      ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t),
        dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
              (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
            dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
              (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
          Real.sin ((t : ℝ) - (u : ℝ)) := by
  classical
  have hcosQ : ∑ u ∈ F, dist (edgeVertices Q ((u : ℝ) : Real.Angle)).1
      (edgeVertices Q ((u : ℝ) : Real.Angle)).2 * Real.cos (u : ℝ) = 0 :=
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).1
  have hsinQ : ∑ u ∈ F, dist (edgeVertices Q ((u : ℝ) : Real.Angle)).1
      (edgeVertices Q ((u : ℝ) : Real.Angle)).2 * Real.sin (u : ℝ) = 0 :=
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).2
  have hincP : ∀ (i : Fin 2) (t : Set.Icc (0 : ℝ) (2 * Real.pi)), 0 < (t : ℝ) →
      (edgeVertices P ((t : ℝ) : Real.Angle)).1 i =
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 i +
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              tangentVector ((u : ℝ) : Real.Angle) i := by
    intro i t ht
    have h1 := positiveVertex_sub_eq_integral_of_eq_convexHull P VP hP (a := 0)
      (b := (t : ℝ)) ht (by simpa using t.property.2) i
    rw [integral_surfaceAreaMeasure_image_Ioc_eq_sum_lifts P VP hP F hidxP
      (fun v ↦ tangentVector v i) t] at h1
    linarith
  have hsupp : ∀ t : Set.Icc (0 : ℝ) (2 * Real.pi), 0 < (t : ℝ) →
      supportValue P ((t : ℝ) : Real.Angle) =
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 * Real.cos (t : ℝ) +
            (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 * Real.sin (t : ℝ) +
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ)) := by
    intro t ht
    rw [← (edgeVertices_fst_mem P ((t : ℝ) : Real.Angle)).2, inner_normalVector_real,
      hincP 0 t ht, hincP 1 t ht]
    have hsplit :
        (∑ u ∈ F.filter (fun u ↦ u ≤ t),
              dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                tangentVector ((u : ℝ) : Real.Angle) 0) * Real.cos (t : ℝ) +
            (∑ u ∈ F.filter (fun u ↦ u ≤ t),
              dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                tangentVector ((u : ℝ) : Real.Angle) 1) * Real.sin (t : ℝ) =
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ)) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [tangentVector_coe_zero, tangentVector_coe_one, Real.sin_sub]
      ring
    linarith
  rw [integral_surfaceAreaMeasure_eq_sum_lifts Q VQ hQ F hidxQ (fun v ↦ supportValue P v)]
  have step1 : ∑ t ∈ F, dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
          (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * supportValue P ((t : ℝ) : Real.Angle) =
      ∑ t ∈ F, ((edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 *
            (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
              (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.cos (t : ℝ)) +
          (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 *
            (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
              (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.sin (t : ℝ)) +
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                  (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ))) := by
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have hms : dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
          (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
        (∑ u ∈ F.filter (fun u ↦ u ≤ t), dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
          (edgeVertices P ((u : ℝ) : Real.Angle)).2 * Real.sin ((t : ℝ) - (u : ℝ))) =
          ∑ u ∈ F.filter (fun u ↦ u ≤ t),
            dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                  (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
                dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                  (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
              Real.sin ((t : ℝ) - (u : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ ↦ by ring
    rw [hsupp t (hidxQ.1 t ht)]
    linear_combination hms
  have step2 : ∑ t ∈ F, ((edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 *
          (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.cos (t : ℝ)) +
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 *
          (dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.sin (t : ℝ)) +
        ∑ u ∈ F.filter (fun u ↦ u ≤ t),
          dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
            Real.sin ((t : ℝ) - (u : ℝ))) =
      (edgeVertices P ((0 : ℝ) : Real.Angle)).1 0 *
          (∑ t ∈ F, dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.cos (t : ℝ)) +
        (edgeVertices P ((0 : ℝ) : Real.Angle)).1 1 *
          (∑ t ∈ F, dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
            (edgeVertices Q ((t : ℝ) : Real.Angle)).2 * Real.sin (t : ℝ)) +
        ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t),
          dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
                (edgeVertices P ((u : ℝ) : Real.Angle)).2 *
              dist (edgeVertices Q ((t : ℝ) : Real.Angle)).1
                (edgeVertices Q ((t : ℝ) : Real.Angle)).2 *
            Real.sin ((t : ℝ) - (u : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [step1, step2, hcosQ, hsinQ]
  ring

/-- The lower-triangular sine double sum is symmetric under swapping the two weight families,
provided the second family has vanishing first trigonometric moments. -/
private theorem sum_filter_le_sin_sub_comm
    {ι : Type*} [LinearOrder ι] (F : Finset ι) (θ : ι → ℝ) (α β : ι → ℝ)
    (hβ0 : ∑ u ∈ F, β u * Real.cos (θ u) = 0)
    (hβ1 : ∑ u ∈ F, β u * Real.sin (θ u) = 0) :
    (∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), α u * β t * Real.sin (θ t - θ u)) =
      ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), β u * α t * Real.sin (θ t - θ u) := by
  set f : ι → ι → ℝ := fun x y ↦ α x * β y * Real.sin (θ y - θ x) with hf
  have hdiag : ∀ x, f x x = 0 := by
    intro x
    simp [hf]
  have hfull : (∑ x ∈ F, ∑ y ∈ F, f x y) = 0 := by
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    have hinner : (∑ y ∈ F, f x y) =
        (α x * Real.cos (θ x)) * (∑ y ∈ F, β y * Real.sin (θ y)) -
          (α x * Real.sin (θ x)) * (∑ y ∈ F, β y * Real.cos (θ y)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      simp only [hf, Real.sin_sub]
      ring
    rw [hinner, hβ0, hβ1]
    ring
  have htrans : (∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), f u t) +
      ∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), f t u = 0 := by
    rw [Finset.sum_filter_le_add_sum_filter_le_swap F f hdiag, hfull]
  have hright : (∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), β u * α t * Real.sin (θ t - θ u)) =
      -∑ t ∈ F, ∑ u ∈ F.filter (fun u ↦ u ≤ t), f t u := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [hf]
    rw [show θ u - θ t = -(θ t - θ u) by ring, Real.sin_neg]
    ring
  rw [hright]
  linarith [htrans]

/-- Symmetry of the mixed support integral for finite convex hulls, including the degenerate
point and segment cases. -/
theorem supportIntegral_symm_of_convexHull (P Q : ConvexBody Point) (VP VQ : Finset Point)
    (hP : (P : Set Point) = convexHull ℝ (VP : Set Point))
    (hQ : (Q : Set Point) = convexHull ℝ (VQ : Set Point)) :
    (∫ t, supportValue P t ∂surfaceAreaMeasure Q) =
      ∫ t, supportValue Q t ∂surfaceAreaMeasure P := by
  classical
  have hturn : 2 * Real.pi ≤ 0 + 2 * Real.pi := le_of_eq (by ring)
  have hSP := finite_properEdgeNormal_lifts P VP hP (a := 0) (b := 2 * Real.pi) hturn
  have hSQ := finite_properEdgeNormal_lifts Q VQ hQ (a := 0) (b := 2 * Real.pi) hturn
  set F : Finset (Set.Icc (0 : ℝ) (2 * Real.pi)) := hSP.toFinset ∪ hSQ.toFinset with hFdef
  have hidxP : IsProperEdgeLiftIndex P F := by
    refine ⟨fun u hu ↦ ?_, fun u h0 hne ↦ ?_⟩
    · rcases Finset.mem_union.mp hu with h | h
      · exact (hSP.mem_toFinset.mp h).1
      · exact (hSQ.mem_toFinset.mp h).1
    · exact Finset.mem_union_left _ (hSP.mem_toFinset.mpr ⟨h0, hne⟩)
  have hidxQ : IsProperEdgeLiftIndex Q F := by
    refine ⟨fun u hu ↦ ?_, fun u h0 hne ↦ ?_⟩
    · rcases Finset.mem_union.mp hu with h | h
      · exact (hSP.mem_toFinset.mp h).1
      · exact (hSQ.mem_toFinset.mp h).1
    · exact Finset.mem_union_right _ (hSQ.mem_toFinset.mpr ⟨h0, hne⟩)
  rw [integral_supportValue_eq_sum_sum_lifts P Q VP VQ hP hQ F hidxP hidxQ,
    integral_supportValue_eq_sum_sum_lifts Q P VQ VP hQ hP F hidxQ hidxP]
  exact sum_filter_le_sin_sub_comm F (fun u ↦ (u : ℝ))
    (fun u ↦ dist (edgeVertices P ((u : ℝ) : Real.Angle)).1
      (edgeVertices P ((u : ℝ) : Real.Angle)).2)
    (fun u ↦ dist (edgeVertices Q ((u : ℝ) : Real.Angle)).1
      (edgeVertices Q ((u : ℝ) : Real.Angle)).2)
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).1
    (sum_edgeLength_lift_cos_sin_eq_zero Q VQ hQ F hidxQ).2

/-- Symmetry of the mixed support integral for arbitrary planar convex bodies:
`∫ h_K dσ_L = ∫ h_L dσ_K`. -/
theorem supportIntegral_symm (K L : ConvexBody Point) :
    (∫ t, supportValue K t ∂surfaceAreaMeasure L) =
      ∫ t, supportValue L t ∂surfaceAreaMeasure K := by
  obtain ⟨VP, P, hPspec, hPdist⟩ := exists_facePreserving_polygonApproximation K ∅
  obtain ⟨VQ, Q, hQspec, hQdist⟩ := exists_facePreserving_polygonApproximation L ∅
  have hlimP : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hPdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hlimQ : Tendsto (fun n ↦ Metric.hausdorffDist (Q n : Set Point) (L : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hQdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_nhds_unique
    (tendsto_integral_supportValue_of_hausdorff_pair P Q K L hlimP hlimQ)
    (Filter.Tendsto.congr (fun n ↦ ?_)
      (tendsto_integral_supportValue_of_hausdorff_pair Q P L K hlimQ hlimP))
  exact supportIntegral_symm_of_convexHull (Q n) (P n) (VQ n) (VP n)
    (hQspec n).2.1 (hPspec n).2.1

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Linearity
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

theorem convexBody_maps_linear (t : I) (K L : ConvexBody Point) :
    (∀ a : Real.Angle,
      supportValue (convexBodyCombination t K L) a =
        (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a) ∧
    (∀ a : Real.Angle,
      (edgeVertices (convexBodyCombination t K L) a).1 =
        (1 - (t : ℝ)) • (edgeVertices K a).1 + (t : ℝ) • (edgeVertices L a).1 ∧
      (edgeVertices (convexBodyCombination t K L) a).2 =
        (1 - (t : ℝ)) • (edgeVertices K a).2 + (t : ℝ) • (edgeVertices L a).2) ∧
    (∀ a b : ℝ, a < b → b < a + Real.pi →
      supportingIntersection (convexBodyCombination t K L) a b =
        (1 - (t : ℝ)) • supportingIntersection K a b +
          (t : ℝ) • supportingIntersection L a b) ∧
    surfaceAreaMeasure (convexBodyCombination t K L) =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L := by
  refine ⟨supportValue_convexBodyCombination t K L, ?_, ?_,
    surfaceAreaMeasure_convexBodyCombination t K L⟩
  · exact edgeVertices_convexBodyCombination t K L
  · intro a b _hab _hba
    simp only [supportingIntersection, supportValue_convexBodyCombination]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

theorem convexBody_area_support_integral :
    (∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K a ∂surfaceAreaMeasure K) ∧
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦
        (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K a ∂surfaceAreaMeasure L) ∧
    IsQuadraticFunctional convexBodyCombination
      (fun K : ConvexBody Point ↦ ClassicalResults.area (K : Set Point)) :=
  convexBody_area_support_integral_of_area_identity
    (convexBody_area_support_integral_of_finiteHull
      (fun P W _hW hPW ↦ convexBody_area_support_integral_of_convexHull P W hPW))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The mixed area of two planar convex bodies

The mixed support integral `∫ h_K dσ_L` is symmetric in the two bodies, and the area of the
Minkowski segment `λ ↦ |(1 - λ) K + λ L|` is therefore the quadratic
`(1 - λ)² |K| + λ (1 - λ) ∫ h_L dσ_K + λ² |L|`, whose right derivative at `λ = 0` is
`∫ (h_L - h_K) dσ_K`.

The symmetry itself is `MovingSofa.supportIntegral_symm` in `MovingSofa.Convex.SupportArea`.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Symmetry of the mixed support integral, together with the right derivative at `0` of the
area along the Minkowski segment from `K` to `L`. -/
theorem supportMeasure_mixedArea_symmetry (K L : ConvexBody Point) :
    (∫ t : Real.Angle, supportValue K t ∂surfaceAreaMeasure L) =
      (∫ t : Real.Angle, supportValue L t ∂surfaceAreaMeasure K) ∧
    HasDerivWithinAt
      (segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L)
      (∫ t : Real.Angle, supportValue L t - supportValue K t ∂surfaceAreaMeasure K)
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  have hsymm := supportIntegral_symm K L
  refine ⟨hsymm, ?_⟩
  obtain ⟨harea, hbil, -⟩ := convexBody_area_support_integral
  have hcont (M : ConvexBody Point) : Continuous (supportValue M) :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hint : ∀ M N : ConvexBody Point, Integrable (supportValue M) (surfaceAreaMeasure N) := by
    intro M N
    let _ : IsFiniteMeasure (surfaceAreaMeasure N) := (surfaceAreaMeasure_face_union N).1
    exact (hcont M).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  rw [integral_sub (hint L K) (hint K K)]
  have hfun : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      segmentFunctional convexBodyCombination
          (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L lam =
        1 / 2 * (∫ t, supportValue K t ∂surfaceAreaMeasure K) +
          ((∫ t, supportValue L t ∂surfaceAreaMeasure K) -
            ∫ t, supportValue K t ∂surfaceAreaMeasure K) * lam +
          (1 / 2 * (∫ t, supportValue K t ∂surfaceAreaMeasure K) -
            (∫ t, supportValue L t ∂surfaceAreaMeasure K) +
            1 / 2 * ∫ t, supportValue L t ∂surfaceAreaMeasure L) * lam ^ 2 := by
    intro lam hlam
    have hseg : segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L lam =
        ClassicalResults.area
          ((convexBodyCombination ⟨lam, hlam⟩ K L : ConvexBody Point) : Set Point) :=
      dite_eq_left hlam
    have h2 := hbil.2 (convexBodyCombination ⟨lam, hlam⟩ K L) ⟨lam, hlam⟩ K L
    have h3 := hbil.1 K ⟨lam, hlam⟩ K L
    have h4 := hbil.1 L ⟨lam, hlam⟩ K L
    simp only [realCombination] at h2 h3 h4
    rw [hseg, harea (convexBodyCombination ⟨lam, hlam⟩ K L), h2, h3, h4, hsymm]
    ring
  have hpoly : ∀ A B C : ℝ, HasDerivAt (fun lam : ℝ ↦ A + B * lam + C * lam ^ 2) B 0 := by
    intro A B C
    have h : HasDerivAt (fun lam : ℝ ↦ A + B * lam + C * lam ^ 2)
        (0 + B * 1 + C * (2 * 0 ^ 1)) 0 :=
      HasDerivAt.add (HasDerivAt.add (hasDerivAt_const _ _)
        ((hasDerivAt_id _).const_mul _)) ((hasDerivAt_pow _ _).const_mul _)
    simpa using h
  exact HasDerivWithinAt.congr (hpoly _ _ _).hasDerivWithinAt hfun
    (hfun 0 ⟨le_rfl, zero_le_one⟩)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Tangent Line Path
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace MovingSofa

/-- Trace intersections with a fixed supporting line, ending at its exposed-edge endpoint. -/
@[expose]
def tangentLinePath (K : ConvexBody Point) (t : ℝ) (s : Set.Ioc (t - Real.pi) t) : Point :=
  if s.val < t then supportingIntersection K (s.val : Real.Angle) (t : Real.Angle)
  else (edgeVertices K (t : Real.Angle)).2

/-- Restrict the tangent-line path to a closed interval of supporting directions. -/
@[expose]
def tangentLineRestriction (K : ConvexBody Point) (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (s : Set.Icc a b) : Point :=
  tangentLinePath K t ⟨s.val, lt_of_lt_of_le ha.1 s.property.1,
    le_trans s.property.2 hb.2⟩

private def tangentLineCoordinate (K : ConvexBody Point) (t s : ℝ) : ℝ :=
  (supportValue K (s : Real.Angle) - supportValue K (t : Real.Angle) * Real.cos (s - t)) /
    Real.sin (s - t)

private theorem tangentLineCoordinate_le (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) {p : Point} (hp : p ∈ K) :
    tangentLineCoordinate K t s ≤ inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t)) := by
  have hsin : Real.sin (s - t) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])
  have hbound := inner_le_supportValue K hp (s : Real.Angle)
  have hn : normalVector (s : Real.Angle) =
      Real.cos (s - t) • normalVector (t : Real.Angle) +
        Real.sin (s - t) • tangentVector (t : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real t (s - t)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right] at hbound
  dsimp [tangentLineCoordinate]
  apply (div_le_iff_of_neg hsin).mpr
  have hc : (inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t))) * Real.sin (s - t) =
      inner ℝ p (tangentVector (t : Real.Angle)) * Real.sin (s - t) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        Real.cos (s - t) := by
    field_simp [hsin.ne]
  rw [hc]
  nlinarith

private theorem tangentLineCoordinate_eq_of_mem_support (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) {p : Point}
    (hp : inner ℝ p (normalVector (s : Real.Angle)) = supportValue K (s : Real.Angle)) :
    tangentLineCoordinate K t s = inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t)) := by
  have hsin : Real.sin (s - t) ≠ 0 :=
    (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])).ne
  have hn : normalVector (s : Real.Angle) =
      Real.cos (s - t) • normalVector (t : Real.Angle) +
        Real.sin (s - t) • tangentVector (t : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real t (s - t)
  dsimp [tangentLineCoordinate]
  rw [← hp, hn, inner_add_right, inner_smul_right, inner_smul_right]
  field_simp
  ring

private theorem monotoneOn_tangentLineCoordinate (K : ConvexBody Point) (t : ℝ) :
    MonotoneOn (tangentLineCoordinate K t) (Ioo (t - Real.pi) t) := by
  intro x hx y hy hxy
  obtain ⟨p, hp, hmax⟩ := exists_mem_inner_eq_supportValue K (y : Real.Angle)
  rw [tangentLineCoordinate_eq_of_mem_support K hy hmax]
  apply (tangentLineCoordinate_le K hx hp).trans
  apply add_le_add_right
  exact mul_le_mul_of_nonpos_left
    (Real.antitoneOn_cos_div_sin_Ioo_neg_pi_zero ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith))
    (sub_nonpos.mpr (inner_le_supportValue K hp (t : Real.Angle)))

private theorem supportingIntersection_eq_tangentLineCoordinate (K : ConvexBody Point)
    {t s : ℝ} (hs : s ∈ Ioo (t - Real.pi) t) :
    supportingIntersection K (s : Real.Angle) (t : Real.Angle) =
      supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
        tangentLineCoordinate K t s • tangentVector (t : Real.Angle) := by
  rw [supportingIntersection_comm K s t
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])).ne']
  simp only [supportingIntersection, tangentLineCoordinate, ← Real.Angle.coe_sub,
    Real.Angle.cos_coe, Real.Angle.sin_coe]

private theorem continuousAt_tangentLineCoordinate (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) : ContinuousAt (tangentLineCoordinate K t) s := by
  have hsin : Real.sin (s - t) ≠ 0 :=
    (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])).ne
  exact ((continuous_supportValue_real K).continuousAt.sub
    (continuousAt_const.mul (Real.continuous_cos.continuousAt.comp
      (continuousAt_id.sub continuousAt_const)))).div
    (Real.continuous_sin.continuousAt.comp (continuousAt_id.sub continuousAt_const)) hsin

private theorem tendsto_tangentLineCoordinate_left (K : ConvexBody Point) (t : ℝ) :
    Tendsto (tangentLineCoordinate K t) (𝓝[<] t)
      (𝓝 (inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)))) := by
  have h := (contact_oneSided_limits K t).2.2.2.2.2.inner
    (𝕜 := ℝ) (tendsto_const_nhds (x := tangentVector (t : Real.Angle)))
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : t - Real.pi < t)] with s hs
  rw [supportingIntersection_eq_tangentLineCoordinate K hs]
  simp only [inner_add_left, real_inner_smul_left, inner_normalVector_tangentVector,
    inner_tangentVector_self, mul_zero, mul_one, zero_add]

private def closedTangentLineCoordinate (K : ConvexBody Point) (t s : ℝ) : ℝ :=
  if s = t then inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle))
  else tangentLineCoordinate K t s

private theorem continuousOn_closedTangentLineCoordinate (K : ConvexBody Point) {t a : ℝ}
    (ha : a ∈ Ioo (t - Real.pi) t) :
    ContinuousOn (closedTangentLineCoordinate K t) (Icc a t) := by
  exact continuousOn_replace_right_endpoint ha.2 _ _
    (fun s hs ↦
      (continuousAt_tangentLineCoordinate K ⟨ha.1.trans_le hs.1, hs.2⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
    (fun s hs ↦
      (continuousAt_tangentLineCoordinate K ⟨ha.1.trans hs.1, hs.2⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
    (tendsto_tangentLineCoordinate_left K t)

private theorem monotoneOn_closedTangentLineCoordinate (K : ConvexBody Point) (t : ℝ) :
    MonotoneOn (closedTangentLineCoordinate K t) (Ioc (t - Real.pi) t) := by
  intro x hx y hy hxy
  by_cases hyEq : y = t
  · subst y
    by_cases hxEq : x = t
    · subst x
      rfl
    · have hxt : x < t := lt_of_le_of_ne hx.2 hxEq
      change (if x = t then _ else _) ≤ (if t = t then _ else _)
      simp only [ite_eq_right hxEq, ite_true]
      apply ge_of_tendsto (tendsto_tangentLineCoordinate_left K t)
      filter_upwards [Ioo_mem_nhdsLT hxt] with u hu
      exact monotoneOn_tangentLineCoordinate K t ⟨hx.1, hxt⟩
        ⟨hx.1.trans hu.1, hu.2⟩ hu.1.le
  · have hyt : y < t := lt_of_le_of_ne hy.2 hyEq
    have hxt : x < t := hxy.trans_lt hyt
    simp only [closedTangentLineCoordinate, ite_eq_right hxt.ne, ite_eq_right hyEq]
    exact monotoneOn_tangentLineCoordinate K t ⟨hx.1, hxt⟩ ⟨hy.1, hyt⟩ hxy

private theorem tangentLinePath_eq_coordinate (K : ConvexBody Point) (t : ℝ)
    (s : Ioc (t - Real.pi) t) :
    tangentLinePath K t s = supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
      closedTangentLineCoordinate K t s • tangentVector (t : Real.Angle) := by
  dsimp [tangentLinePath]
  split_ifs with hs
  · rw [supportingIntersection_eq_tangentLineCoordinate K ⟨s.property.1, hs⟩]
    simp only [closedTangentLineCoordinate, ite_eq_right hs.ne]
  · have heq : (s : ℝ) = t := le_antisymm s.property.2 (le_of_not_gt hs)
    simp only [closedTangentLineCoordinate, heq]
    have hp := (edgeVertices_snd_mem K (t : Real.Angle)).2
    change inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
      supportValue K (t : Real.Angle) at hp
    rw [← hp]
    exact (inner_normalVector_smul_add_inner_tangentVector_smul _ _).symm

/-- Every value of a tangent-line path lies on the supporting line at its own path parameter. -/
theorem tangentLinePath_mem_supportingLine (K : ConvexBody Point) (t : ℝ)
    (s : Set.Ioc (t - Real.pi) t) :
    tangentLinePath K t s ∈
      (supportingLineHalfPlane (K : Set Point) ((s : ℝ) : Real.Angle)).1 := by
  unfold tangentLinePath
  split_ifs with hs
  · exact supportingIntersection_inner_left K (s : ℝ) t
  · have hst : (s : ℝ) = t := le_antisymm s.property.2 (le_of_not_gt hs)
    rw [hst]
    exact (edgeVertices_snd_mem K (t : Real.Angle)).2

theorem tangentLinePath_segment_area (K : ConvexBody Point) (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a ≤ b) :
    ∃ γ : ContinuousBVPaths a b,
      γ.val = tangentLineRestriction K t a b ha hb ∧
      Set.range γ.val = segment ℝ (tangentLinePath K t ⟨a, ha⟩)
        (tangentLinePath K t ⟨b, hb⟩) ∧
      Set.range γ.val ⊆ (supportingLineHalfPlane (K : Set Point) (t : Real.Angle)).1 ∧
      curveAreaFunctional γ =
        segmentArea (tangentLinePath K t ⟨a, ha⟩) (tangentLinePath K t ⟨b, hb⟩) := by
  let Q : Set.Icc a b → ℝ := fun s ↦ closedTangentLineCoordinate K t s
  have hQmono : Monotone Q := by
    intro x y hxy
    exact monotoneOn_closedTangentLineCoordinate K t
      ⟨ha.1.trans_le x.property.1, x.property.2.trans hb.2⟩
      ⟨ha.1.trans_le y.property.1, y.property.2.trans hb.2⟩ hxy
  have hQcont : Continuous Q := by
    change Continuous (Set.domRestrict (Set.Icc a b) (closedTangentLineCoordinate K t))
    by_cases hat : a < t
    · exact continuousOn_iff_continuous_domRestrict.mp
        ((continuousOn_closedTangentLineCoordinate K ⟨ha.1, hat⟩).mono
          (Icc_subset_Icc_right hb.2))
    · have heq : a = b := le_antisymm hab (hb.2.trans (le_of_not_gt hat))
      have hc : ContinuousOn (closedTangentLineCoordinate K t) ({a} : Set ℝ) :=
        (show ({a} : Set ℝ).Subsingleton from Set.subsingleton_singleton).continuousOn _
      exact continuousOn_iff_continuous_domRestrict.mp (hc.mono (by simp [heq]))
  have hQbv : BoundedVariationOn Q Set.univ := by
    apply MonotoneOn.boundedVariationOn (f := Q) (s := Set.univ)
      (fun _ _ _ _ hxy ↦ hQmono hxy)
      (C := |Q ⟨a, le_rfl, hab⟩| + |Q ⟨b, hab, le_rfl⟩|)
    intro s _
    have hlo := hQmono (show (⟨a, le_rfl, hab⟩ : Set.Icc a b) ≤ s from s.property.1)
    have hhi := hQmono (show s ≤ (⟨b, hab, le_rfl⟩ : Set.Icc a b) from s.property.2)
    exact abs_le.mpr ⟨by
      linarith [neg_abs_le (Q ⟨a, le_rfl, hab⟩), abs_nonneg (Q ⟨b, hab, le_rfl⟩)], by
      linarith [le_abs_self (Q ⟨b, hab, le_rfl⟩), abs_nonneg (Q ⟨a, le_rfl, hab⟩)]⟩
  let h := supportValue K (t : Real.Angle)
  let γ : ContinuousBVPaths a b := {
    val := fun s ↦ h • normalVector (t : Real.Angle) + Q s • tangentVector (t : Real.Angle)
    property := ⟨continuous_const.add (hQcont.smul continuous_const), fun i ↦ by
      let C : NNReal := ⟨|tangentVector (t : Real.Angle) i|, abs_nonneg _⟩
      have hLip : LipschitzWith C (fun r : ℝ ↦
          h * normalVector (t : Real.Angle) i + r * tangentVector (t : Real.Angle) i) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simp only [Real.dist_eq]
        rw [show (h * normalVector (t : Real.Angle) i + x * tangentVector (t : Real.Angle) i) -
          (h * normalVector (t : Real.Angle) i + y * tangentVector (t : Real.Angle) i) =
            (x - y) * tangentVector (t : Real.Angle) i by ring, abs_mul, mul_comm]
        rfl
      have hcomp := hLip.comp_boundedVariationOn hQbv
      change BoundedVariationOn (fun t_1 ↦
        h * normalVector (t : Real.Angle) i + Q t_1 * tangentVector (t : Real.Angle) i) Set.univ
      exact hcomp⟩ }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · funext s
    unfold tangentLineRestriction
    exact (tangentLinePath_eq_coordinate K t
      ⟨s, lt_of_lt_of_le ha.1 s.property.1, s.property.2.trans hb.2⟩).symm
  · rw [show γ.val = fun s ↦ h • normalVector (t : Real.Angle) +
        Q s • tangentVector (t : Real.Angle) from rfl]
    let A := Q ⟨a, le_rfl, hab⟩
    let B := Q ⟨b, hab, le_rfl⟩
    have hAB : A ≤ B := hQmono hab
    have hQrange : Set.range Q = Set.Icc (Q ⟨a, le_rfl, hab⟩) (Q ⟨b, hab, le_rfl⟩) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨s, rfl⟩
        exact ⟨hQmono s.property.1, hQmono s.property.2⟩
      · intro y hy
        let _ : PreconnectedSpace (Set.Icc a b) :=
          Subtype.preconnectedSpace isPreconnected_Icc
        exact intermediate_value_univ ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩ hQcont hy
    have haeq := tangentLinePath_eq_coordinate K t ⟨a, ha⟩
    have hbeq := tangentLinePath_eq_coordinate K t ⟨b, hb⟩
    have hAa : closedTangentLineCoordinate K t a = A := rfl
    have hBb : closedTangentLineCoordinate K t b = B := rfl
    change Set.range (fun s ↦ h • normalVector (t : Real.Angle) +
      Q s • tangentVector (t : Real.Angle)) = _
    rw [haeq, hbeq]
    rw [hAa, hBb]
    rw [segment_eq_image_lineMap]
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      have hs : Q s ∈ Set.Icc A B := by
        exact ⟨hQmono s.property.1, hQmono s.property.2⟩
      by_cases hABeq : A = B
      · refine ⟨0, by simp, ?_⟩
        have : Q s = A := le_antisymm (hs.2.trans_eq hABeq.symm) hs.1
        ext i
        simp [h, hABeq, this]
      · let u := (Q s - A) / (B - A)
        have hpos : 0 < B - A := sub_pos.mpr (lt_of_le_of_ne hAB hABeq)
        refine ⟨u, ⟨div_nonneg (sub_nonneg.mpr hs.1) hpos.le,
          (div_le_one hpos).2 (by linarith [hs.2])⟩, ?_⟩
        ext i
        simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul]
        dsimp [u]
        field_simp [hpos.ne']
        ring
    · rintro ⟨u, hu, rfl⟩
      let r := A + u * (B - A)
      have hr : r ∈ Set.Icc A B := by
        dsimp [r]
        constructor
        · exact le_add_of_nonneg_right (mul_nonneg hu.1 (sub_nonneg.mpr hAB))
        · nlinarith [mul_le_mul_of_nonneg_right hu.2 (sub_nonneg.mpr hAB)]
      have hrange : r ∈ Set.range Q := by simpa [A, B, hQrange] using hr
      obtain ⟨s, hs⟩ := hrange
      refine ⟨s, ?_⟩
      ext i
      simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]
      rw [hs]
      ring
  · intro p hp
    obtain ⟨s, rfl⟩ := hp
    change inner ℝ (γ.val s) (normalVector (t : Real.Angle)) = supportValue K _
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, real_inner_comm, inner_normalVector_tangentVector]
    simp [h]
  · let Qbv : RightContinuousIntervalBV a b := {
      toFun := Q
      boundedVariation := hQbv
      right_continuous := fun s ↦ hQcont.continuousAt.continuousWithinAt }
    have hcoord (i : Fin 2) (s : Set.Icc a b) :
        (continuousBVCoordinate γ i).toFun s =
          h * normalVector (t : Real.Angle) i +
            tangentVector (t : Real.Angle) i * Qbv.toFun s := by
      change (h • normalVector (t : Real.Angle) + Q s • tangentVector (t : Real.Angle)) i = _
      simp [Qbv, mul_comm]
    unfold curveAreaFunctional
    change (intervalStieltjesIntegral (continuousBVCoordinate γ 1)
        (continuousBVCoordinate γ 0).toFun Set.univ -
      intervalStieltjesIntegral (continuousBVCoordinate γ 0)
        (continuousBVCoordinate γ 1).toFun Set.univ) / 2 = _
    rw [intervalStieltjesIntegral_affine_driver_cross hab Qbv
      (continuousBVCoordinate γ 0) (continuousBVCoordinate γ 1) hQcont
      (h * normalVector (t : Real.Angle) 0) (tangentVector (t : Real.Angle) 0)
      (h * normalVector (t : Real.Angle) 1) (tangentVector (t : Real.Angle) 1)
      (hcoord 0) (hcoord 1)]
    have haeq := tangentLinePath_eq_coordinate K t ⟨a, ha⟩
    have hbeq := tangentLinePath_eq_coordinate K t ⟨b, hb⟩
    rw [haeq, hbeq]
    simp only [Qbv]
    simp [segmentArea, planeCrossProduct, normalVector, tangentVector, frame, h]
    simp only [Q]
    ring

theorem tangentLinePath_convexLinear (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a ≤ b) :
    ∃ F : ConvexBody Point → ContinuousBVPaths a b,
      (∀ K, (F K).val = tangentLineRestriction K t a b ha hb) ∧
      IsConvexLinear convexBodyCombination
        (fun r x y ↦ (1 - (r : ℝ)) • x + (r : ℝ) • y) F := by
  let F : ConvexBody Point → ContinuousBVPaths a b := fun K ↦
    (tangentLinePath_segment_area K t a b ha hb hab).choose
  have hF (K : ConvexBody Point) :
      (F K).val = tangentLineRestriction K t a b ha hb :=
    (tangentLinePath_segment_area K t a b ha hb hab).choose_spec.1
  refine ⟨F, hF, ?_⟩
  intro r K L
  apply Subtype.ext
  funext s
  change (F (convexBodyCombination r K L)).val s =
    ((1 - (r : ℝ)) • (F K).val + (r : ℝ) • (F L).val) s
  rw [hF, hF, hF]
  unfold tangentLineRestriction tangentLinePath
  by_cases hs : (s : ℝ) < t
  · simp only [hs, ↓reduceIte, Pi.add_apply, Pi.smul_apply]
    exact (convexBody_maps_linear r K L).2.2.1 (s : ℝ) t hs
      (by linarith [ha.1, s.property.1])
  · have hst : (s : ℝ) = t := by
      apply le_antisymm
      · exact le_trans s.property.2 hb.2
      · exact le_of_not_gt hs
    simp only [hs, ↓reduceIte, Pi.add_apply, Pi.smul_apply]
    simpa [hst] using (convexBody_maps_linear r K L).2.1 (t : Real.Angle) |>.2

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Convex.ArcCutBoundary`.
* `Convex.ArcArea`.
* `Convex.ArcBilinear`.
* `Convex.ArcJordan`.
* `Convex.ArcRegionArea`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Cut Boundary
-/

public section

noncomputable section

namespace MovingSofa

open Set

private theorem normalVector_injective_cut : Function.Injective normalVector := by
  intro a b hab
  induction a using Real.Angle.induction_on with
  | _ a =>
    induction b using Real.Angle.induction_on with
    | _ b =>
      apply Real.Angle.cos_sin_inj
      · exact congrFun (congrArg WithLp.ofLp hab) 0
      · exact congrFun (congrArg WithLp.ofLp hab) 1

-- Duplicate of the current private UpperGraph helper; promote with the separation helper.
private theorem exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p v : Point} (hv : v ≠ 0) {a b : Real.Angle}
    (ha : IsExteriorNormal K p a) (hb : IsExteriorNormal K p b)
    (hva : inner ℝ v (normalVector a) = 0)
    (hvb : inner ℝ v (normalVector b) = 0) : a = b := by
  let orientation : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal orientation hv
      (norm_normalVector a) (norm_normalVector b) hva hvb with hab | hab
  · exact normalVector_injective_cut hab
  · exfalso
    obtain ⟨z, hz⟩ := hK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let q := z + (ε / 2) • normalVector a
    have hq : q ∈ K := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show q - z = (ε / 2) • normalVector a by simp [q], norm_smul,
        norm_normalVector, Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
      norm_num
      linarith))
    have haz := ha z (interior_subset hz)
    have hbz := hb z (interior_subset hz)
    have hba : normalVector b = -normalVector a := by rw [hab]; simp
    rw [hba, inner_neg_right] at hbz
    have heq : inner ℝ (z - p) (normalVector a) = 0 := by linarith
    have haq := ha q hq
    have hqp : q - p = (z - p) + (ε / 2) • normalVector a := by
      dsimp only [q]
      module
    rw [hqp, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
      norm_normalVector a, heq, zero_add] at haq
    have : ε / 2 ≤ 0 := by simpa using haq
    linarith

private theorem isExteriorNormal_of_mem_exposedEdge
    (K : ConvexBody Point) {p : Point} {a : Real.Angle}
    (hp : p ∈ exposedEdge K a) : IsExteriorNormal K p a := by
  intro q hq
  have hqle := inner_le_supportValue K hq a
  have hpEq := hp.2
  change inner ℝ p (normalVector a) = supportValue K a at hpEq
  rw [inner_sub_left, hpEq]
  linarith

/-- The frontier of a cut body is the retained convex boundary arc together with its chord. -/
theorem frontier_eq_convexBoundaryArc_union_segment_of_cut
    (K K' : ConvexBody Point) (a b t : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    frontier (K' : Set Point) = convexBoundaryArc K a b ∪ segment ℝ P Q := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u, hxu⟩ := exists_mem_exposedEdge_of_mem_frontier K' hInt hx
    let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let s := AddCircle.equivIoc (2 * Real.pi) (t - Real.pi) u
    have hs : (s : ℝ) ∈ Set.Ioc (t - Real.pi) (t + Real.pi) := by
      have := s.property
      convert this using 1
      ring_nf
    have hsu : (((s : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
    have hxs : x ∈ exposedEdge K' (s : ℝ) := by simpa [hsu] using hxu
    rcases le_or_gt (s : ℝ) a with hsa | has
    · left
      left
      left
      have hface := hleft (s : ℝ) ⟨hs.1, hsa⟩
      rw [hface] at hxs
      simpa [hP] using hxs
    · rcases lt_or_ge (s : ℝ) b with hsb | hbs
      · left
        left
        right
        refine Set.mem_iUnion_of_mem (s : ℝ) ?_
        refine Set.mem_iUnion_of_mem ⟨has, hsb⟩ ?_
        · rw [← hmiddle (s : ℝ) ⟨has, hsb⟩]
          exact hxs
      · rcases lt_or_eq_of_le hs.2 with hst | hst
        · left
          right
          have hface := hright (s : ℝ) ⟨hbs, hst⟩
          rw [hface] at hxs
          simpa [hQ] using hxs
        · right
          rw [hst] at hxs
          change x ∈ exposedEdge K'
            ((t : Real.Angle) + (Real.pi : Real.Angle)) at hxs
          rw [hterminal] at hxs
          simpa [segment_symm] using hxs
  · rintro x (hx | hx)
    · rcases hx with hx | hx
      · rcases hx with hx | hx
        · have hPa : P ∈ exposedEdge K' (a : ℝ) := by
            rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
            simp
          have hxP : x = P := by simpa [hP] using hx
          rw [hxP]
          exact exposedEdge_subset_frontier K'
            (a : Real.Angle) hPa
        · rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
          rcases Set.mem_iUnion.mp hx with ⟨hs, hx⟩
          rw [← hmiddle s hs] at hx
          exact exposedEdge_subset_frontier K' (s : Real.Angle) hx
      · have hQb : Q ∈ exposedEdge K' (b : ℝ) := by
          rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
          simp
        have hxQ : x = Q := by simpa [hQ] using hx
        rw [hxQ]
        exact exposedEdge_subset_frontier K'
          (b : Real.Angle) hQb
    · rw [segment_symm, ← hterminal] at hx
      exact exposedEdge_subset_frontier K'
        ((t + Real.pi : ℝ) : Real.Angle) hx

/-- A retained convex boundary arc meets its cutting chord only at the endpoints. -/
theorem convexBoundaryArc_inter_segment_eq_endpoints_of_cut
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    convexBoundaryArc K a b ∩ segment ℝ P Q = {P, Q} := by
  have hPa : P ∈ exposedEdge K' (a : ℝ) := by
    rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
    simp
  have hQb : Q ∈ exposedEdge K' (b : ℝ) := by
    rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
    simp
  have hPterm : P ∈ exposedEdge K' (t + Real.pi) := by
    rw [hterminal]
    exact right_mem_segment ℝ Q P
  have hQterm : Q ∈ exposedEdge K' (t + Real.pi) := by
    rw [hterminal]
    exact left_mem_segment ℝ Q P
  apply Set.Subset.antisymm
  · rintro x ⟨hxarc, hxseg⟩
    rcases hxarc with hxarc | hxQ
    · rcases hxarc with hxP | hxmid
      · left
        simpa [hP] using hxP
      · rcases Set.mem_iUnion.mp hxmid with ⟨s, hxmid⟩
        rcases Set.mem_iUnion.mp hxmid with ⟨hs, hxsK⟩
        have hxs : x ∈ exposedEdge K' (s : ℝ) := by
          rw [hmiddle s hs]
          exact hxsK
        rw [segment_eq_image] at hxseg
        obtain ⟨r, hr, hxr⟩ := hxseg
        by_cases hr0 : r = 0
        · left
          subst r
          simpa using hxr.symm
        by_cases hr1 : r = 1
        · right
          subst r
          simpa using hxr.symm
        have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
        have hrlt : r < 1 := lt_of_le_of_ne hr.2 hr1
        have hPK : P ∈ K' := hPa.1
        have hQK : Q ∈ K' := hQb.1
        have hPLe := inner_le_supportValue K' hPK (s : Real.Angle)
        have hQLe := inner_le_supportValue K' hQK (s : Real.Angle)
        have hxEq := hxs.2
        change inner ℝ x (normalVector (s : Real.Angle)) =
          supportValue K' (s : Real.Angle) at hxEq
        rw [← hxr, inner_add_left, inner_smul_left, inner_smul_left] at hxEq
        simp only [map_sub, map_one, RCLike.conj_to_real] at hxEq
        have hPEq : inner ℝ P (normalVector (s : Real.Angle)) =
            supportValue K' (s : Real.Angle) := by
          nlinarith
        have hQEq : inner ℝ Q (normalVector (s : Real.Angle)) =
            supportValue K' (s : Real.Angle) := by
          nlinarith
        have hPs : P ∈ exposedEdge K' (s : ℝ) := ⟨hPK, hPEq⟩
        have hQs : Q ∈ exposedEdge K' (s : ℝ) := ⟨hQK, hQEq⟩
        have hos : inner ℝ (Q - P) (normalVector (s : Real.Angle)) = 0 := by
          rw [inner_sub_left, hPEq, hQEq]
          ring
        have hot : inner ℝ (Q - P) (normalVector (t + Real.pi : Real.Angle)) = 0 := by
          change inner ℝ (Q - P)
            (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = 0
          rw [normalVector_add_pi, inner_neg_right, inner_sub_left, hPt, hQt]
          ring
        have hQP : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
        have hang : (s : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) :=
          exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut K' hInt hQP
            (isExteriorNormal_of_mem_exposedEdge K' hPs)
            (isExteriorNormal_of_mem_exposedEdge K' hPterm) hos hot
        have hnv := congrArg normalVector hang
        have hcos : Real.cos (s - (t + Real.pi)) = 1 := by
          rw [← inner_normalVector_normalVector s (t + Real.pi), hnv,
            inner_normalVector_self]
        have htupper : t < a + Real.pi := lt_trans htb hba
        have hlower : -(2 * Real.pi) < s - (t + Real.pi) := by
          nlinarith [hs.1, htupper]
        have hupper : s - (t + Real.pi) < 2 * Real.pi := by
          nlinarith [hs.2, hat, Real.pi_pos]
        have := (Real.cos_eq_one_iff_of_lt_of_lt hlower hupper).mp hcos
        have hbtpi : b < t + Real.pi := by nlinarith [hba, hat]
        linarith [hs.2, hbtpi]
    · right
      simpa [hQ] using hxQ
  · intro x hx
    rcases hx with hx | hx
    · subst x
      constructor
      · left
        left
        simp [hP]
      · exact left_mem_segment ℝ P Q
    · subst x
      constructor
      · right
        simp [hQ]
      · exact right_mem_segment ℝ P Q

/-- A convex body admits a counterclockwise BV frontier parametrization based off a fixed face. -/
theorem exists_closedBVJordan_frontier_base_not_mem_chord
    (K : ConvexBody Point) (t : ℝ) (P Q : Point)
    (hInt : (interior (K : Set Point)).Nonempty)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P) :
    ∃ (a b : ℝ) (x : ContinuousBVPaths a b),
      ∃ hab : a < b, IsOrientedJordanParametrization hab.le (frontier (K : Set Point))
        true x.val ∧ x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q := by
  obtain ⟨R, hRt⟩ := exposedEdge_nonempty K (t : Real.Angle)
  have hRnot : R ∉ segment ℝ P Q := by
    intro hRseg
    have hRopp : R ∈ exposedEdge K (t + Real.pi) := by
      rw [hterminal]
      simpa [segment_symm] using hRseg
    have hv : tangentVector (t : Real.Angle) ≠ 0 := by
      intro hzero
      have := inner_tangentVector_self t
      rw [hzero, inner_zero_left] at this
      norm_num at this
    have hot : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector t
    have hopp : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t + Real.pi : Real.Angle)) = 0 := by
      change inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = 0
      rw [normalVector_add_pi, inner_neg_right, hot, neg_zero]
    have hang : (t : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) :=
      exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut K hInt hv
        (isExteriorNormal_of_mem_exposedEdge K hRt)
        (isExteriorNormal_of_mem_exposedEdge K hRopp) hot hopp
    have hnv := congrArg normalVector hang
    change normalVector (t : Real.Angle) =
      normalVector (((t + Real.pi : ℝ) : Real.Angle)) at hnv
    rw [normalVector_add_pi] at hnv
    have hz : normalVector (t : Real.Angle) = 0 := by
      ext i
      have hi := congrFun (congrArg WithLp.ofLp hnv) i
      simp only [PiLp.neg_apply] at hi
      have : (normalVector (t : Real.Angle)) i = 0 := by linarith
      exact this
    have := norm_normalVector (t : Real.Angle)
    rw [hz, norm_zero] at this
    norm_num at this
  obtain ⟨o, ho⟩ := hInt
  obtain ⟨ρ, e, C, γ, hradial, he, hLip, hγ, hγJordan, hinterior⟩ :=
    convexBody_radial_boundary K o ho
  have hRrange : R ∈ Set.range γ.val := by
    rw [hγJordan.2.2.2.1]
    exact exposedEdge_subset_frontier K (t : Real.Angle) hRt
  obtain ⟨s, hstop, hsR⟩ := exists_param_lt_top_of_mem_range (by positivity) γ.val
    hγJordan.2.2.2.2.1 hRrange
  by_cases hs0 : (s : ℝ) = 0
  · refine ⟨0, 2 * Real.pi, γ, mul_pos (by norm_num) Real.pi_pos, hγJordan, ?_⟩
    have hs : s = ⟨0, le_rfl, (mul_pos (by norm_num) Real.pi_pos).le⟩ :=
      Subtype.ext hs0
    rw [← hsR, hs] at hRnot
    exact hRnot
  · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1 (Ne.symm hs0)
    obtain ⟨r, hrJordan, hr⟩ :=
      exists_oriented_cyclic_rotation_eq_concat (by positivity) γ hγJordan s hspos hstop
    refine ⟨0, 2, r, by norm_num, hrJordan, ?_⟩
    simpa [hr, Function.concatUnitIntervals, hsR] using hRnot

end MovingSofa

noncomputable section

namespace MovingSofa

/-- The nonterminal boundary of a convex cut body realizes the corresponding convex boundary arc. -/
theorem exists_rectifiableOrientedArc_convexBoundaryArc_of_cut
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = convexBoundaryArc K a b ∧
        A.val.startPoint = P ∧ A.val.endPoint = Q := by
  have hfrontier := frontier_eq_convexBoundaryArc_union_segment_of_cut
    K K' a b t P Q hat htb hba hP hQ hleft hmiddle hright hterminal hInt
  have hinter := convexBoundaryArc_inter_segment_eq_endpoints_of_cut
    K K' a b t c P Q hat htb hba hPQ hPt hQt hP hQ hleft hmiddle hright
      hterminal hInt
  obtain ⟨α, β, x, hαβ, hx, hbase⟩ :=
    exists_closedBVJordan_frontier_base_not_mem_chord K' t P Q hInt hterminal
  exact exists_rectifiableOrientedArc_of_closedJordan_cut hαβ hx P Q hPQ hbase
    hfrontier hinter

private theorem isExposed_exposedEdge_jordan (K : ConvexBody Point) (t : Real.Angle) :
    IsExposed ℝ (K : Set Point) (exposedEdge K t) :=
  isExposed_exposedEdge K t

/-- A singleton exposed face of a segment is one of its endpoints. -/
theorem endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    (K : ConvexBody Point) (x y P : Point) (s : Real.Angle)
    (hK : (K : Set Point) = segment ℝ x y)
    (hface : exposedEdge K s = {P}) : x = P ∨ y = P := by
  have hPextreme : P ∈ Set.extremePoints ℝ (K : Set Point) := by
    have hexposed : IsExposed ℝ (K : Set Point) {P} := by
      rw [← hface]
      exact isExposed_exposedEdge_jordan K s
    exact hexposed.isExtreme.mem_extremePoints
  rw [mem_extremePoints_iff_forall_segment] at hPextreme
  have hxK : x ∈ (K : Set Point) := by rw [hK]; exact left_mem_segment ℝ x y
  have hyK : y ∈ (K : Set Point) := by rw [hK]; exact right_mem_segment ℝ x y
  have hPseg : P ∈ segment ℝ x y := by rw [← hK]; exact hPextreme.1
  exact hPextreme.2 x hxK y hyK hPseg

/-- A cut body with empty interior has its selected boundary arc equal to the endpoint segment. -/
theorem convexBoundaryArc_eq_segment_of_cut_interior_empty
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hInt : interior (K' : Set Point) = ∅) :
    convexBoundaryArc K a b = segment ℝ P Q := by
  have hPmem : P ∈ (K' : Set Point) := by
    have ha : a ∈ Set.Ioc (t - Real.pi) a := ⟨by linarith, le_rfl⟩
    have : P ∈ exposedEdge K' (a : Real.Angle) := by rw [hleft a ha]; simp
    exact this.1
  have hQmem : Q ∈ (K' : Set Point) := by
    have hb : b ∈ Set.Ico b (t + Real.pi) := ⟨le_rfl, by linarith⟩
    have : Q ∈ exposedEdge K' (b : Real.Angle) := by rw [hright b hb]; simp
    exact this.1
  have hnsub : ¬(K' : Set Point).Subsingleton := by
    intro hs
    exact hPQ (hs hPmem hQmem)
  obtain ⟨x, y, hxy, hK'⟩ := K'.exists_eq_segment_of_interior_empty hnsub hInt
  have hxP : x = P ∨ y = P := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y P (a : Real.Angle) hK' (hleft a ⟨by linarith, le_rfl⟩)
  have hxQ : x = Q ∨ y = Q := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y Q (b : Real.Angle) hK' (hright b ⟨le_rfl, by linarith⟩)
  have hK'PQ : (K' : Set Point) = segment ℝ P Q := by
    rcases hxP with rfl | rfl <;> rcases hxQ with hxQ | hxQ
    · exact (hPQ hxQ).elim
    · simpa [hxQ] using hK'
    · simpa [hxQ, segment_symm ℝ] using hK'
    · exact (hPQ hxQ).elim
  have horth : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hQt, hPt, sub_self]
  let d : Point × Point × Real.Angle := (P, Q, (t : Real.Angle))
  have hd : IsSegmentPresentation K' d := ⟨hPQ, hK'PQ, horth⟩
  have hface : exposedEdge K (t : Real.Angle) = (K' : Set Point) := by
    rw [← hmiddle t ⟨hat, htb⟩]
    exact exposedEdge_eq_segment_of_orthogonal K' d hd (t : Real.Angle) horth
  apply Set.Subset.antisymm
  · rw [convexBoundaryArc]
    refine Set.union_subset (Set.union_subset (by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [hP]
      exact left_mem_segment ℝ _ _) ?_) (by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [hQ]
      exact right_mem_segment ℝ _ _)
    refine Set.iUnion₂_subset fun s hs z hz ↦ ?_
    rw [← hK'PQ]
    have hz' : z ∈ exposedEdge K' (s : Real.Angle) := by
      rw [hmiddle s hs]
      exact hz
    exact hz'.1
  · intro z hz
    have hzK' : z ∈ (K' : Set Point) := by rw [hK'PQ]; exact hz
    have hzface : z ∈ exposedEdge K (t : Real.Angle) := by rw [hface]; exact hzK'
    rw [convexBoundaryArc]
    apply Set.mem_union_left
    apply Set.mem_union_right
    apply Set.mem_iUnion.mpr
    refine ⟨t, Set.mem_iUnion.mpr ⟨⟨hat, htb⟩, hzface⟩⟩

end MovingSofa

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Area
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- An oriented rectifiable arc agrees with the prescribed convex boundary arc and its
endpoints. -/
def RealizesConvexArc (K : ConvexBody Point) (a b : ℝ)
    (Γ : RectifiableOrientedArc) : Prop :=
  Γ.val.carrier = convexBoundaryArc K a b ∧
    Γ.val.startPoint = (edgeVertices K (a : Real.Angle)).1 ∧
    Γ.val.endPoint = (edgeVertices K (b : Real.Angle)).2

/-- The signed area of a realization of the convex boundary arc, or zero if none exists. -/
def convexArcArea (K : ConvexBody Point) (a b : ℝ) : ℝ := by
  classical
  exact if h : ∃ Γ, RealizesConvexArc K a b Γ then jordanArcArea h.choose else 0

/-- Every realization of a convex boundary arc computes that arc's signed area. -/
theorem convexArcArea_eq_jordanArcArea_of_realizes {K : ConvexBody Point} {a b : ℝ}
    {Γ : RectifiableOrientedArc} (hΓ : RealizesConvexArc K a b Γ) :
    convexArcArea K a b = jordanArcArea Γ := by
  rw [convexArcArea, dite_eq_left ⟨Γ, hΓ⟩]
  let Δ := Classical.choose (show ∃ Γ, RealizesConvexArc K a b Γ from ⟨Γ, hΓ⟩)
  have hΔ : RealizesConvexArc K a b Δ :=
    Classical.choose_spec (show ∃ Γ, RealizesConvexArc K a b Γ from ⟨Γ, hΓ⟩)
  change curveAreaFunctional (Classical.choice Δ.property).path =
    curveAreaFunctional (Classical.choice Γ.property).path
  exact (curveArea_reparametrization.2.1 Δ Γ
    (Classical.choice Δ.property) (Classical.choice Γ.property)
    (hΔ.1.trans hΓ.1.symm)).1
      (hΔ.2.1.trans hΓ.2.1.symm) (hΔ.2.2.trans hΓ.2.2.symm)

/-- Any bounded-variation parametrization of a convex boundary arc computes that arc's signed
area. -/
theorem convexArcArea_eq_curveAreaFunctional_of_realizes {K : ConvexBody Point} {a b : ℝ}
    {Γ : OrientedJordanArc} (p : ArcBVParametrization Γ)
    (hΓ : RealizesConvexArc K a b ⟨Γ, ⟨p⟩⟩) :
    convexArcArea K a b = curveAreaFunctional p.path := by
  rw [convexArcArea_eq_jordanArcArea_of_realizes hΓ]
  exact (curveArea_arc_same_carrier Γ Γ
    (Classical.choice (⟨Γ, ⟨p⟩⟩ : RectifiableOrientedArc).property) p rfl).1 rfl rfl

/-- A continuous bounded-variation path on `[a, b]` that traces a convex boundary arc
injectively, from the arc's first vertex to its last, computes that arc's signed area. -/
theorem convexArcArea_eq_curveAreaFunctional_of_injOn {K : ConvexBody Point} {α β a b : ℝ}
    {f : ℝ → Point} (x : ContinuousBVPaths a b) (hab : a < b)
    (hx : ∀ t : Set.Icc a b, x.val t = f t) (hinj : Set.InjOn f (Set.Icc a b))
    (himage : f '' Set.Icc a b = convexBoundaryArc K α β)
    (hstart : f a = (edgeVertices K (α : Real.Angle)).1)
    (hend : f b = (edgeVertices K (β : Real.Angle)).2) :
    convexArcArea K α β = curveAreaFunctional x := by
  have hxinj : Function.Injective x.val := fun s t hst ↦
    Subtype.ext (hinj s.2 t.2 (by rw [← hx s, ← hx t, hst]))
  have hrange : Set.range x.val = convexBoundaryArc K α β := by
    rw [← himage, Set.image_eq_range]
    exact congrArg Set.range (funext hx)
  have hstart' : x.val ⟨a, le_rfl, hab.le⟩ = (edgeVertices K (α : Real.Angle)).1 := by
    rw [hx, hstart]
  have hend' : x.val ⟨b, hab.le, le_rfl⟩ = (edgeVertices K (β : Real.Angle)).2 := by
    rw [hx, hend]
  let Γ : OrientedJordanArc :=
    { carrier := convexBoundaryArc K α β
      startPoint := (edgeVertices K (α : Real.Angle)).1
      endPoint := (edgeVertices K (β : Real.Angle)).2
      parametrizable :=
        ⟨a, b, hab.le, x.val, x.property.1, hxinj, hrange, hstart', hend'⟩ }
  exact convexArcArea_eq_curveAreaFunctional_of_realizes (Γ := Γ)
    ⟨a, b, hab.le, x, hxinj, hrange, hstart', hend'⟩ ⟨rfl, rfl, rfl⟩

private theorem exists_degenerate_convexArc (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hcut := (convexBoundaryArc_cut K a b hab hba P P (supportingIntersection K a b)
    rfl heq rfl).1 rfl
  obtain ⟨Γ, hcarrier, hstart, hend, _⟩ := (segmentArea_jordan_and_frame P P).1
  have hreal : RealizesConvexArc K a b Γ := by
    refine ⟨hcarrier.trans (segment_same ℝ P) |>.trans hcut.2.symm,
      hstart, hend.trans heq⟩
  exact ⟨Γ, hreal, convexArcArea_eq_jordanArcArea_of_realizes hreal, fun _ ↦ by
    rw [hcarrier, segment_same, hstart]⟩

private theorem surfaceAreaMeasure_openArc_eq_zero_of_convexBoundaryArc_eq_singleton
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    {P : Point} (hArc : convexBoundaryArc K a b = {P}) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hmeas : MeasurableSet E := (Real.Angle.isOpen_image_Ioo a b).measurableSet
  have hsubset : E ⊆ (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc a b :=
    Set.image_mono Set.Ioo_subset_Icc_self
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 E hmeas
    (Or.inr ⟨a, b, hab.le, hba, hsubset⟩)]
  have hunion_sub : (⋃ t ∈ E, exposedEdge K t) ⊆ {P} := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨htE, hxt⟩ := ht
    obtain ⟨r, hr, rfl⟩ := htE
    have hxArc : x ∈ convexBoundaryArc K a b := by
      change x ∈ ({(edgeVertices K (a : Real.Angle)).1} ∪
        (⋃ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle))) ∪
        {(edgeVertices K (b : Real.Angle)).2}
      apply Set.mem_union_left
      apply Set.mem_union_right
      exact Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, hxt⟩⟩
    rw [hArc] at hxArc
    exact hxArc
  have hunion_nonempty : (⋃ t ∈ E, exposedEdge K t).Nonempty := by
    let r := (a + b) / 2
    have hr : r ∈ Set.Ioo a b := by dsimp [r]; constructor <;> linarith
    obtain ⟨x, hx⟩ := exposedEdge_nonempty K (r : Real.Angle)
    exact ⟨x, Set.mem_iUnion.2 ⟨(r : Real.Angle), Set.mem_iUnion.2
      ⟨⟨r, hr, rfl⟩, hx⟩⟩⟩
  have hunion : (⋃ t ∈ E, exposedEdge K t) = {P} :=
    Set.Nonempty.subset_singleton_iff hunion_nonempty |>.mp hunion_sub
  rw [hunion]
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point
    (by norm_num : (0 : ℝ) < 1)
  exact measure_singleton P

private theorem convexArcArea_eq_integral_of_endpoints_eq (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2) :
    convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2 := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hcut := (convexBoundaryArc_cut K a b hab hba P P (supportingIntersection K a b)
    rfl heq rfl).1 rfl
  obtain ⟨Γ, hcarrier, hstart, hend, hΓarea⟩ := (segmentArea_jordan_and_frame P P).1
  have hreal : RealizesConvexArc K a b Γ := by
    refine ⟨hcarrier.trans (segment_same ℝ P) |>.trans hcut.2.symm,
      hstart, hend.trans heq⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal, hΓarea]
  have hμ := surfaceAreaMeasure_openArc_eq_zero_of_convexBoundaryArc_eq_singleton
    K hab hba hcut.2
  rw [MeasureTheory.setIntegral_measure_zero _ hμ]
  simp [segmentArea, planeCrossProduct]
  ring

private theorem exists_pos_smul_tangentVector_of_cut
    (K : ConvexBody Point) {a t : ℝ} (hat : a < t) (hta : t < a + Real.pi)
    {P Q : Point} (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQK : Q ∈ K) (hne : P ≠ Q)
    (hnormal : inner ℝ P (normalVector (t : Real.Angle)) =
      inner ℝ Q (normalVector (t : Real.Angle))) :
    ∃ d : ℝ, 0 < d ∧ Q - P = d • tangentVector (t : Real.Angle) := by
  let d := inner ℝ (Q - P) (tangentVector (t : Real.Angle))
  have hnormal0 : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hnormal, sub_self]
  have hdecomp : Q - P = d • tangentVector (t : Real.Angle) := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - P) (t : Real.Angle), hnormal0, zero_smul, zero_add]
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a := by
    rw [hP]
    exact (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hQa : inner ℝ Q (normalVector (a : Real.Angle)) ≤ supportValue K a :=
    inner_le_supportValue K hQK (a : Real.Angle)
  have hinner : inner ℝ (Q - P) (normalVector (a : Real.Angle)) ≤ 0 := by
    rw [inner_sub_left, hPa]
    linarith
  have hsin : 0 < Real.sin (t - a) := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
  have htana : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (a : Real.Angle)) = -Real.sin (t - a) := by
    rw [real_inner_comm]
    have h := sin_sub_eq_neg_inner_normalVector_tangentVector
      (a : Real.Angle) (t : Real.Angle)
    have h' : (((t - a : ℝ) : Real.Angle)).sin =
        -inner ℝ (normalVector (a : Real.Angle)) (tangentVector (t : Real.Angle)) := by
      simpa only [Real.Angle.coe_sub] using h
    rw [Real.Angle.sin_coe] at h'
    linarith
  have hdnonneg : 0 ≤ d := by
    rw [hdecomp, real_inner_smul_left, htana] at hinner
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    apply hne
    have : Q - P = 0 := by rw [hdecomp, hd, zero_smul]
    exact (sub_eq_zero.mp this).symm
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdecomp⟩

/-- The half support integral against a surface measure is convex-bilinear in the pair of
bodies, by convex-linearity of support functions and surface measures. -/
theorem convexArcIntegral_bilinear (a b : ℝ) :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
        ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hcont (K : ConvexBody Point) : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint (K L : ConvexBody Point) :
      Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure L) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
    exact (hcont K).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  constructor
  · intro K t L M
    have hmeasure := (convexBody_maps_linear t L M).2.2.2
    change (1 / 2 : ℝ) * (∫ u in E, supportValue K u ∂surfaceAreaMeasure
        (convexBodyCombination t L M)) = _
    simp only [realCombination]
    rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      integral_add_measure ((hint K L).restrict.smul_measure ENNReal.ofReal_ne_top)
        ((hint K M).restrict.smul_measure ENNReal.ofReal_ne_top)]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal,
      sub_nonneg.mpr (show (t : ℝ) ≤ 1 from t.property.2), t.property.1]
    ring
  · intro L t K M
    change (1 / 2 : ℝ) * (∫ u in E, supportValue (convexBodyCombination t K M) u
      ∂surfaceAreaMeasure L) = _
    simp only [realCombination]
    have hfun : (fun u : Real.Angle ↦ supportValue (convexBodyCombination t K M) u) =
        fun u ↦ (1 - (t : ℝ)) * supportValue K u + (t : ℝ) * supportValue M u := by
      funext u
      exact (convexBody_maps_linear t K M).1 u
    rw [hfun, integral_add ((hint K L).restrict.const_mul _) ((hint M L).restrict.const_mul _),
      integral_const_mul, integral_const_mul]
    ring

private theorem convexArcArea_quadratic_of_integral_eq (a b : ℝ)
    (harea : ∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  let B := fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K t ∂surfaceAreaMeasure L
  refine ⟨B, convexArcIntegral_bilinear a b, ?_⟩
  intro K
  change convexArcArea K a b = B K K
  rw [harea K]
  simp only [B]
  ring

private theorem convexArc_area_of_realization_and_integral
    (a b : ℝ)
    (hgeom : ∀ K : ConvexBody Point,
      ∃ Γ : RectifiableOrientedArc,
        RealizesConvexArc K a b Γ ∧
        (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}))
    (harea : ∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) :
    (∀ K : ConvexBody Point, ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint})) ∧
    (∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) ∧
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  refine ⟨?_, harea, convexArcArea_quadratic_of_integral_eq a b harea⟩
  intro K
  obtain ⟨Γ, hreal, hsingleton⟩ := hgeom K
  exact ⟨Γ, hreal, convexArcArea_eq_jordanArcArea_of_realizes hreal, hsingleton⟩

private theorem exists_convexArc_realization (a b : ℝ) (hab : a < b)
    (hba : b < a + Real.pi) (K : ConvexBody Point) :
    ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}) := by
  by_cases heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2
  · obtain ⟨Γ, hreal, -, hsingleton⟩ := exists_degenerate_convexArc K a b hab hba heq
    exact ⟨Γ, hreal, hsingleton⟩
  · let P := (edgeVertices K (a : Real.Angle)).1
    let Q := (edgeVertices K (b : Real.Angle)).2
    let O := supportingIntersection K a b
    obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
    obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
      hright, hterminal⟩ := hcut heq
    by_cases hInt : (interior (K' : Set Point)).Nonempty
    · obtain ⟨Γ, hcarrier, hstart, hend⟩ :=
        exists_rectifiableOrientedArc_convexBoundaryArc_of_cut K K' a b t c P Q
          hat htb hba heq hPt hQt rfl rfl hleft hmiddle hright hterminal hInt
      have hreal : RealizesConvexArc K a b Γ := ⟨hcarrier, hstart, hend⟩
      refine ⟨Γ, hreal, ?_⟩
      intro hendpoints
      exact (heq (hstart.symm.trans (hendpoints.trans hend))) |>.elim
    · have hInt' : interior (K' : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hInt
      have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
        hat htb hba heq hPt hQt rfl rfl hleft hmiddle hright hInt'
      obtain ⟨Γ, hcarrier, hstart, hend, -⟩ := (segmentArea_jordan_and_frame P Q).1
      have hreal : RealizesConvexArc K a b Γ :=
        ⟨hcarrier.trans harc.symm, hstart, hend⟩
      refine ⟨Γ, hreal, ?_⟩
      intro hendpoints
      exact (heq (hstart.symm.trans (hendpoints.trans hend))) |>.elim

private theorem surfaceAreaMeasure_restrict_openArc_eq_of_exposedEdge_eq
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hfaces : ∀ s ∈ Set.Ioo a b,
      exposedEdge K (s : Real.Angle) = exposedEdge L (s : Real.Angle)) :
    (surfaceAreaMeasure K).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) =
      (surfaceAreaMeasure L).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  have hSE : MeasurableSet (S ∩ E) := hS.inter hE
  have hdomain : S ∩ E ⊆ (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc a b :=
    Set.inter_subset_right.trans (Set.image_mono Set.Ioo_subset_Icc_self)
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 (S ∩ E) hSE
      (Or.inr ⟨a, b, hab.le, hba, hdomain⟩),
    (surfaceAreaMeasure_face_union L).2.2.2.2 (S ∩ E) hSE
      (Or.inr ⟨a, b, hab.le, hba, hdomain⟩)]
  congr 2
  ext p
  simp only [Set.mem_iUnion, Set.mem_inter_iff, E]
  constructor
  · rintro ⟨⟨hpS, s, hs, hsp⟩, hx⟩
    subst p
    exact ⟨⟨hpS, ⟨s, hs, rfl⟩⟩, hfaces s hs ▸ hx⟩
  · rintro ⟨⟨hpS, s, hs, hsp⟩, hx⟩
    subst p
    exact ⟨⟨hpS, ⟨s, hs, rfl⟩⟩, hfaces s hs |>.symm ▸ hx⟩

private theorem surfaceAreaMeasure_compl_openArc_union_terminal_eq_zero_of_cut
    (K : ConvexBody Point) {a b t : ℝ} {P Q : Point}
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hInt : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K
      (((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b ∪
        {((t + Real.pi : ℝ) : Real.Angle)})ᶜ) = 0 := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t + Real.pi : ℝ)
  let D := (E ∪ {θ})ᶜ
  have hD : MeasurableSet D :=
    ((Real.Angle.isOpen_image_Ioo a b).measurableSet.union
      (measurableSet_singleton θ)).compl
  have hface := (surfaceAreaMeasure_face_union K).2.2.2.2 D hD (Or.inl hInt)
  have hunion : (⋃ u ∈ D, exposedEdge K u) ⊆ {P, Q} := by
    intro x hx
    obtain ⟨u, huD, hxu⟩ := Set.mem_iUnion₂.mp hx
    let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let s := AddCircle.equivIoc (2 * Real.pi) (t - Real.pi) u
    have hs : (s : ℝ) ∈ Set.Ioc (t - Real.pi) (t + Real.pi) := by
      have hs' := s.property
      convert hs' using 1
      ring_nf
    have hsu : (((s : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
    have hxs : x ∈ exposedEdge K (s : ℝ) := by simpa [hsu] using hxu
    rcases le_or_gt (s : ℝ) a with hsa | has
    · rw [hleft (s : ℝ) ⟨hs.1, hsa⟩] at hxs
      exact Or.inl (by simpa using hxs)
    · rcases lt_or_ge (s : ℝ) b with hsb | hbs
      · exfalso
        apply huD
        apply Set.mem_union_left
        exact ⟨s, ⟨has, hsb⟩, hsu⟩
      · rcases lt_or_eq_of_le hs.2 with hst | hst
        · rw [hright (s : ℝ) ⟨hbs, hst⟩] at hxs
          exact Or.inr (by simpa using hxs)
        · exfalso
          apply huD
          apply Set.mem_union_right
          simp only [Set.mem_singleton_iff, θ]
          rw [← hsu, hst]
  rw [show (((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b ∪
      {((t + Real.pi : ℝ) : Real.Angle)})ᶜ) = D by rfl, hface]
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact measure_mono_null hunion
    ((Set.toFinite {P, Q}).measure_zero (Measure.hausdorffMeasure 1))

private theorem integral_eq_openArc_add_terminal_of_cut
    (K : ConvexBody Point) {a b t : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hInt : (interior (K : Set Point)).Nonempty) :
    (∫ u, supportValue K u ∂surfaceAreaMeasure K) =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) +
      (surfaceAreaMeasure K).real {((t + Real.pi : ℝ) : Real.Angle)} *
        supportValue K ((t + Real.pi : ℝ) : Real.Angle) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t + Real.pi : ℝ)
  let C := E ∪ {θ}
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcont : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint : Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure K) :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hC : MeasurableSet C :=
    (Real.Angle.isOpen_image_Ioo a b).measurableSet.union (measurableSet_singleton θ)
  have hzero : surfaceAreaMeasure K Cᶜ = 0 := by
    exact surfaceAreaMeasure_compl_openArc_union_terminal_eq_zero_of_cut
      K hleft hright hInt
  have hdisj : Disjoint E {θ} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨s, hs, heq⟩
    have hlow : t - Real.pi < a := by linarith
    have hupp : b < t + Real.pi := by linarith
    have hsrange : s ∈ Set.Ioc (t - Real.pi) (t + Real.pi) :=
      ⟨hlow.trans hs.1, (hs.2.trans hupp).le⟩
    have htrange : t + Real.pi ∈ Set.Ioc (t - Real.pi) (t + Real.pi) :=
      ⟨by linarith [Real.pi_pos], le_rfl⟩
    have hinj := Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos]) hsrange htrange heq
    rw [hinj] at hs
    exact (not_lt_of_ge hupp.le hs.2)
  have hsplit := MeasureTheory.setIntegral_union hdisj (measurableSet_singleton θ)
    hint.integrableOn hint.integrableOn
  have hall := MeasureTheory.integral_add_compl hC hint
  rw [MeasureTheory.setIntegral_measure_zero _ hzero, add_zero] at hall
  rw [← hall, hsplit, MeasureTheory.integral_singleton]
  rfl

private theorem terminal_surface_term_eq_segmentArea_of_cut
    (K : ConvexBody Point) {t c d : ℝ} {P Q : Point}
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    (surfaceAreaMeasure K).real {((t + Real.pi : ℝ) : Real.Angle)} *
        supportValue K ((t + Real.pi : ℝ) : Real.Angle) / 2 =
      segmentArea Q P := by
  let θ : Real.Angle := (t + Real.pi : ℝ)
  have hterminal' : exposedEdge K θ = segment ℝ Q P := by
    simpa only [θ, Real.Angle.coe_add] using hterminal
  have hmass : (surfaceAreaMeasure K).real {θ} = d := by
    have htangent_norm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
      have hsq : ‖tangentVector (t : Real.Angle)‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, inner_tangentVector_self]
      nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
    rw [Measure.real, (surfaceAreaMeasure_atom_length K θ).1, hterminal',
      MeasureTheory.hausdorffMeasure_segment, edist_dist]
    simp only [dist_eq_norm, sub_eq_add_neg]
    rw [show Q + -P = Q - P by rfl, hdir, norm_smul, htangent_norm,
      mul_one, Real.norm_eq_abs, abs_of_pos hd]
    exact ENNReal.toReal_ofReal hd.le
  have hsupp : supportValue K θ = -c := by
    have hPterm : P ∈ exposedEdge K θ := by
      rw [hterminal']
      exact right_mem_segment ℝ Q P
    have h := hPterm.2
    change inner ℝ P (normalVector θ) = supportValue K θ at h
    change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = _ at h
    rw [normalVector_add_pi, inner_neg_right, hPt] at h
    linarith
  have hQline : Q ∈ normalLine θ (-c) := by
    change inner ℝ Q (normalVector θ) = -c
    change inner ℝ Q (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hQt]
  have hPline : P ∈ normalLine θ (-c) := by
    change inner ℝ P (normalVector θ) = -c
    change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hPt]
  have hdir' : P - Q = d • tangentVector θ := by
    have htangent : tangentVector θ = -tangentVector (t : Real.Angle) := by
      ext i
      fin_cases i <;> simp [θ, tangentVector, frame]
    calc
      P - Q = -(Q - P) := by module
      _ = -(d • tangentVector (t : Real.Angle)) := congrArg Neg.neg hdir
      _ = d • tangentVector θ := by rw [htangent]; module
  rw [hmass, hsupp]
  rw [mul_comm]
  exact ((segmentArea_jordan_and_frame Q P).2 θ (-c) d hQline hPline hdir').symm

private theorem supportValue_eq_of_exposedEdge_eq (K L : ConvexBody Point)
    (t : Real.Angle) (hface : exposedEdge K t = exposedEdge L t) :
    supportValue K t = supportValue L t := by
  obtain ⟨p, hp⟩ := exposedEdge_nonempty K t
  have hp' : p ∈ exposedEdge L t := hface ▸ hp
  exact hp.2.symm.trans hp'.2

private theorem integral_openArc_eq_of_exposedEdge_eq
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hfaces : ∀ s ∈ Set.Ioo a b,
      exposedEdge K (s : Real.Angle) = exposedEdge L (s : Real.Angle)) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue L t ∂surfaceAreaMeasure L := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hμ := surfaceAreaMeasure_restrict_openArc_eq_of_exposedEdge_eq
    K L hab hba hfaces
  change (∫ t, supportValue K t ∂(surfaceAreaMeasure K).restrict E) =
    ∫ t, supportValue L t ∂(surfaceAreaMeasure L).restrict E
  rw [hμ]
  apply MeasureTheory.integral_congr_ae
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  filter_upwards [ae_restrict_mem hE] with t ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact supportValue_eq_of_exposedEdge_eq K L _ (hfaces s hs)

private theorem jordanArcArea_eq_integral_of_cut_interior_nonempty
    (K : ConvexBody Point) {a b t c d α β : ℝ} {P Q : Point}
    {x : ContinuousBVPaths α β} {A : RectifiableOrientedArc}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K : Set Point)) true x.val)
    (hAarea : curveAreaFunctional x = jordanArcArea A + segmentArea Q P)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K : Set Point)).Nonempty)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    jordanArcArea A =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hxarea := curveArea_eq_jordanInterior_area α β hαβ.le
    (frontier (K : Set Point)) x hx
  rw [jordanInterior_frontier_eq_interior K.convex K.isCompact.isClosed
    K.isCompact.isBounded K.nonempty] at hxarea
  have hinterarea : ClassicalResults.area (interior (K : Set Point)) =
      ClassicalResults.area (K : Set Point) := by
    simp only [ClassicalResults.area]
    rw [measure_interior_of_null_frontier (K.convex.addHaar_frontier volume)]
  rw [hinterarea, (convexBody_area_support_integral.1 K)] at hxarea
  have hsplit := integral_eq_openArc_add_terminal_of_cut K hat htb hba hleft hright hInt
  have hterminalArea := terminal_surface_term_eq_segmentArea_of_cut K hPt hQt hterminal
    hd hdir
  rw [hAarea, hsplit] at hxarea
  linarith

private theorem convexArcArea_eq_integral_of_cut_interior_nonempty
    (K K' : ConvexBody Point) {a b t c d α β : ℝ} {P Q : Point}
    {x : ContinuousBVPaths α β} {A : RectifiableOrientedArc}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K' : Set Point)) true x.val)
    (hAcarrier : A.val.carrier = convexBoundaryArc K a b)
    (hAstart : A.val.startPoint = P) (hAend : A.val.endPoint = Q)
    (hAarea : curveAreaFunctional x = jordanArcArea A + segmentArea Q P)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hreal : RealizesConvexArc K a b A := ⟨hAcarrier, hAstart.trans hP, hAend.trans hQ⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal]
  rw [jordanArcArea_eq_integral_of_cut_interior_nonempty K' hαβ hx hAarea
    hat htb hba hPt hQt hleft hright hterminal hInt hd hdir]
  exact congrArg (fun z : ℝ ↦ z / 2)
    (integral_openArc_eq_of_exposedEdge_eq K' K (hat.trans htb) hba hmiddle)

private theorem integral_openArc_eq_segmentArea_of_segment
    (K : ConvexBody Point) {a b t c d : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hK : (K : Set Point) = segment ℝ P Q) (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K u ∂surfaceAreaMeasure K) / 2 = segmentArea P Q := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t : ℝ)
  have horth : inner ℝ (Q - P) (normalVector θ) = 0 := by
    change inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0
    rw [inner_sub_left, hQt, hPt, sub_self]
  have hpres : IsSegmentPresentation K (P, Q, θ) := ⟨hPQ, hK, horth⟩
  have htangent_norm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    have hsq : ‖tangentVector (t : Real.Angle)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_tangentVector_self]
    nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
  have hdist : dist P Q = d := by
    rw [dist_eq_norm, show P - Q = -(Q - P) by module, norm_neg, hdir,
      norm_smul, htangent_norm, mul_one, Real.norm_eq_abs, abs_of_pos hd]
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  have htE : θ ∈ E := ⟨t, ⟨hat, htb⟩, rfl⟩
  have hopp : θ + (Real.pi : Real.Angle) ∉ E := by
    rintro ⟨s, hs, heq⟩
    have hsupper : s ≤ a + 2 * Real.pi := by
      have : s < a + Real.pi := hs.2.trans hba
      linarith [Real.pi_pos]
    have htupper : t + Real.pi ≤ a + 2 * Real.pi := by
      linarith [htb, hba, Real.pi_pos]
    have hsrange : s ∈ Set.Ioc a (a + 2 * Real.pi) := ⟨hs.1, hsupper⟩
    have htrange : t + Real.pi ∈ Set.Ioc a (a + 2 * Real.pi) :=
      ⟨by linarith [hat, Real.pi_pos], htupper⟩
    have hinj := Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos])
      hsrange htrange
    have hst : s = t + Real.pi := hinj (by
      change (s : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle)
      simpa only [θ, Real.Angle.coe_add] using heq)
    linarith [hs.2, hba]
  have hmeasure : (surfaceAreaMeasure K).restrict E =
      ENNReal.ofReal d • Measure.dirac θ := by
    classical
    rw [surfaceAreaMeasure_eq_segmentPresentation K (P, Q, θ) hpres, hdist,
      Measure.restrict_smul, Measure.restrict_add]
    simp [restrict_dirac, htE, hopp]
  change (∫ u, supportValue K u ∂(surfaceAreaMeasure K).restrict E) / 2 = _
  rw [hmeasure, MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
    ENNReal.toReal_ofReal hd.le]
  have hPline : P ∈ normalLine θ c := hPt
  have hQline : Q ∈ normalLine θ c := hQt
  have hsupp : supportValue K θ = c := by
    have hpK : P ∈ K := by
      change P ∈ (K : Set Point)
      rw [hK]
      exact left_mem_segment ℝ P Q
    have hp : P ∈ exposedEdge K θ := by
      rw [exposedEdge_eq_segment_of_orthogonal K (P, Q, θ) hpres θ horth]
      exact hpK
    have hpEq := hp.2
    change inner ℝ P (normalVector θ) = supportValue K θ at hpEq
    exact hpEq.symm.trans hPt
  rw [hsupp]
  simp only [smul_eq_mul]
  convert ((segmentArea_jordan_and_frame P Q).2 θ c d hPline hQline hdir).symm using 1
  ring

private theorem convexArcArea_eq_integral_of_cut_interior_empty
    (K K' : ConvexBody Point) {a b t c d : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hInt : interior (K' : Set Point) = ∅)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hPmem : P ∈ (K' : Set Point) := by
    have : P ∈ exposedEdge K' (a : Real.Angle) := by
      rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
      simp
    exact this.1
  have hQmem : Q ∈ (K' : Set Point) := by
    have : Q ∈ exposedEdge K' (b : Real.Angle) := by
      rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
      simp
    exact this.1
  have hnsub : ¬(K' : Set Point).Subsingleton := by
    intro hs
    exact hPQ (hs hPmem hQmem)
  obtain ⟨x, y, hxy, hK'⟩ := K'.exists_eq_segment_of_interior_empty hnsub hInt
  have hxP : x = P ∨ y = P := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y P (a : Real.Angle) hK' (hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩)
  have hxQ : x = Q ∨ y = Q := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y Q (b : Real.Angle) hK' (hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  have hK'PQ : (K' : Set Point) = segment ℝ P Q := by
    rcases hxP with rfl | rfl <;> rcases hxQ with hxQ | hxQ
    · exact (hPQ hxQ).elim
    · simpa [hxQ] using hK'
    · simpa [hxQ, segment_symm ℝ] using hK'
    · exact (hPQ hxQ).elim
  have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
    hat htb hba hPQ hPt hQt hP hQ hleft hmiddle hright hInt
  obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
    (segmentArea_jordan_and_frame P Q).1
  have hreal : RealizesConvexArc K a b A :=
    ⟨hAcarrier.trans harc.symm, hAstart.trans hP, hAend.trans hQ⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal]
  rw [hAarea]
  rw [← integral_openArc_eq_segmentArea_of_segment K' hat htb hba hK'PQ hPQ
    hPt hQt hd hdir]
  exact congrArg (fun z : ℝ ↦ z / 2)
    (integral_openArc_eq_of_exposedEdge_eq K' K (hat.trans htb) hba hmiddle)

private theorem convexArcArea_eq_integral_of_endpoints_ne
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
  obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
    hright, hterminal⟩ := hcut hne
  have hnormal : inner ℝ P (normalVector (t : Real.Angle)) =
      inner ℝ Q (normalVector (t : Real.Angle)) := hPt.trans hQt.symm
  obtain ⟨d, hd, hdir⟩ := exists_pos_smul_tangentVector_of_cut K hat
    (htb.trans hba) rfl (edgeVertices_snd_mem K (b : Real.Angle)).1 hne hnormal
  by_cases hInt : (interior (K' : Set Point)).Nonempty
  · have hfrontier := frontier_eq_convexBoundaryArc_union_segment_of_cut
      K K' a b t P Q hat htb hba rfl rfl hleft hmiddle hright hterminal hInt
    have hinter := convexBoundaryArc_inter_segment_eq_endpoints_of_cut
      K K' a b t c P Q hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright
        hterminal hInt
    obtain ⟨α, β, x, hαβ, hx, hbase⟩ :=
      exists_closedBVJordan_frontier_base_not_mem_chord K' t P Q hInt hterminal
    obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
      exists_rectifiableOrientedArc_of_cut_with_area K' hαβ hx hne hbase
        hfrontier hinter hPt hQt hterminal hd hdir
    exact convexArcArea_eq_integral_of_cut_interior_nonempty K K' hαβ hx
      hAcarrier hAstart hAend hAarea rfl rfl hat htb hba hPt hQt hmiddle hleft hright
        hterminal hInt hd hdir
  · exact convexArcArea_eq_integral_of_cut_interior_empty K K' hat htb hba hne
      hPt hQt rfl rfl hleft hmiddle hright (Set.not_nonempty_iff_eq_empty.mp hInt)
      hd hdir

theorem convexArc_area (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    (∀ K : ConvexBody Point, ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint})) ∧
    (∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) ∧
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  apply convexArc_area_of_realization_and_integral a b
    (exists_convexArc_realization a b hab hba)
  intro K
  by_cases heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2
  · exact convexArcArea_eq_integral_of_endpoints_eq K hab hba heq
  · exact convexArcArea_eq_integral_of_endpoints_ne K hab hba heq

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Bilinear
-/

public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- Half the coordinate cross Stieltjes integral over the open parameter interval. -/
def openIntervalCrossIntegral {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (g : Set.Icc a b → Point) : ℝ :=
  (intervalStieltjesIntegral (f 1) (fun t ↦ g t 0) {t | a < (t : ℝ) ∧ (t : ℝ) < b} -
    intervalStieltjesIntegral (f 0) (fun t ↦ g t 1) {t | a < (t : ℝ) ∧ (t : ℝ) < b}) / 2

/-- The half-support integral is the vertex cross Stieltjes integral, for any bounded
measurable selection from the first body's exposed edges. -/
private theorem halfSupportIntegral_eq_openIntervalCrossIntegral
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (F : Fin 2 → RightContinuousIntervalBV a b)
    (hF : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (F i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure L)
    (W : Real.Angle → Point) (C : ℝ)
    (hWm : ∀ i : Fin 2, Measurable fun t : Ioc a b ↦ W (((t : ℝ) : Real.Angle)) i)
    (hWb : ∀ (u : Real.Angle) (i : Fin 2), ‖W u i‖ ≤ C)
    (hWsupp : ∀ u : Real.Angle, planeCrossProduct (W u) (tangentVector u) = supportValue K u) :
    ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K t ∂surfaceAreaMeasure L) =
      openIntervalCrossIntegral F (fun t ↦ W (((t : ℝ) : Real.Angle))) := by
  have hWcoord : ∀ u : Real.Angle,
      W u 0 * tangentVector u 1 - W u 1 * tangentVector u 0 = supportValue K u := hWsupp
  have hE : MeasurableSet {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} :=
    measurableSet_Ioo.preimage measurable_subtype_coe
  have hEa : ∀ t ∈ {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b}, a < (t : ℝ) :=
    fun _ ht ↦ ht.1
  have himg : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1.le, hs.2.le⟩, hs, rfl⟩
  have hsub : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} ⊆
      Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
    rintro u ⟨t, ht, rfl⟩
    exact ⟨⟨(t : ℝ), ht.1, ht.2.le⟩, rfl⟩
  have hSmeas : MeasurableSet ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b}) := by
    rw [himg]
    exact (Real.Angle.isOpen_image_Ioo a b).measurableSet
  have h1 := intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable L hab hturn F hF
    1 (fun u ↦ W u 0) C (hWm 0) (fun u ↦ hWb u 0) _ hE hEa
  have h0 := intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable L hab hturn F hF
    0 (fun u ↦ W u 1) C (hWm 1) (fun u ↦ hWb u 1) _ hE hEa
  have hi1 := integrableOn_mul_tangentVector_of_bounded L hturn 1 (fun u ↦ W u 0) C (hWm 0)
    (fun u ↦ hWb u 0) _ hSmeas hsub
  have hi0 := integrableOn_mul_tangentVector_of_bounded L hturn 0 (fun u ↦ W u 1) C (hWm 1)
    (fun u ↦ hWb u 1) _ hSmeas hsub
  rw [openIntervalCrossIntegral, h1, h0, ← integral_sub hi1 hi0,
    setIntegral_congr_fun hSmeas (fun u _ ↦ hWcoord u), himg]
  ring

theorem convexArc_bilinear_computation (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
        ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) ∧
    ∃ F : ConvexBody Point → Fin 2 → RightContinuousIntervalBV a b,
      (∀ K i t, (F K i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      (∀ K L : ConvexBody Point,
        ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) =
          openIntervalCrossIntegral (F L) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) ∧
        ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) =
          openIntervalCrossIntegral (F L) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2)) ∧
      (∀ K : ConvexBody Point, convexArcArea K a b =
        openIntervalCrossIntegral (F K) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1)) := by
  have hturn : b ≤ a + 2 * Real.pi := by linarith [Real.pi_pos]
  refine ⟨convexArcIntegral_bilinear a b, ?_⟩
  choose F hFtoFun hFmeasure using fun L : ConvexBody Point ↦
    positiveVertex_stieltjes_surface L a b hab hturn
  have hcross1 (K L : ConvexBody Point) :
      ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure L) =
        openIntervalCrossIntegral (F L)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point)
    refine halfSupportIntegral_eq_openIntervalCrossIntegral K L hab hturn (F L) (hFmeasure L)
      (fun u ↦ (edgeVertices K u).1) R
      (fun i ↦ measurable_positiveVertex_coordinate_Ioc K hab.le i)
      (fun u i ↦ ?_) (fun u ↦ ?_)
    · have hmem := hR (edgeVertices_fst_mem K u).1
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (by simpa [Real.norm_eq_abs] using Point.abs_apply_le_norm _ i) hmem
    · rw [planeCrossProduct_tangentVector, (edgeVertices_fst_mem K u).2]
  have hcross2 (K L : ConvexBody Point) :
      ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure L) =
        openIntervalCrossIntegral (F L)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point)
    refine halfSupportIntegral_eq_openIntervalCrossIntegral K L hab hturn (F L) (hFmeasure L)
      (fun u ↦ (edgeVertices K u).2) R
      (fun i ↦ measurable_negativeVertex_coordinate K hab.le i) (fun u i ↦ ?_) (fun u ↦ ?_)
    · have hmem := hR (edgeVertices_snd_mem K u).1
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (by simpa [Real.norm_eq_abs] using Point.abs_apply_le_norm _ i) hmem
    · rw [planeCrossProduct_tangentVector, (edgeVertices_snd_mem K u).2]
  refine ⟨F, hFtoFun, fun K L ↦ ⟨hcross1 K L, hcross2 K L⟩, fun K ↦ ?_⟩
  have harea := (convexArc_area a b hab hba).2.1 K
  have hK := hcross1 K K
  rw [harea]
  linarith

/-- Antisymmetry of the vertex cross Stieltjes integral over the open interval, up to the two
endpoint corrections: the negative vertices at `b` and the positive vertices at `a`. -/
theorem openIntervalCrossIntegral_antisymm {a b : ℝ} (hab : a < b)
    (K L : ConvexBody Point) (FK FL : Fin 2 → RightContinuousIntervalBV a b)
    (hFK : ∀ i t, (FK i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (hFL : ∀ i t, (FL i).toFun t =
      (edgeVertices L (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i) :
    openIntervalCrossIntegral FL (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) -
        openIntervalCrossIntegral FK (fun t ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1) =
      segmentArea (edgeVertices K (b : Real.Angle)).2 (edgeVertices L (b : Real.Angle)).2 -
        segmentArea (edgeVertices K (a : Real.Angle)).1 (edgeVertices L (a : Real.Angle)).1 := by
  have key (i j : Fin 2) :
      intervalStieltjesIntegral (FL j)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2 i)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} +
        intervalStieltjesIntegral (FK i)
          (fun t ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1 j)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      (edgeVertices K (b : Real.Angle)).2 i * (edgeVertices L (b : Real.Angle)).2 j -
        (edgeVertices K (a : Real.Angle)).1 i * (edgeVertices L (a : Real.Angle)).1 j := by
    have h := intervalStieltjes_integration_by_parts_Ioo a b hab (FK i) (FL j)
    have h1 : intervalStieltjesIntegral (FL j) (Function.leftLim (FK i).toFun)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
        intervalStieltjesIntegral (FL j)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2 i)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} :=
      VectorMeasure.setIntegral_congr_fun
        (fun t ht ↦ leftLim_positiveVertex_coordinate K FK hFK i t ht.1)
    have h2 : (FL j).toFun =
        fun t : Set.Icc a b ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1 j :=
      funext (hFL j)
    rw [h1, leftLim_positiveVertex_coordinate K FK hFK i ⟨b, hab.le, le_rfl⟩ hab,
      leftLim_positiveVertex_coordinate L FL hFL j ⟨b, hab.le, le_rfl⟩ hab,
      hFK i ⟨a, le_rfl, hab.le⟩, hFL j ⟨a, le_rfl, hab.le⟩, h2] at h
    exact h
  have k01 := key 0 1
  have k10 := key 1 0
  simp only [openIntervalCrossIntegral, segmentArea, planeCrossProduct]
  linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Arc Jordan
-/

public section

noncomputable section

namespace MovingSofa

open Set

/-- A rectifiable path traverses a segment with monotone surjective reparametrizations. -/
def IsSegmentTraversal (γ : RectifiablePathData) (P Q : Point) : Prop :=
  ∃ (φ : Set.Icc (0 : ℝ) 1 → Set.Icc γ.a γ.b)
    (τ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1),
    Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
    Continuous τ ∧ Monotone τ ∧ Function.Surjective τ ∧
    ∀ s, γ.path.val (φ s) = (1 - (τ s : ℝ)) • P + (τ s : ℝ) • Q

/-- A rectifiable path traverses an oriented Jordan arc in reverse. -/
def IsReverseArcTraversal (γ : RectifiablePathData) {A : OrientedJordanArc}
    (p : ArcBVParametrization A) : Prop :=
  ∃ (φ : Set.Icc (0 : ℝ) 1 → Set.Icc γ.a γ.b)
    (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc p.a p.b),
    Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
    Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
    ∀ s, γ.path.val (φ s) = p.path.val
      ⟨p.a + p.b - (ψ s : ℝ), by
        constructor <;> linarith [(ψ s).property.1, (ψ s).property.2]⟩

/-- A path traversing an oriented segment has the segment's signed area. -/
theorem IsSegmentTraversal.curveAreaFunctional_eq {γ : RectifiablePathData} {P Q : Point}
    (h : IsSegmentTraversal γ P Q) : curveAreaFunctional γ.path = segmentArea P Q := by
  obtain ⟨φ, τ, hφc, hφm, hφs, hτc, hτm, hτs, heq⟩ := h
  obtain ⟨y, hy, hymono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    γ.ordered zero_le_one γ.path φ hφc hφs (Or.inl hφm)
  obtain ⟨y', hy', hy'mono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    zero_le_one zero_le_one (lineSegmentBVPath P Q) τ hτc hτs (Or.inl hτm)
  have hyy : y = y' := by
    refine Subtype.ext ?_
    rw [hy, hy']
    funext s
    rw [Function.comp_apply, Function.comp_apply, heq s, lineSegmentBVPath_apply]
  rw [← hymono hφm, hyy, hy'mono hτm, curveAreaFunctional_lineSegmentBVPath]

/-- A path traversing an oriented Jordan arc backwards has the opposite signed area. -/
theorem IsReverseArcTraversal.curveAreaFunctional_eq {γ : RectifiablePathData}
    {A : OrientedJordanArc} {p : ArcBVParametrization A} (h : IsReverseArcTraversal γ p) :
    curveAreaFunctional γ.path = -curveAreaFunctional p.path := by
  obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := h
  set ρ : Set.Icc (0 : ℝ) 1 → Set.Icc p.a p.b := fun s ↦
    ⟨p.a + p.b - (ψ s : ℝ), by
      constructor <;> linarith [(ψ s).property.1, (ψ s).property.2]⟩ with hρdef
  have hcomp : ∀ s, γ.path.val (φ s) = p.path.val (ρ s) := heq
  have hρc : Continuous ρ :=
    (continuous_const.sub (continuous_subtype_val.comp hψc)).subtype_mk _
  have hρa : Antitone ρ := fun s t hst ↦
    Subtype.coe_le_coe.mp (by
      simp only [hρdef]
      linarith [Subtype.coe_le_coe.mpr (hψm hst)])
  have hρs : Function.Surjective ρ := by
    intro u
    obtain ⟨s, hs⟩ := hψs ⟨p.a + p.b - (u : ℝ), by
      constructor <;> linarith [u.property.1, u.property.2]⟩
    refine ⟨s, Subtype.ext ?_⟩
    have hval : ((ψ s : ℝ)) = p.a + p.b - (u : ℝ) := congrArg Subtype.val hs
    simp only [hρdef, hval]
    ring
  obtain ⟨y, hy, hymono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    γ.ordered zero_le_one γ.path φ hφc hφs (Or.inl hφm)
  obtain ⟨y', hy', -, hy'anti⟩ := curveArea_comp_monotone_or_antitone_surjective
    p.ordered zero_le_one p.path ρ hρc hρs (Or.inr hρa)
  have hyy : y = y' := by
    refine Subtype.ext ?_
    rw [hy, hy']
    funext s
    exact hcomp s
  rw [← hymono hφm, hyy, hy'anti hρa]

private def reverseArcPath {A : OrientedJordanArc} (p : ArcBVParametrization A) :
    ContinuousBVPaths p.a p.b where
  val := p.path.val ∘ Set.Icc.reverse p.ordered
  property := by
    constructor
    · exact p.path.property.1.comp (Set.Icc.continuous_reverse p.ordered)
    · intro i
      exact BoundedVariationOn.comp_antitone_surjective_Icc p.ordered
        (p.path.property.2 i) (Set.Icc.antitone_reverse p.ordered)
        (Set.Icc.surjective_reverse p.ordered)

private lemma reverseArcPath_start {A : OrientedJordanArc}
    (p : ArcBVParametrization A) :
    (reverseArcPath p).val ⟨p.a, le_rfl, p.ordered⟩ = A.endPoint := by
  simpa [reverseArcPath, Set.Icc.reverse] using p.end_eq

private lemma isSegmentTraversal_lineSegmentBVPath (P Q : Point) :
    IsSegmentTraversal
      { a := 0, b := 1, ordered := by norm_num, path := lineSegmentBVPath P Q } P Q := by
  refine ⟨id, id, continuous_id, monotone_id, Function.surjective_id,
    continuous_id, monotone_id, Function.surjective_id, ?_⟩
  intro s
  simp [lineSegmentBVPath, Path.segment_apply, AffineMap.lineMap_apply_module']
  module

private theorem boundedVariation_concatUnitIntervals_coordinate_jordan
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) (i : Fin 2) :
    BoundedVariationOn (fun t ↦ Function.concatUnitIntervals p.val q.val t i) Set.univ :=
  boundedVariation_concatUnitIntervals_coordinate p q hjoin i

private def concatUnitPaths_jordan (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  ⟨Function.concatUnitIntervals p.val q.val,
    Function.continuous_concatUnitIntervals p.property.1 q.property.1 hjoin,
    boundedVariation_concatUnitIntervals_coordinate_jordan p q hjoin⟩

private lemma concatUnitPaths_jordan_end (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    (concatUnitPaths_jordan p q hjoin).val ⟨2, by norm_num⟩ =
      q.val ⟨1, by norm_num⟩ := by
  change Function.concatUnitIntervals p.val q.val ⟨2, by norm_num⟩ = _
  unfold Function.concatUnitIntervals
  simp only
  rw [ite_eq_right (by norm_num : ¬(2 : ℝ) ≤ 1)]
  apply congrArg q.val
  apply Subtype.ext
  norm_num

private def unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Set.Icc (0 : ℝ) 1 → Set.Icc a b :=
  Set.Icc.convexComb ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

private lemma continuous_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Continuous (unitParam_jordan a b hab) :=
  Set.Icc.continuous_convexComb _ _

private lemma monotone_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Monotone (unitParam_jordan a b hab) := by
  intro s t hst
  apply Subtype.coe_le_coe.mp
  simp only [unitParam_jordan, Set.Icc.coe_convexComb]
  nlinarith [show (s : ℝ) ≤ t from hst]

private lemma surjective_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective (unitParam_jordan a b hab) :=
  surjective_convexComb_endpoints a b hab

private theorem exists_reverseArcUnitPath {A : OrientedJordanArc}
    (p : ArcBVParametrization A) :
    ∃ q : ContinuousBVPaths 0 1,
      q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered ∧
      IsReverseArcTraversal
        { a := 0, b := 1, ordered := by norm_num, path := q } p := by
  obtain ⟨q, hq⟩ := continuousBVPaths_comp_monotone_surjective p.ordered
    (reverseArcPath p) (unitParam_jordan p.a p.b p.ordered)
    (continuous_unitParam_jordan _ _ _) (monotone_unitParam_jordan _ _ _)
    (surjective_unitParam_jordan _ _ _)
  refine ⟨q, hq, ?_⟩
  let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
  let ψ := unitParam_jordan p.a p.b p.ordered
  refine ⟨φ, ψ, continuous_id, monotone_id, Function.surjective_id,
    continuous_unitParam_jordan _ _ _, monotone_unitParam_jordan _ _ _,
    surjective_unitParam_jordan _ _ _, ?_⟩
  intro s
  rw [hq]
  change p.path.val (Set.Icc.reverse p.ordered (ψ s)) = p.path.val _
  simp only [ψ, unitParam_jordan, Set.Icc.reverse, Set.Icc.coe_convexComb]

private def doubleParam_jordan : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 :=
  fun t ↦ ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩

private lemma continuous_doubleParam_jordan : Continuous doubleParam_jordan :=
  Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

private lemma monotone_doubleParam_jordan : Monotone doubleParam_jordan := by
  intro s t hst
  exact Subtype.coe_le_coe.mp (mul_le_mul_of_nonneg_left hst (by norm_num))

private lemma surjective_doubleParam_jordan : Function.Surjective doubleParam_jordan := by
  intro t
  refine ⟨⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩, ?_⟩
  apply Subtype.ext
  change 2 * ((t : ℝ) / 2) = t
  ring

private def reparamTwoToUnit_jordan (q : ContinuousBVPaths 0 2) :
    ContinuousBVPaths 0 1 :=
  ⟨q.val ∘ doubleParam_jordan,
    q.property.1.comp continuous_doubleParam_jordan,
    fun i ↦ BoundedVariationOn.comp_monotone_surjective_Icc (by norm_num)
      (q.property.2 i) monotone_doubleParam_jordan surjective_doubleParam_jordan⟩

private lemma reparamTwoToUnit_one (q : ContinuousBVPaths 0 2) :
    (reparamTwoToUnit_jordan q).val ⟨1, by norm_num⟩ = q.val ⟨2, by norm_num⟩ := by
  change q.val (doubleParam_jordan ⟨1, by norm_num⟩) = q.val ⟨2, by norm_num⟩
  rw [show doubleParam_jordan ⟨1, by norm_num⟩ = ⟨2, by norm_num⟩ by
    apply Subtype.ext
    norm_num [doubleParam_jordan]]

private def concatThreeUnitPaths_jordan (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  let q := concatUnitPaths_jordan p₀ p₁ h01
  concatUnitPaths_jordan (reparamTwoToUnit_jordan q) p₂ (by
    rw [reparamTwoToUnit_one]
    exact (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12)

private lemma concatThreeUnitPaths_first_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
        p₀.val t := by
  simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan,
    reparamTwoToUnit_jordan]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left (by nlinarith [t.property.1, t.property.2] : (t : ℝ) / 2 ≤ 1)]
  have houter : Set.projIcc 0 1 (by norm_num) ((t : ℝ) / 2) =
      ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩ := by
    exact Set.projIcc_of_mem (by norm_num) (by
      constructor <;> nlinarith [t.property.1, t.property.2])
  rw [houter]
  change Function.concatUnitIntervals p₀.val p₁.val
    (doubleParam_jordan ⟨(t : ℝ) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩) = p₀.val t
  rw [show doubleParam_jordan ⟨(t : ℝ) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
      ⟨(t : ℝ), ⟨t.property.1, t.property.2.trans (by norm_num)⟩⟩ by
    apply Subtype.ext
    simp [doubleParam_jordan]
    ring]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left t.property.2]
  apply congrArg p₀.val
  exact Set.projIcc_of_mem (by norm_num) t.property

private lemma concatThreeUnitPaths_middle_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨(1 + (t : ℝ)) / 2, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ = p₁.val t := by
  simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan,
    reparamTwoToUnit_jordan]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left (by nlinarith [t.property.2] : (1 + (t : ℝ)) / 2 ≤ 1)]
  have houter : Set.projIcc 0 1 (by norm_num) ((1 + (t : ℝ)) / 2) =
      ⟨(1 + (t : ℝ)) / 2, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ := by
    exact Set.projIcc_of_mem (by norm_num) (by
      constructor <;> nlinarith [t.property.1, t.property.2])
  rw [houter]
  change Function.concatUnitIntervals p₀.val p₁.val
    (doubleParam_jordan ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩) = p₁.val t
  rw [show doubleParam_jordan ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
      ⟨1 + (t : ℝ), by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ by
    apply Subtype.ext
    simp [doubleParam_jordan]
    ring]
  unfold Function.concatUnitIntervals
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
    subst t
    simpa using h01
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    rw [ite_eq_right (by linarith : ¬(1 + (t : ℝ) ≤ 1))]
    apply congrArg p₁.val
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [show 1 + (t : ℝ) - 1 = t by ring, min_eq_right t.property.2,
      max_eq_right t.property.1]

private lemma concatThreeUnitPaths_last_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨1 + (t : ℝ), by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ = p₂.val t := by
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
    rw [ht']
    rw [show (⟨1 + ((⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ), by
      norm_num⟩ : Set.Icc (0 : ℝ) 2) = ⟨1, by norm_num⟩ by
      apply Subtype.ext
      norm_num]
    change (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩
    unfold concatThreeUnitPaths_jordan
    change Function.concatUnitIntervals _ p₂.val ⟨1, by norm_num⟩ = _
    unfold Function.concatUnitIntervals
    rw [ite_eq_left (by norm_num : (1 : ℝ) ≤ 1)]
    calc
      _ = (reparamTwoToUnit_jordan
          (concatUnitPaths_jordan p₀ p₁ h01)).val ⟨1, by norm_num⟩ := by
        apply congrArg _
        apply Subtype.ext
        norm_num [Set.coe_projIcc]
      _ = _ := by
        rw [reparamTwoToUnit_one, concatUnitPaths_jordan_end]
        exact h12
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan]
    unfold Function.concatUnitIntervals
    rw [ite_eq_right (by linarith : ¬(1 + (t : ℝ) ≤ 1))]
    apply congrArg p₂.val
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [show 1 + (t : ℝ) - 1 = t by ring, min_eq_right t.property.2,
      max_eq_right t.property.1]

private theorem isPathConcatenation_concatThreeUnitPaths_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num,
        path := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12 }
      ![{ a := 0, b := 1, ordered := by norm_num, path := p₀ },
        { a := 0, b := 1, ordered := by norm_num, path := p₁ },
        { a := 0, b := 1, ordered := by norm_num, path := p₂ }] := by
  let cuts : Fin 4 → Set.Icc (0 : ℝ) 2 :=
    ![⟨0, by norm_num⟩, ⟨1 / 2, by norm_num⟩,
      ⟨1, by norm_num⟩, ⟨2, by norm_num⟩]
  refine ⟨by norm_num, cuts, ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] at hij <;>
      norm_num [cuts, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro i
  fin_cases i
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 0) : ℝ)
        (cuts (Fin.succ 0) : ℝ) := fun t ↦ ⟨(t : ℝ) / 2, by
          change (0 : ℝ) ≤ (t : ℝ) / 2 ∧ (t : ℝ) / 2 ≤ 1 / 2
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk (continuous_subtype_val.div_const 2) _,
      ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      exact Subtype.coe_le_coe.mp (div_le_div_of_nonneg_right hst (by norm_num))
    · intro t
      have ht : (0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 / 2 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨2 * (t : ℝ), by
        change (0 : ℝ) ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change 2 * (t : ℝ) / 2 = t
      ring
    · intro t
      exact concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 t
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 1) : ℝ)
        (cuts (Fin.succ 1) : ℝ) := fun t ↦ ⟨(1 + (t : ℝ)) / 2, by
          change (1 / 2 : ℝ) ≤ (1 + (t : ℝ)) / 2 ∧ (1 + (t : ℝ)) / 2 ≤ 1
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk
      ((continuous_const.add continuous_subtype_val).div_const 2) _, ?_, ?_,
      continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      apply Subtype.coe_le_coe.mp
      have hst' : (s : ℝ) ≤ t := hst
      change (1 + (s : ℝ)) / 2 ≤ (1 + (t : ℝ)) / 2
      linarith
    · intro t
      have ht : (1 / 2 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨2 * (t : ℝ) - 1, by
        change (0 : ℝ) ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change (1 + (2 * (t : ℝ) - 1)) / 2 = t
      ring
    · intro t
      exact concatThreeUnitPaths_middle_jordan p₀ p₁ p₂ h01 h12 t
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 2) : ℝ)
        (cuts (Fin.succ 2) : ℝ) := fun t ↦ ⟨1 + (t : ℝ), by
          change (1 : ℝ) ≤ 1 + (t : ℝ) ∧ 1 + (t : ℝ) ≤ 2
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk
      (continuous_const.add continuous_subtype_val) _, ?_, ?_,
      continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      apply Subtype.coe_le_coe.mp
      have hst' : (s : ℝ) ≤ t := hst
      change 1 + (s : ℝ) ≤ 1 + (t : ℝ)
      linarith
    · intro t
      have ht : (1 : ℝ) ≤ t ∧ (t : ℝ) ≤ 2 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨(t : ℝ) - 1, by
        change (0 : ℝ) ≤ (t : ℝ) - 1 ∧ (t : ℝ) - 1 ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change 1 + ((t : ℝ) - 1) = t
      ring
    · intro t
      exact concatThreeUnitPaths_last_jordan p₀ p₁ p₂ h01 h12 t

private lemma range_comp_surjective {α β γ : Type*} (f : β → γ) (g : α → β)
    (hg : Function.Surjective g) : Set.range (f ∘ g) = Set.range f := by
  apply Set.Subset.antisymm
  · exact Set.range_comp_subset_range _ _
  · rintro y ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hg x
    exact ⟨z, rfl⟩

private lemma range_concatThreeUnitPaths_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    Set.range (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val =
      Set.range p₀.val ∪ Set.range p₁.val ∪ Set.range p₂.val := by
  let q := concatUnitPaths_jordan p₀ p₁ h01
  have hqend : q.val ⟨2, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ :=
    (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12
  have houter : (reparamTwoToUnit_jordan q).val ⟨1, by norm_num⟩ =
      p₂.val ⟨0, by norm_num⟩ := (reparamTwoToUnit_one q).trans hqend
  change Set.range (Function.concatUnitIntervals
    (reparamTwoToUnit_jordan q).val p₂.val) = _
  rw [Function.range_concatUnitIntervals _ _ houter]
  have hrepr : Set.range (reparamTwoToUnit_jordan q).val = Set.range q.val := by
    exact range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
  rw [hrepr]
  change Set.range (Function.concatUnitIntervals p₀.val p₁.val) ∪ Set.range p₂.val = _
  rw [Function.range_concatUnitIntervals _ _ h01]

private lemma range_reverseArcUnitPath {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (q : ContinuousBVPaths 0 1)
    (hq : q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered) :
    Set.range q.val = A.carrier := by
  rw [hq, range_comp_surjective _ _ (surjective_unitParam_jordan _ _ _)]
  change Set.range (p.path.val ∘ Set.Icc.reverse p.ordered) = _
  rw [range_comp_surjective _ _ (Set.Icc.surjective_reverse p.ordered), p.range_eq]

private theorem segment_fst_supportingIntersection_inter_body
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
        (K : Set Point) = {(edgeVertices K (a : Real.Angle)).1} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d, hd, hO⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  change O = P + d • tangentVector (a : Real.Angle) at hO
  apply Set.Subset.antisymm
  · rintro z ⟨hzseg, hzK⟩
    rw [segment_eq_image] at hzseg
    obtain ⟨r, hr, rfl⟩ := hzseg
    have hPn := (edgeVertices_fst_mem K (a : Real.Angle)).2
    have hOn := supportingIntersection_inner_left K a b
    have hzline : inner ℝ ((1 - r) • P + r • O) (normalVector (a : Real.Angle)) =
        supportValue K a := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      change (1 - r) * inner ℝ P (normalVector (a : Real.Angle)) +
        r * inner ℝ O (normalVector (a : Real.Angle)) = _
      rw [show inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a from hPn,
        show inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a from hOn]
      ring
    have hzedge : (1 - r) • P + r • O ∈ exposedEdge K (a : Real.Angle) :=
      ⟨hzK, hzline⟩
    have hzle : inner ℝ ((1 - r) • P + r • O) (tangentVector (a : Real.Angle)) ≤
        inner ℝ P (tangentVector (a : Real.Angle)) := by
      rw [inner_edgeVertices_fst_tangent]
      exact le_csSup ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddAbove ⟨_, hzedge, rfl⟩
    rw [hO, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_add_left, real_inner_smul_left, inner_tangentVector_self] at hzle
    have hr0 : r = 0 := by nlinarith [hr.1]
    simp [hr0]
  · intro z hz
    have hzP : z = P := by simpa [P] using hz
    subst z
    exact ⟨left_mem_segment ℝ P O, (edgeVertices_fst_mem K _).1⟩

private theorem segment_supportingIntersection_snd_inter_body
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 ∩
        (K : Set Point) = {(edgeVertices K (b : Real.Angle)).2} := by
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d, hd, hO⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  change O = Q - d • tangentVector (b : Real.Angle) at hO
  apply Set.Subset.antisymm
  · rintro z ⟨hzseg, hzK⟩
    rw [segment_eq_image] at hzseg
    obtain ⟨r, hr, rfl⟩ := hzseg
    have hQn := (edgeVertices_snd_mem K (b : Real.Angle)).2
    have hOn := supportingIntersection_inner_right K a b
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
    have hzline : inner ℝ ((1 - r) • O + r • Q) (normalVector (b : Real.Angle)) =
        supportValue K b := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      change (1 - r) * inner ℝ O (normalVector (b : Real.Angle)) +
        r * inner ℝ Q (normalVector (b : Real.Angle)) = _
      rw [show inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b from hOn,
        show inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b from hQn]
      ring
    have hzedge : (1 - r) • O + r • Q ∈ exposedEdge K (b : Real.Angle) :=
      ⟨hzK, hzline⟩
    have hzge : inner ℝ Q (tangentVector (b : Real.Angle)) ≤
        inner ℝ ((1 - r) • O + r • Q) (tangentVector (b : Real.Angle)) := by
      rw [inner_edgeVertices_snd_tangent]
      exact csInf_le ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddBelow ⟨_, hzedge, rfl⟩
    rw [hO, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_sub_left, real_inner_smul_left, inner_tangentVector_self] at hzge
    have hr1 : r = 1 := by nlinarith [hr.2]
    simp [hr1]
  · intro z hz
    have hzQ : z = Q := by simpa [Q] using hz
    subst z
    exact ⟨right_mem_segment ℝ O Q, (edgeVertices_snd_mem K _).1⟩

/-- A convex boundary arc lies in its convex body. -/
theorem convexBoundaryArc_subset_body (K : ConvexBody Point) (a b : ℝ) :
    convexBoundaryArc K a b ⊆ (K : Set Point) := by
  rintro z (hz | hz)
  · rcases hz with hz | hz
    · simpa using hz ▸ (edgeVertices_fst_mem K (a : Real.Angle)).1
    · rcases Set.mem_iUnion.mp hz with ⟨t, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨_, hz⟩
      exact hz.1
  · simpa using hz ▸ (edgeVertices_snd_mem K (b : Real.Angle)).1

private theorem segment_fst_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
        convexBoundaryArc K a b = {(edgeVertices K (a : Real.Angle)).1} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ segment ℝ (edgeVertices K (a : Real.Angle)).1
        (supportingIntersection K a b) ∩ (K : Set Point) :=
      ⟨hz.1, convexBoundaryArc_subset_body K a b hz.2⟩
    simpa [segment_fst_supportingIntersection_inter_body K hab hba hne] using hz'
  · intro z hz
    have hzP : z = (edgeVertices K (a : Real.Angle)).1 := by simpa using hz
    subst z
    exact ⟨left_mem_segment _ _ _, Or.inl (Or.inl rfl)⟩

private theorem segment_snd_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 ∩
        convexBoundaryArc K a b = {(edgeVertices K (b : Real.Angle)).2} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ segment ℝ (supportingIntersection K a b)
        (edgeVertices K (b : Real.Angle)).2 ∩ (K : Set Point) :=
      ⟨hz.1, convexBoundaryArc_subset_body K a b hz.2⟩
    simpa [segment_supportingIntersection_snd_inter_body K hab hba hne] using hz'
  · intro z hz
    have hzQ : z = (edgeVertices K (b : Real.Angle)).2 := by simpa using hz
    subst z
    exact ⟨right_mem_segment _ _ _, Or.inr rfl⟩

private theorem supporting_segments_inter
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
      segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 =
        {supportingIntersection K a b} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a :=
    (edgeVertices_fst_mem K _).2
  have hOa : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
    supportingIntersection_inner_left K a b
  have hOb : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hQb : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b :=
    (edgeVertices_snd_mem K _).2
  have inner_eq_of_segment {X Y z v : Point} {c : ℝ}
      (hX : inner ℝ X v = c) (hY : inner ℝ Y v = c)
      (hz : z ∈ segment ℝ X Y) : inner ℝ z v = c := by
    rw [segment_eq_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hX, hY]
    ring
  apply Set.Subset.antisymm
  · rintro z ⟨hz₁, hz₂⟩
    have hza : inner ℝ z (normalVector (a : Real.Angle)) = supportValue K a :=
      inner_eq_of_segment hPa hOa hz₁
    have hzb : inner ℝ z (normalVector (b : Real.Angle)) = supportValue K b :=
      inner_eq_of_segment hOb hQb hz₂
    have hna : inner ℝ (z - O) (normalVector (a : Real.Angle)) = 0 := by
      rw [inner_sub_left, hza, hOa, sub_self]
    have hnb : inner ℝ (z - O) (normalVector (b : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzb, hOb, sub_self]
    have hnexp : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    have hta : inner ℝ (z - O) (tangentVector (a : Real.Angle)) = 0 := by
      rw [hnexp, inner_add_right, inner_smul_right, inner_smul_right, hna,
        mul_zero, zero_add] at hnb
      exact (mul_eq_zero.mp hnb).resolve_left hsin.ne'
    have hzo : z = O := by
      rw [show z = O + (z - O) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
        (z - O) (a : Real.Angle), hna, hta, zero_smul, zero_smul, add_zero]
      simp
    simp [O, hzo]
  · intro z hz
    have hzO : z = O := by simpa [O] using hz
    subst z
    exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

private def brokenSupportPath (K : ConvexBody Point) (a b : ℝ) :
    Path (edgeVertices K (a : Real.Angle)).1 (edgeVertices K (b : Real.Angle)).2 :=
  (Path.segment (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b)).trans
    (Path.segment (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2)

private theorem path_segment_injective {P Q : Point} (hPQ : P ≠ Q) :
    Function.Injective (Path.segment P Q) := by
  intro s t hst
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ hPQ (by
    simpa only [Path.segment_apply] using hst)

private theorem brokenSupportPath_injective
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    Function.Injective (brokenSupportPath K a b) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d₀, hd₀, hPO⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  obtain ⟨d₁, hd₁, hQO⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  change O = P + d₀ • tangentVector (a : Real.Angle) at hPO
  change O = Q - d₁ • tangentVector (b : Real.Angle) at hQO
  have htne (u : Real.Angle) : tangentVector u ≠ 0 := by
    intro hu
    have hone : inner ℝ (tangentVector u) (tangentVector u) = 1 := by
      rw [← u.coe_toReal]
      exact inner_tangentVector_self u.toReal
    rw [hu] at hone
    simp at hone
  have hPOne : P ≠ O := by
    intro h
    have hz : d₀ • tangentVector (a : Real.Angle) = 0 := by
      calc
        d₀ • tangentVector (a : Real.Angle) = O - P := by rw [hPO]; abel
        _ = 0 := by rw [← h, sub_self]
    exact hd₀.ne' ((smul_eq_zero.mp hz).resolve_right (htne _))
  have hOQne : O ≠ Q := by
    intro h
    have hz : d₁ • tangentVector (b : Real.Angle) = 0 := by
      calc
        d₁ • tangentVector (b : Real.Angle) = Q - O := by rw [hQO]; abel
        _ = 0 := by rw [h, sub_self]
    exact hd₁.ne' ((smul_eq_zero.mp hz).resolve_right (htne _))
  intro s t hst
  change ((Path.segment P O).trans (Path.segment O Q)) s =
    ((Path.segment P O).trans (Path.segment O Q)) t at hst
  simp only [Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have heq := path_segment_injective hPOne hst
    apply Subtype.ext
    have := congrArg Subtype.val heq
    norm_num at this ⊢
    linarith
  · have hmem : (Path.segment P O) ⟨2 * (s : ℝ), by constructor <;> linarith
        [s.property.1, s.property.2]⟩ ∈ segment ℝ P O ∩ segment ℝ O Q := by
      constructor
      · rw [← Path.range_segment]
        exact Set.mem_range_self _
      · rw [hst, ← Path.range_segment]
        exact Set.mem_range_self _
    have hO := Set.ext_iff.mp (supporting_segments_inter K hab hba) _ |>.mp hmem
    have hs1 : (2 : ℝ) * s = 1 := by
      have heq := path_segment_injective hPOne (hO.trans (Path.target _).symm)
      exact congrArg Subtype.val heq
    have ht0 : 2 * (t : ℝ) - 1 = 0 := by
      have heq := path_segment_injective hOQne (hst.symm.trans (hO.trans (Path.source _).symm))
      exact congrArg Subtype.val heq
    apply Subtype.ext
    linarith
  · have hmem : (Path.segment P O) ⟨2 * (t : ℝ), by constructor <;> linarith
        [t.property.1, t.property.2]⟩ ∈ segment ℝ P O ∩ segment ℝ O Q := by
      constructor
      · rw [← Path.range_segment]
        exact Set.mem_range_self _
      · rw [← hst, ← Path.range_segment]
        exact Set.mem_range_self _
    have hO := Set.ext_iff.mp (supporting_segments_inter K hab hba) _ |>.mp hmem
    have ht1 : (2 : ℝ) * t = 1 := by
      have heq := path_segment_injective hPOne (hO.trans (Path.target _).symm)
      exact congrArg Subtype.val heq
    have hs0 : 2 * (s : ℝ) - 1 = 0 := by
      have heq := path_segment_injective hOQne (hst.trans (hO.trans (Path.source _).symm))
      exact congrArg Subtype.val heq
    apply Subtype.ext
    linarith
  · have heq := path_segment_injective hOQne hst
    apply Subtype.ext
    have := congrArg Subtype.val heq
    norm_num at this ⊢
    linarith

private theorem brokenSupportPath_range
    (K : ConvexBody Point) (a b : ℝ) :
    Set.range (brokenSupportPath K a b) =
      segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∪
      segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 := by
  simp [brokenSupportPath, Path.trans_range, Path.range_segment]

private theorem brokenSupportPath_range_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    Set.range (brokenSupportPath K a b) ∩ convexBoundaryArc K a b =
      {(edgeVertices K (a : Real.Angle)).1, (edgeVertices K (b : Real.Angle)).2} := by
  rw [brokenSupportPath_range, Set.union_inter_distrib_right,
    segment_fst_inter_convexBoundaryArc K hab hba hne,
    segment_snd_inter_convexBoundaryArc K hab hba hne]
  ext z
  simp [or_comm]

private def arcUnitPath {A : OrientedJordanArc} (p : ArcBVParametrization A) :
    Path A.startPoint A.endPoint where
  toFun := p.path.val ∘ unitParam_jordan p.a p.b p.ordered
  source' := by
    change p.path.val (unitParam_jordan p.a p.b p.ordered 0) = A.startPoint
    rw [show unitParam_jordan p.a p.b p.ordered 0 = ⟨p.a, le_rfl, p.ordered⟩ by
      exact Set.Icc.convexComb_zero _ _]
    exact p.start_eq
  target' := by
    change p.path.val (unitParam_jordan p.a p.b p.ordered 1) = A.endPoint
    rw [show unitParam_jordan p.a p.b p.ordered 1 = ⟨p.b, p.ordered, le_rfl⟩ by
      exact Set.Icc.convexComb_one _ _]
    exact p.end_eq
  continuous_toFun := p.path.property.1.comp (continuous_unitParam_jordan _ _ _)

private theorem arcUnitPath_injective {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (hne : A.startPoint ≠ A.endPoint) :
    Function.Injective (arcUnitPath p) := by
  intro s t hst
  have hpab : p.a < p.b := lt_of_le_of_ne p.ordered fun hab ↦ by
    have heq : (⟨p.a, le_rfl, p.ordered⟩ : Set.Icc p.a p.b) =
        ⟨p.b, p.ordered, le_rfl⟩ := Subtype.ext hab
    exact hne (p.start_eq.symm.trans ((congrArg p.path.val heq).trans p.end_eq))
  have huv := p.injective (by simpa [arcUnitPath, Function.comp_apply] using hst)
  exact (strictMono_convexComb_of_lt _ _ hpab).injective huv

private theorem arcUnitPath_range {A : OrientedJordanArc}
    (p : ArcBVParametrization A) : Set.range (arcUnitPath p) = A.carrier := by
  change Set.range (p.path.val ∘ unitParam_jordan p.a p.b p.ordered) = _
  rw [range_comp_surjective _ _ (surjective_unitParam_jordan _ _ _), p.range_eq]

private theorem isJordanCurve_of_tau {Γ : Set Point} (hΓ : TauCeti.IsJordanCurve Γ) :
    IsJordanCurve Γ := by
  obtain ⟨e⟩ := TauCeti.isJordanCurve_iff.mp hΓ
  refine ⟨fun z ↦ (e.symm z : Point), continuous_subtype_val.comp e.symm.continuous,
    fun z w h ↦ e.symm.injective (Subtype.ext h), ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    exact (e.symm u).property
  · intro z hz
    exact ⟨e ⟨z, hz⟩, congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)⟩

private theorem convexArc_broken_isJordanCurve
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A) :
    IsJordanCurve (Set.range (brokenSupportPath K a b) ∪ A.val.carrier) := by
  have hmeet : Set.range (brokenSupportPath K a b) ∩ Set.range (arcUnitPath p) =
      {(edgeVertices K (a : Real.Angle)).1, (edgeVertices K (b : Real.Angle)).2} := by
    rw [arcUnitPath_range, hA.1]
    exact brokenSupportPath_range_inter_convexBoundaryArc K hab hba hne
  have hstart : A.val.startPoint = (edgeVertices K (a : Real.Angle)).1 := hA.2.1
  have hend : A.val.endPoint = (edgeVertices K (b : Real.Angle)).2 := hA.2.2
  have hstartend : A.val.startPoint ≠ A.val.endPoint := by simpa [hstart, hend] using hne
  let δ : Path (edgeVertices K (a : Real.Angle)).1
      (edgeVertices K (b : Real.Angle)).2 :=
    (arcUnitPath p).cast hstart.symm hend.symm
  have hδinj : Function.Injective δ := by
    simpa only [δ, Path.cast_coe] using arcUnitPath_injective p hstartend
  have hδrange : Set.range δ = A.val.carrier := by
    simpa only [δ, Path.cast_coe] using arcUnitPath_range p
  have htau := TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair
    (brokenSupportPath_injective K hab hba hne) hδinj (by
      rw [hδrange]
      simpa [hstart, hend, arcUnitPath_range] using hmeet)
  rw [hδrange] at htau
  exact isJordanCurve_of_tau htau

private theorem jordanInterior_subset_closedConvexHull {Γ : Set Point}
    (hΓ : Γ.Nonempty) : jordanInterior Γ ⊆ closedConvexHull ℝ Γ := by
  intro p hp
  exact TauCeti.filledHull_subset_closedConvexHull hΓ (TauCeti.mem_filledHull_iff.mpr hp.2)

/-- The region enclosed by a loop inside a closed convex set stays inside that set. -/
theorem jordanInterior_subset_of_subset_closed_convex
    {Γ C : Set Point} (hΓ : Γ.Nonempty) (hsub : Γ ⊆ C)
    (hconv : Convex ℝ C) (hclosed : IsClosed C) : jordanInterior Γ ⊆ C := by
  exact (jordanInterior_subset_closedConvexHull hΓ).trans
    (closedConvexHull_min hsub hconv hclosed)

private theorem isOpen_jordanInterior_of_isJordanCurve {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) : IsOpen (jordanInterior Γ) := by
  obtain ⟨U, V, hUopen, hVopen, hUconn, hVconn, hUbounded, hVunbounded, hdis,
    hcover, hfrontU, hfrontV, hcompU, hcompV⟩ := jordan_separation hΓ
  have heq : jordanInterior Γ = U := by
    ext p
    constructor
    · intro hp
      have hpUV : p ∈ U ∪ V := hcover.symm.subset hp.1
      rcases hpUV with hpU | hpV
      · exact hpU
      · exfalso
        exact hVunbounded (by simpa only [hcompV p hpV] using hp.2)
    · intro hpU
      constructor
      · intro hpΓ
        have hpcompl : p ∈ Γᶜ := hcover ▸ Or.inl hpU
        exact hpcompl hpΓ
      · simpa only [hcompU p hpU] using hUbounded
  rw [heq]
  exact hUopen

private theorem jordanInterior_subset_interior_of_subset_closed_convex
    {Γ C : Set Point} (hJordan : IsJordanCurve Γ) (hΓ : Γ.Nonempty)
    (hsub : Γ ⊆ C) (hconv : Convex ℝ C) (hclosed : IsClosed C) :
    jordanInterior Γ ⊆ interior C := by
  intro p hp
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset
    ((isOpen_jordanInterior_of_isJordanCurve hJordan).mem_nhds hp)
    (jordanInterior_subset_of_subset_closed_convex hΓ hsub hconv hclosed)

private theorem injOn_concatUnitPaths_jordan
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩)
    (hclose : q.val ⟨1, by norm_num⟩ = p.val ⟨0, by norm_num⟩)
    (hp : Function.Injective p.val) (hq : Function.Injective q.val)
    (hmeet : Set.range p.val ∩ Set.range q.val =
      {p.val ⟨0, by norm_num⟩, p.val ⟨1, by norm_num⟩}) :
    Set.InjOn (concatUnitPaths_jordan p q hjoin).val {t | (t : ℝ) < 2} := by
  intro s hs t ht hst
  change (s : ℝ) < 2 at hs
  change (t : ℝ) < 2 at ht
  change Function.concatUnitIntervals p.val q.val s =
    Function.concatUnitIntervals p.val q.val t at hst
  unfold Function.concatUnitIntervals at hst
  split_ifs at hst with hs₁ ht₁ ht₁
  · have heq := congrArg Subtype.val (hp hst)
    apply Subtype.ext
    simp only [Set.coe_projIcc] at heq
    rw [min_eq_right hs₁, max_eq_right s.property.1,
      min_eq_right ht₁, max_eq_right t.property.1] at heq
    exact heq
  · have hmem : p.val (Set.projIcc 0 1 (by norm_num) (s : ℝ)) ∈
        Set.range p.val ∩ Set.range q.val :=
      ⟨Set.mem_range_self _, hst ▸ Set.mem_range_self _⟩
    rw [hmeet] at hmem
    rcases hmem with hP | hQ
    · have hs0 := congrArg Subtype.val (hp hP)
      have ht1 := congrArg Subtype.val (hq (hst.symm.trans (hP.trans hclose.symm)))
      simp only [Set.coe_projIcc] at hs0 ht1
      rw [min_eq_right hs₁, max_eq_right s.property.1] at hs0
      rw [min_eq_right (by linarith [t.property.2]),
        max_eq_right (by linarith)] at ht1
      exfalso
      linarith
    · have hs1 := congrArg Subtype.val (hp hQ)
      have ht0 := congrArg Subtype.val (hq (hst.symm.trans (hQ.trans hjoin)))
      simp only [Set.coe_projIcc] at hs1 ht0
      rw [min_eq_right hs₁, max_eq_right s.property.1] at hs1
      rw [min_eq_right (by linarith [t.property.2]),
        max_eq_right (by linarith)] at ht0
      apply Subtype.ext
      linarith
  · have hmem : p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) ∈
        Set.range p.val ∩ Set.range q.val :=
      ⟨Set.mem_range_self _, hst.symm ▸ Set.mem_range_self _⟩
    rw [hmeet] at hmem
    rcases hmem with hP | hQ
    · have ht0 := congrArg Subtype.val (hp hP)
      have hs1 := congrArg Subtype.val (hq (hst.trans (hP.trans hclose.symm)))
      simp only [Set.coe_projIcc] at ht0 hs1
      rw [min_eq_right ht₁, max_eq_right t.property.1] at ht0
      rw [min_eq_right (by linarith [s.property.2]),
        max_eq_right (by linarith)] at hs1
      exfalso
      linarith
    · have ht1 := congrArg Subtype.val (hp hQ)
      have hs0 := congrArg Subtype.val (hq (hst.trans (hQ.trans hjoin)))
      simp only [Set.coe_projIcc] at ht1 hs0
      rw [min_eq_right ht₁, max_eq_right t.property.1] at ht1
      rw [min_eq_right (by linarith [s.property.2]),
        max_eq_right (by linarith)] at hs0
      apply Subtype.ext
      linarith
  · have heq := congrArg Subtype.val (hq hst)
    apply Subtype.ext
    simp only [Set.coe_projIcc] at heq
    rw [min_eq_right (by linarith [s.property.2]), max_eq_right (by linarith),
      min_eq_right (by linarith [t.property.2]), max_eq_right (by linarith)] at heq
    linarith

private theorem reparam_support_segments_eq_brokenSupportPath
    (K : ConvexBody Point) (a b : ℝ)
    (h01 : (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)).val
      ⟨1, by norm_num⟩ =
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
        ⟨0, by norm_num⟩) :
    (reparamTwoToUnit_jordan (concatUnitPaths_jordan
      (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
      h01)).val = brokenSupportPath K a b := by
  funext t
  simp only [reparamTwoToUnit_jordan, Function.comp_apply, doubleParam_jordan,
    concatUnitPaths_jordan, lineSegmentBVPath, brokenSupportPath]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [Path.trans_apply, dite_eq_left ht]
    unfold Function.concatUnitIntervals
    rw [ite_eq_left (by linarith)]
    congr 1
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by linarith [t.property.2]),
      max_eq_right (by linarith [t.property.1])]
  · simp only [Path.trans_apply, dite_eq_right ht]
    unfold Function.concatUnitIntervals
    rw [ite_eq_right (by linarith)]
    congr 1
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by linarith [t.property.2]),
      max_eq_right (by linarith [t.property.1])]

private theorem reverseArcUnitPath_injective {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (q : ContinuousBVPaths 0 1)
    (hq : q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered)
    (hne : A.startPoint ≠ A.endPoint) : Function.Injective q.val := by
  have hpab : p.a < p.b := lt_of_le_of_ne p.ordered fun hab ↦ by
    have heq : (⟨p.a, le_rfl, p.ordered⟩ : Set.Icc p.a p.b) =
        ⟨p.b, p.ordered, le_rfl⟩ := Subtype.ext hab
    exact hne (p.start_eq.symm.trans ((congrArg p.path.val heq).trans p.end_eq))
  intro s t hst
  rw [hq] at hst
  have hrev := p.injective hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hrev
  simp only [Set.Icc.reverse] at hval
  have huv : (unitParam_jordan p.a p.b p.ordered s : ℝ) =
      unitParam_jordan p.a p.b p.ordered t := by linarith
  exact congrArg Subtype.val
    ((strictMono_convexComb_of_lt _ _ hpab).injective (Subtype.ext huv))

private theorem brokenSupportPath_union_convexArc_subset_endpointHalfPlanes
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) :
    Set.range (brokenSupportPath K a b) ∪ A.val.carrier ⊆
      (supportingLineHalfPlane K (a : Real.Angle)).2 ∩
        (supportingLineHalfPlane K (b : Real.Angle)).2 := by
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hK (t : Real.Angle) : (K : Set Point) ⊆ (supportingLineHalfPlane K t).2 := by
    intro p hp
    exact inner_le_supportValue K hp t
  have hOa : supportingIntersection K a b ∈ (supportingLineHalfPlane K a).2 := by
    exact le_of_eq (supportingIntersection_inner_left K a b)
  have hOb : supportingIntersection K a b ∈ (supportingLineHalfPlane K b).2 := by
    exact le_of_eq (supportingIntersection_inner_right K a b hsin.ne')
  have hconv (t : Real.Angle) : Convex ℝ (supportingLineHalfPlane K t).2 := by
    intro x hx y hy u v hu hv huv
    change inner ℝ x (normalVector t) ≤ supportValue K t at hx
    change inner ℝ y (normalVector t) ≤ supportValue K t at hy
    change inner ℝ (u • x + v • y) (normalVector t) ≤ supportValue K t
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    calc
      u * inner ℝ x (normalVector t) + v * inner ℝ y (normalVector t) ≤
          u * supportValue K t + v * supportValue K t :=
        add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
      _ = supportValue K t := by rw [← add_mul, huv, one_mul]
  intro p hp
  rcases hp with hp | hp
  · rw [brokenSupportPath_range] at hp
    rcases hp with hp | hp
    · constructor
      · exact (hconv a).segment_subset
          (hK a (edgeVertices_fst_mem K (a : Real.Angle)).1) hOa hp
      · exact (hconv b).segment_subset
          (hK b (edgeVertices_fst_mem K (a : Real.Angle)).1) hOb hp
    · constructor
      · exact (hconv a).segment_subset hOa
          (hK a (edgeVertices_snd_mem K (b : Real.Angle)).1) hp
      · exact (hconv b).segment_subset hOb
          (hK b (edgeVertices_snd_mem K (b : Real.Angle)).1) hp
  · have hpK : p ∈ K := convexBoundaryArc_subset_body K a b (hA.1 ▸ hp)
    exact ⟨hK a hpK, hK b hpK⟩

private theorem convexBoundaryArc_exists_support_eq
    (K : ConvexBody Point) {a b : ℝ} (hab : a ≤ b) {p : Point}
    (hp : p ∈ convexBoundaryArc K a b) :
    ∃ t ∈ Set.Icc a b,
      inner ℝ p (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  rcases hp with (hp | hp) | hp
  · subst p
    exact ⟨a, ⟨le_rfl, hab⟩, (edgeVertices_fst_mem K (a : Real.Angle)).2⟩
  · simp only [Set.mem_iUnion] at hp
    obtain ⟨t, htab, hp⟩ := hp
    exact ⟨t, ⟨htab.1.le, htab.2.le⟩, hp.2⟩
  · subst p
    exact ⟨b, ⟨hab, le_rfl⟩, (edgeVertices_snd_mem K (b : Real.Angle)).2⟩

private theorem inner_midpoint_normal_pos {a b t : ℝ}
    (_hab : a < b) (hba : b < a + Real.pi) (ht : t ∈ Set.Icc a b) :
    0 < inner ℝ (normalVector (((a + b) / 2 : ℝ) : Real.Angle))
      (normalVector (t : Real.Angle)) := by
  rw [inner_normalVector_normalVector]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [ht.1, ht.2]

private theorem sub_pos_midpoint_normal_inner_lt_support
    (K : ConvexBody Point) {a b r : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    {p : Point}
    (hp : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2) (hr : 0 < r)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    inner ℝ (p - r • normalVector (((a + b) / 2 : ℝ) : Real.Angle))
        (normalVector (t : Real.Angle)) < supportValue K (t : Real.Angle) := by
  have hple : inner ℝ p (normalVector (t : Real.Angle)) ≤
      supportValue K (t : Real.Angle) := by
    exact Set.mem_iInter₂.mp hp t ht
  rw [inner_sub_left, real_inner_smul_left]
  have hdot := inner_midpoint_normal_pos hab hba ht
  nlinarith

private theorem brokenSupportPath_mem_support_eq
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hp : p ∈ Set.range (brokenSupportPath K a b)) :
    inner ℝ p (normalVector (a : Real.Angle)) = supportValue K a ∨
      inner ℝ p (normalVector (b : Real.Angle)) = supportValue K b := by
  have hsin : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
  rw [brokenSupportPath_range] at hp
  rcases hp with hp | hp
  · left
    rw [segment_eq_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      (edgeVertices_fst_mem K (a : Real.Angle)).2,
      supportingIntersection_inner_left]
    ring
  · right
    rw [segment_eq_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      supportingIntersection_inner_right K a b hsin,
      (edgeVertices_snd_mem K (b : Real.Angle)).2]
    ring

private theorem sub_pos_midpoint_normal_not_mem_boundary_loop
    (K : ConvexBody Point) {a b r : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) {p : Point}
    (hp : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2) (hr : 0 < r) :
    p - r • normalVector (((a + b) / 2 : ℝ) : Real.Angle) ∉
      Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
  intro hq
  rcases hq with hq | hq
  · rcases brokenSupportPath_mem_support_eq K hab hba hq with hqa | hqb
    · exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr a
        ⟨le_rfl, hab.le⟩)) hqa
    · exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr b
        ⟨hab.le, le_rfl⟩)) hqb
  · obtain ⟨t, ht, hqt⟩ := convexBoundaryArc_exists_support_eq K hab.le (hA.1 ▸ hq)
    exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr t ht)) hqt

private theorem boundaryLoop_component_unbounded_of_mem_supportIntersection
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) {p : Point}
    (hpX : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2)
    (hpΓ : p ∉ Set.range (brokenSupportPath K a b) ∪ A.val.carrier) :
    ¬ Bornology.IsBounded (connectedComponentIn
      (Set.range (brokenSupportPath K a b) ∪ A.val.carrier)ᶜ p) := by
  let n := normalVector (((a + b) / 2 : ℝ) : Real.Angle)
  let f : ℝ → Point := fun r ↦ p - r • n
  have hf : Continuous f := continuous_const.sub (continuous_id.smul continuous_const)
  have hpre : IsPreconnected (f '' Set.Ici 0) :=
    isPreconnected_Ici.image f hf.continuousOn
  have hsub : f '' Set.Ici 0 ⊆
      (Set.range (brokenSupportPath K a b) ∪ A.val.carrier)ᶜ := by
    rintro q ⟨r, hr, rfl⟩
    by_cases hr0 : r = 0
    · simpa [f, hr0] using hpΓ
    · exact sub_pos_midpoint_normal_not_mem_boundary_loop K hab hba A hA hpX
        (lt_of_le_of_ne hr (Ne.symm hr0))
  have hpmem : p ∈ f '' Set.Ici 0 := ⟨0, by simp, by simp [f]⟩
  have hcomp := hpre.subset_connectedComponentIn hpmem hsub
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hn : ‖n‖ = 1 := norm_normalVector_real ((a + b) / 2)
  let r := max 0 (C + ‖p‖ + 1)
  have hr : 0 ≤ r := le_max_left _ _
  have hq := hC (f r) (hcomp ⟨r, hr, rfl⟩)
  have hdiff : ‖r • n‖ ≤ C + ‖p‖ := by
    calc
      ‖r • n‖ = ‖p - f r‖ := by simp [f]
      _ ≤ ‖p‖ + ‖f r‖ := norm_sub_le _ _
      _ ≤ C + ‖p‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hn, mul_one] at hdiff
  have hlower : C + ‖p‖ + 1 ≤ r := le_max_right _ _
  linarith

private theorem jordanInterior_boundaryLoop_disjoint_supportIntersection
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) :
    Disjoint (jordanInterior (Set.range (brokenSupportPath K a b) ∪ A.val.carrier))
      (⋂ t ∈ Set.Icc a b, (supportingLineHalfPlane K (t : Real.Angle)).2) := by
  rw [Set.disjoint_left]
  intro p hpI hpX
  exact boundaryLoop_component_unbounded_of_mem_supportIntersection
    K hab hba A hA hpX hpI.1 hpI.2

private theorem isClosed_supportingLineHalfPlane_lower
    (K : ConvexBody Point) (t : Real.Angle) :
    IsClosed (supportingLineHalfPlane K t).2 := by
  exact isClosed_le (continuous_id.inner continuous_const) continuous_const

private theorem convex_supportingLineHalfPlane_lower
    (K : ConvexBody Point) (t : Real.Angle) :
    Convex ℝ (supportingLineHalfPlane K t).2 := by
  intro x hx y hy u v hu hv huv
  change inner ℝ x (normalVector t) ≤ supportValue K t at hx
  change inner ℝ y (normalVector t) ≤ supportValue K t at hy
  change inner ℝ (u • x + v • y) (normalVector t) ≤ supportValue K t
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp only [RCLike.conj_to_real]
  calc
    u * inner ℝ x (normalVector t) + v * inner ℝ y (normalVector t) ≤
        u * supportValue K t + v * supportValue K t :=
      add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
    _ = supportValue K t := by rw [← add_mul, huv, one_mul]

private theorem jordanInterior_boundaryLoop_subset_endpointHalfPlanes
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A) :
    jordanInterior (Set.range (brokenSupportPath K a b) ∪ A.val.carrier) ⊆
      interior ((supportingLineHalfPlane K a).2 ∩
        (supportingLineHalfPlane K b).2) := by
  apply jordanInterior_subset_interior_of_subset_closed_convex
    (convexArc_broken_isJordanCurve K hab hba hne A p hA)
  · exact (Set.range_nonempty _).inl
  · exact brokenSupportPath_union_convexArc_subset_endpointHalfPlanes K hab hba A hA
  · exact (convex_supportingLineHalfPlane_lower K a).inter
      (convex_supportingLineHalfPlane_lower K b)
  · exact (isClosed_supportingLineHalfPlane_lower K a).inter
      (isClosed_supportingLineHalfPlane_lower K b)

private theorem concatThree_first_image_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val ''
        Set.Icc (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 2) ⟨1 / 2, by norm_num⟩ =
      Set.range p₀.val := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    have htt : (t : ℝ) ≤ 1 / 2 := by exact_mod_cast ht.2
    let u : Set.Icc (0 : ℝ) 1 := ⟨2 * (t : ℝ), by
      constructor <;> nlinarith [t.property.1, htt]⟩
    refine ⟨u, ?_⟩
    have heq : (⟨(u : ℝ) / 2, by
        constructor <;> nlinarith [u.property.1, u.property.2]⟩ : Set.Icc (0 : ℝ) 2) = t := by
      apply Subtype.ext
      dsimp [u]
      ring
    rw [← heq]
    exact (concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 u).symm
  · rintro z ⟨u, rfl⟩
    let t : Set.Icc (0 : ℝ) 2 := ⟨(u : ℝ) / 2, by
      constructor <;> nlinarith [u.property.1, u.property.2]⟩
    refine ⟨t, ⟨by exact Subtype.coe_le_coe.mp t.property.1,
      by change (t : ℝ) ≤ 1 / 2; dsimp [t]; linarith [u.property.2]⟩, ?_⟩
    exact concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 u

private theorem concatThree_convexArc_oriented
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A)
    (p₂ : ContinuousBVPaths 0 1)
    (hp₂ : p₂.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered)
    (h01 : (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)).val
      ⟨1, by norm_num⟩ =
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
        ⟨0, by norm_num⟩)
    (h12 : (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
      ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 2)
      (Set.range (concatThreeUnitPaths_jordan
        (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
        (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
        p₂ h01 h12).val) true
      (concatThreeUnitPaths_jordan
        (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
        (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
        p₂ h01 h12).val := by
  let p₀ := lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)
  let p₁ := lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2
  let q := concatUnitPaths_jordan p₀ p₁ h01
  let q' := reparamTwoToUnit_jordan q
  let γ := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  have hq' : q'.val = brokenSupportPath K a b :=
    reparam_support_segments_eq_brokenSupportPath K a b h01
  have hpq : Function.Injective q'.val := hq' ▸ brokenSupportPath_injective K hab hba hne
  have hPneQ : A.val.startPoint ≠ A.val.endPoint := by simpa [hA.2.1, hA.2.2] using hne
  have hp₂inj := reverseArcUnitPath_injective p p₂ hp₂ hPneQ
  have hqrange : Set.range q'.val = Set.range (brokenSupportPath K a b) := by rw [hq']
  have hp₂range : Set.range p₂.val = A.val.carrier := range_reverseArcUnitPath p p₂ hp₂
  have hmeet : Set.range q'.val ∩ Set.range p₂.val =
      {q'.val ⟨0, by norm_num⟩, q'.val ⟨1, by norm_num⟩} := by
    rw [hqrange, hp₂range, hA.1,
      brokenSupportPath_range_inter_convexBoundaryArc K hab hba hne, hq']
    simp [brokenSupportPath]
  have hclose : p₂.val ⟨1, by norm_num⟩ = q'.val ⟨0, by norm_num⟩ := by
    rw [hp₂]
    simp [q', hq', brokenSupportPath, reverseArcPath, unitParam_jordan, Set.Icc.reverse,
      hA.2.1, p.start_eq]
  have hjoin : q'.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ := by
    rw [show q'.val ⟨1, by norm_num⟩ = q.val ⟨2, by norm_num⟩ from
      reparamTwoToUnit_one q]
    exact (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12
  have hinj := injOn_concatUnitPaths_jordan q' p₂ hjoin
    hclose hpq hp₂inj hmeet
  have hrange : Set.range γ.val = Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
    rw [show γ = concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12 by rfl]
    rw [range_concatThreeUnitPaths_jordan, hp₂range]
    have hq'q : Set.range q'.val = Set.range q.val :=
      range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
    rw [← Function.range_concatUnitIntervals p₀.val p₁.val h01]
    change Set.range q.val ∪ A.val.carrier = _
    rw [← hq'q, hqrange]
  have hJordan := convexArc_broken_isJordanCurve K hab hba hne A p hA
  obtain ⟨d, hd, hdir⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  have hclosedγ : γ.val ⟨0, by norm_num⟩ = γ.val ⟨2, by norm_num⟩ := by
    simpa [γ, concatThreeUnitPaths_jordan, concatUnitPaths_jordan, q', q] using hclose.symm
  have hinjγ : Set.InjOn γ.val {t | (t : ℝ) < 2} := by
    simpa [γ, concatThreeUnitPaths_jordan, q', q] using hinj
  have hhalfγ (t : Set.Icc (0 : ℝ) 2) :
      γ.val t ∈ normalHalfPlane (a : Real.Angle) (supportValue K a) false false :=
    (brokenSupportPath_union_convexArc_subset_endpointHalfPlanes K hab hba A hA
      (hrange ▸ Set.mem_range_self t)).1
  let s : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let t : Set.Icc (0 : ℝ) 2 := ⟨1 / 2, by norm_num⟩
  have hs : γ.val s = (edgeVertices K (a : Real.Angle)).1 := by
    simpa [s, γ, p₀, lineSegmentBVPath] using
      concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 ⟨0, by norm_num⟩
  have ht : γ.val t = supportingIntersection K a b := by
    simpa [t, γ, p₀, lineSegmentBVPath] using
      concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 ⟨1, by norm_num⟩
  exact jordan_counterclockwise_of_supporting_segment 0 2 (by norm_num) γ.val
    γ.property.1 (hrange ▸ hJordan) hclosedγ hinjγ
    (a : Real.Angle) (supportValue K a) hhalfγ s t (by
      change (0 : ℝ) < 1 / 2
      norm_num)
    (by rw [hs]; exact (edgeVertices_fst_mem K (a : Real.Angle)).2)
    d hd (by rw [hs, ht]; exact hdir)
    (by
      rw [hs, ht]
      rw [show γ.val '' Set.Icc s t = Set.range p₀.val by
        simpa [s, t, γ] using concatThree_first_image_jordan p₀ p₁ p₂ h01 h12]
      exact Path.range_segment _ _)

private theorem exists_rectifiableOrientedArc_segment_jordan (P Q : Point) (hPQ : P ≠ Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = segment ℝ P Q ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  let Γ : OrientedJordanArc :=
    { carrier := segment ℝ P Q
      startPoint := P
      endPoint := Q
      parametrizable := by
        refine ⟨0, 1, by norm_num, Path.segment P Q,
          (Path.segment P Q).continuous, Path.segment_injective_of_ne hPQ,
          Path.range_segment P Q, ?_, ?_⟩ <;> simp }
  let z : ArcBVParametrization Γ :=
    { a := 0
      b := 1
      ordered := by norm_num
      path := lineSegmentBVPath P Q
      injective := Path.segment_injective_of_ne hPQ
      range_eq := Path.range_segment P Q
      start_eq := by simp [lineSegmentBVPath, Γ]
      end_eq := by simp [lineSegmentBVPath, Γ] }
  let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
  exact ⟨A, rfl, rfl, rfl⟩

private theorem exists_rectifiableOrientedArc_convexBoundaryArc_jordan
    (K : ConvexBody Point) (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K a).1 ≠ (edgeVertices K b).2) :
    ∃ A : RectifiableOrientedArc, RealizesConvexArc K a b A := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
  obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
      hright, hterminal⟩ := hcut hne
  by_cases hInt : (interior (K' : Set Point)).Nonempty
  · obtain ⟨A, hcarrier, hstart, hend⟩ :=
      exists_rectifiableOrientedArc_convexBoundaryArc_of_cut K K' a b t c P Q
        hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright hterminal hInt
    exact ⟨A, hcarrier, hstart, hend⟩
  · have hInt' : interior (K' : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hInt
    have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
      hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright hInt'
    obtain ⟨A, hcarrier, hstart, hend⟩ :=
      exists_rectifiableOrientedArc_segment_jordan P Q hne
    exact ⟨A, hcarrier.trans harc.symm, hstart, hend⟩

/-- The supporting segments and reversed convex boundary arc form a counterclockwise Jordan
curve. -/
theorem convexBoundaryArc_jordan (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K a).1 ≠ (edgeVertices K b).2) :
    ∃ (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
      (γ : RectifiablePathData) (pieces : Fin 3 → RectifiablePathData),
      RealizesConvexArc K a b A ∧
      IsSegmentTraversal (pieces 0) (edgeVertices K a).1 (supportingIntersection K a b) ∧
      IsSegmentTraversal (pieces 1) (supportingIntersection K a b) (edgeVertices K b).2 ∧
      IsReverseArcTraversal (pieces 2) p ∧ IsPathConcatenation γ pieces ∧
      IsOrientedJordanParametrization γ.ordered (Set.range γ.path.val) true γ.path.val ∧
      jordanInterior (Set.range γ.path.val) ⊆
        interior ((supportingLineHalfPlane K a).2 ∩ (supportingLineHalfPlane K b).2) ∧
      Disjoint (jordanInterior (Set.range γ.path.val))
        (⋂ t ∈ Set.Icc a b, (supportingLineHalfPlane K (t : Real.Angle)).2) := by
  obtain ⟨A, hA⟩ :=
    exists_rectifiableOrientedArc_convexBoundaryArc_jordan K a b hab hba hne
  let p : ArcBVParametrization A.val := Classical.choice A.property
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  let p₀ := lineSegmentBVPath P O
  let p₁ := lineSegmentBVPath O Q
  obtain ⟨p₂, hp₂, hp₂rev⟩ := exists_reverseArcUnitPath p
  have h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩ := by
    simp [p₀, p₁, lineSegmentBVPath]
  have h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ := by
    rw [hp₂]
    change p₁.val ⟨1, by norm_num⟩ =
      (reverseArcPath p).val (unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩)
    rw [show unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩ =
      ⟨p.a, le_rfl, p.ordered⟩ by exact Set.Icc.convexComb_zero _ _]
    rw [reverseArcPath_start]
    simpa [p₁, Q, lineSegmentBVPath, Path.segment_apply,
      AffineMap.lineMap_apply_module'] using hA.2.2.symm
  let γpath := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  let γ : RectifiablePathData :=
    { a := 0, b := 2, ordered := by norm_num, path := γpath }
  let pieces : Fin 3 → RectifiablePathData :=
    ![{ a := 0, b := 1, ordered := by norm_num, path := p₀ },
      { a := 0, b := 1, ordered := by norm_num, path := p₁ },
      { a := 0, b := 1, ordered := by norm_num, path := p₂ }]
  have horient := concatThree_convexArc_oriented K hab hba hne A p hA p₂ hp₂ h01 h12
  have hrange : Set.range γ.path.val =
      Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
    change Set.range (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val = _
    rw [range_concatThreeUnitPaths_jordan, range_reverseArcUnitPath p p₂ hp₂]
    rw [← Function.range_concatUnitIntervals p₀.val p₁.val h01]
    let q := concatUnitPaths_jordan p₀ p₁ h01
    have hrepr : Set.range (reparamTwoToUnit_jordan q).val = Set.range q.val :=
      range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
    change Set.range q.val ∪ A.val.carrier = _
    rw [← hrepr, show (reparamTwoToUnit_jordan q).val = brokenSupportPath K a b by
      simpa [q, p₀, p₁, P, Q, O] using
        reparam_support_segments_eq_brokenSupportPath K a b h01]
  refine ⟨A, p, γ, pieces, hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pieces, P, O, Matrix.cons_val_zero] using
      isSegmentTraversal_lineSegmentBVPath P O
  · simpa [pieces, Q, O, Matrix.cons_val_zero, Matrix.cons_val_one] using
      isSegmentTraversal_lineSegmentBVPath O Q
  · simpa [pieces, Matrix.cons_val_zero, Matrix.cons_val_one] using hp₂rev
  · simpa [γ, γpath, pieces] using
      isPathConcatenation_concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  · simpa [γ, γpath, p₀, p₁] using horient
  · rw [hrange]
    exact jordanInterior_boundaryLoop_subset_endpointHalfPlanes K hab hba hne A p hA
  · rw [hrange]
    exact jordanInterior_boundaryLoop_disjoint_supportIntersection K hab hba A hA

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area of the region between a convex arc and its supporting tangents

The loop built from a convex boundary arc and the two tangent segments meeting at the
intersection of the arc's endpoint supporting lines bounds the "Mamikon region" cut off by
those tangents.  The single result here bounds that region's signed area by the measure of any
set that receives it.
-/

public section

noncomputable section

namespace MovingSofa

/-- The region between a convex boundary arc and its two supporting tangent segments has area
at most that of any finite-measure set that receives every point of a closed convex carrier of
the body which lies inside both endpoint supporting half-planes but outside the body. -/
theorem convexArc_tangentRegion_area_le (B : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    {C : Set Point} (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hBC : (B : Set Point) ⊆ C)
    (hOC : supportingIntersection B (a : Real.Angle) (b : Real.Angle) ∈ C)
    {E : Set Point} (hE : MeasureTheory.volume E ≠ ⊤)
    (hsubE : ∀ q ∈ interior ((supportingLineHalfPlane B (a : Real.Angle)).2 ∩
        (supportingLineHalfPlane B (b : Real.Angle)).2),
      q ∈ C → q ∉ (B : Set Point) → q ∈ E) :
    segmentArea (edgeVertices B (a : Real.Angle)).1
        (supportingIntersection B (a : Real.Angle) (b : Real.Angle)) +
      segmentArea (supportingIntersection B (a : Real.Angle) (b : Real.Angle))
        (edgeVertices B (b : Real.Angle)).2 -
      convexArcArea B a b ≤ ClassicalResults.area E := by
  have harea0 : (0 : ℝ) ≤ ClassicalResults.area E := ENNReal.toReal_nonneg
  by_cases hPQ : (edgeVertices B (a : Real.Angle)).1 = (edgeVertices B (b : Real.Angle)).2
  · -- coincident endpoints: the cut lemma collapses the arc and the intersection to one point
    obtain ⟨hO, hcar⟩ := (convexBoundaryArc_cut B a b hab hba _ _ _ rfl rfl rfl).1 hPQ
    obtain ⟨Δ, hΔcar, hΔstart, hΔend, hΔarea⟩ :=
      (segmentArea_jordan_and_frame (edgeVertices B (a : Real.Angle)).1
        (edgeVertices B (a : Real.Angle)).1).1
    have hreal : RealizesConvexArc B a b Δ :=
      ⟨hΔcar.trans ((segment_same ℝ _).trans hcar.symm), hΔstart, hΔend.trans hPQ⟩
    have hzero : segmentArea (edgeVertices B (a : Real.Angle)).1
        (edgeVertices B (a : Real.Angle)).1 = 0 := by
      simp only [segmentArea, planeCrossProduct]
      ring
    rw [convexArcArea_eq_jordanArcArea_of_realizes hreal, hΔarea, hO, ← hPQ, hzero]
    simpa using harea0
  · obtain ⟨A, p, γ, pieces, hA, hs0, hs1, hrev, hconcat, horient, hint, hdisj⟩ :=
      convexBoundaryArc_jordan B a b hab hba hPQ
    have hΓne : (Set.range γ.path.val).Nonempty :=
      ⟨_, ⟨⟨γ.a, le_rfl, γ.ordered⟩, rfl⟩⟩
    have hpiece0 : Set.range (pieces 0).path.val ⊆ C := by
      obtain ⟨φ, τ, -, -, hφs, -, -, -, heq⟩ := hs0
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      exact hconv (hBC (edgeVertices_fst_mem B _).1) hOC
        (by linarith [(τ s).property.2]) (τ s).property.1 (by ring)
    have hpiece1 : Set.range (pieces 1).path.val ⊆ C := by
      obtain ⟨φ, τ, -, -, hφs, -, -, -, heq⟩ := hs1
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      exact hconv hOC (hBC (edgeVertices_snd_mem B _).1)
        (by linarith [(τ s).property.2]) (τ s).property.1 (by ring)
    have hpiece2 : Set.range (pieces 2).path.val ⊆ C := by
      obtain ⟨φ, ψ, -, -, hφs, -, -, -, heq⟩ := hrev
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      have hmem : ∀ v : Set.Icc p.a p.b, p.path.val v ∈ (B : Set Point) := by
        intro v
        have h : p.path.val v ∈ Set.range p.path.val := ⟨v, rfl⟩
        rw [p.range_eq, hA.1] at h
        exact convexBoundaryArc_subset_body B a b h
      exact hBC (hmem _)
    -- the whole loop lies in `C`, hence so does the region it encloses
    have hrangeC : Set.range γ.path.val ⊆ C := by
      refine hconcat.range_subset_iUnion.trans (Set.iUnion_subset ?_)
      intro i
      fin_cases i
      · exact hpiece0
      · exact hpiece1
      · exact hpiece2
    have hRC : jordanInterior (Set.range γ.path.val) ⊆ C :=
      jordanInterior_subset_of_subset_closed_convex hΓne hrangeC hconv hclosed
    -- `B` sits inside all of its supporting half-planes, so the region avoids `B`
    have hRnotB : ∀ q ∈ jordanInterior (Set.range γ.path.val), q ∉ (B : Set Point) := by
      intro q hq hqB
      refine Set.disjoint_left.mp hdisj hq (Set.mem_iInter₂.mpr fun t _ ↦ ?_)
      change inner ℝ q (normalVector (t : Real.Angle)) ≤ supportValue (B : Set Point) _
      exact inner_le_supportValue B hqB _
    have hRE : jordanInterior (Set.range γ.path.val) ⊆ E := fun q hq =>
      hsubE q (hint hq) (hRC hq) (hRnotB q hq)
    -- signed area of the counterclockwise loop is the area it encloses, and path additivity
    -- splits it into the two segments and the reversed arc
    have hloop : curveAreaFunctional γ.path =
        ClassicalResults.area (jordanInterior (Set.range γ.path.val)) :=
      curveArea_eq_jordanInterior_area γ.a γ.b γ.ordered _ γ.path horient
    have hparc : curveAreaFunctional p.path = convexArcArea B a b := by
      rw [convexArcArea_eq_jordanArcArea_of_realizes hA]
      change _ = curveAreaFunctional (Classical.choice A.property).path
      exact (curveArea_reparametrization.2.1 A.val A.val p
        (Classical.choice A.property) rfl).1 rfl rfl
    have hval : segmentArea (edgeVertices B (a : Real.Angle)).1
          (supportingIntersection B (a : Real.Angle) (b : Real.Angle)) +
        segmentArea (supportingIntersection B (a : Real.Angle) (b : Real.Angle))
          (edgeVertices B (b : Real.Angle)).2 - convexArcArea B a b =
        curveAreaFunctional γ.path := by
      rw [curveArea_concatenation γ pieces hconcat, Fin.sum_univ_three,
        hs0.curveAreaFunctional_eq, hs1.curveAreaFunctional_eq,
        hrev.curveAreaFunctional_eq, hparc]
      ring
    rw [hval, hloop]
    have hle : MeasureTheory.volume (jordanInterior (Set.range γ.path.val)) ≤
        MeasureTheory.volume E := MeasureTheory.measure_mono hRE
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hE hle) hE).mpr hle

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.Mamikon.Basic`.
* `Area.Variation`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Mamikon / Basic
-/

public section

noncomputable section

namespace MovingSofa

/-- The signed area between the convex boundary arc and a path on its supporting lines. -/
@[expose]
def mamikonFunctional (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (_hba : b < a + Real.pi) (z : ContinuousBVPaths a b)
    (_hz : ∀ t : Set.Icc a b,
      z.val t ∈ (supportingLineHalfPlane K (t.val : Real.Angle)).1) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1
      (z.val ⟨a, le_rfl, hab.le⟩) +
    curveAreaFunctional z +
    segmentArea (z.val ⟨b, hab.le, le_rfl⟩)
      (edgeVertices K (b : Real.Angle)).2 -
    convexArcArea K a b

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Variation
-/

public section

noncomputable section

open MeasureTheory Set
open scoped unitInterval

namespace MovingSofa

/-- Coordinatewise convex combination of two pairs of planar points. -/
@[expose]
def pointPairCombination (t : I) (x y : Point × Point) : Point × Point :=
  ((1 - (t : ℝ)) • x.1 + (t : ℝ) • y.1,
    (1 - (t : ℝ)) • x.2 + (t : ℝ) • y.2)

theorem segmentArea_variation :
    IsQuadraticFunctional pointPairCombination (fun x ↦ segmentArea x.1 x.2) ∧
    ∀ p q p' q' : Point,
      convexDirectionalDerivative pointPairCombination (fun x ↦ segmentArea x.1 x.2)
        (p, q) (p', q') =
      (planeCrossProduct (p' + q') (q - p) - 2 * planeCrossProduct p q) / 2 +
        (segmentArea q q' - segmentArea p p') := by
  let h : (Point × Point) → (Point × Point) → ℝ := fun x y ↦
    (planeCrossProduct x.1 y.2 + planeCrossProduct y.1 x.2) / 4
  have hh : IsConvexBilinear pointPairCombination pointPairCombination realCombination h := by
    constructor <;> intro x t y z <;>
      simp [h, pointPairCombination, realCombination, planeCrossProduct] <;> ring
  have hf (x : Point × Point) : segmentArea x.1 x.2 = h x x := by
    simp only [h, segmentArea]
    ring
  refine ⟨⟨h, hh, hf⟩, ?_⟩
  intro p q p' q'
  rw [(quadratic_directional_derivative pointPairCombination _ h hh hf).2.1]
  simp [h, segmentArea, planeCrossProduct]
  ring

/-- The pointwise convex combination of two continuous BV paths. -/
@[expose]
def bvPathCombination {a b : ℝ} (t : I) (x y : ContinuousBVPaths a b) :
    ContinuousBVPaths a b :=
  (1 - (t : ℝ)) • x + (t : ℝ) • y

private theorem coordinate_measure_smul_add_smul {a b : ℝ} (r s : ℝ)
    (x y : ContinuousBVPaths a b) (i : Fin 2) :
    intervalStieltjesMeasure (continuousBVCoordinate (r • x + s • y) i) =
      r • intervalStieltjesMeasure (continuousBVCoordinate x i) +
        s • intervalStieltjesMeasure (continuousBVCoordinate y i) := by
  obtain ⟨F, hF, hμ⟩ := intervalStieltjes_linear_combination a b
    (continuousBVCoordinate x i) (continuousBVCoordinate y i) r s
  rw [← hμ]
  refine congrArg _ (RightContinuousIntervalBV.toFun_injective (funext fun u ↦ ?_))
  simpa [continuousBVCoordinate] using (hF u).symm

private def coordinateIntegral {a b : ℝ} (x y : ContinuousBVPaths a b) (i j : Fin 2) : ℝ :=
  intervalStieltjesIntegral (continuousBVCoordinate y j) (fun t ↦ x.val t i) univ

private theorem coordinateIntegral_smul_add_smul_right {a b : ℝ} (r s : ℝ)
    (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral x (r • y + s • z) i j =
      r * coordinateIntegral x y i j + s * coordinateIntegral x z i j := by
  have hi (w : ContinuousBVPaths a b) :
      (intervalStieltjesMeasure (continuousBVCoordinate w j)).Integrable (fun s ↦ x.val s i) :=
    RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp x.property.1)
  unfold coordinateIntegral intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [coordinate_measure_smul_add_smul, VectorMeasure.integral_add_vectorMeasure
    ((hi y).smul_vectorMeasure _) ((hi z).smul_vectorMeasure _)]
  simp only [VectorMeasure.integral_smul_vectorMeasure, smul_eq_mul]

private theorem coordinateIntegral_smul_add_smul_left {a b : ℝ} (r s : ℝ)
    (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral (r • x + s • y) z i j =
      r * coordinateIntegral x z i j + s * coordinateIntegral y z i j := by
  have hi (w : ContinuousBVPaths a b) :
      (intervalStieltjesMeasure (continuousBVCoordinate z j)).Integrable (fun s ↦ w.val s i) :=
    RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp w.property.1)
  unfold coordinateIntegral intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  change (∫ᵛ u, r • x.val u i + s • y.val u i
    ∂[ContinuousLinearMap.mul ℝ ℝ; intervalStieltjesMeasure (continuousBVCoordinate z j)]) = _
  have hadd := VectorMeasure.integral_fun_add (B := ContinuousLinearMap.mul ℝ ℝ)
    ((hi x).smul r) ((hi y).smul s)
  simp only [Pi.smul_apply, VectorMeasure.integral_fun_smul] at hadd
  simpa only [smul_eq_mul] using hadd

private theorem coordinateIntegral_combination_right {a b : ℝ}
    (t : I) (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral x (bvPathCombination t y z) i j =
      (1 - (t : ℝ)) * coordinateIntegral x y i j + (t : ℝ) * coordinateIntegral x z i j :=
  coordinateIntegral_smul_add_smul_right _ _ x y z i j

private theorem coordinateIntegral_combination_left {a b : ℝ}
    (t : I) (x y z : ContinuousBVPaths a b) (i j : Fin 2) :
    coordinateIntegral (bvPathCombination t x y) z i j =
      (1 - (t : ℝ)) * coordinateIntegral x z i j + (t : ℝ) * coordinateIntegral y z i j :=
  coordinateIntegral_smul_add_smul_left _ _ x y z i j

private theorem coordinateIntegral_difference {a b : ℝ} (x y : ContinuousBVPaths a b)
    (i j : Fin 2) :
    intervalStieltjesIntegral (continuousBVCoordinate x j) (fun t ↦ y.val t i - x.val t i) univ =
      coordinateIntegral y x i j - coordinateIntegral x x i j := by
  unfold coordinateIntegral intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  exact VectorMeasure.integral_fun_sub
    (RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp y.property.1))
    (RightContinuousIntervalBV.integrable_of_continuous _
      ((PiLp.continuous_apply 2 _ i).comp x.property.1))

private theorem curveArea_quadratic_derivative (a b : ℝ) :
    IsQuadraticFunctional bvPathCombination (@curveAreaFunctional a b) ∧
    ∀ x y : ContinuousBVPaths a b,
      convexDirectionalDerivative bvPathCombination curveAreaFunctional x y =
        (coordinateIntegral x y 0 1 - coordinateIntegral x y 1 0 +
          (coordinateIntegral y x 0 1 - coordinateIntegral y x 1 0) -
          2 * (coordinateIntegral x x 0 1 - coordinateIntegral x x 1 0)) / 2 := by
  let h : ContinuousBVPaths a b → ContinuousBVPaths a b → ℝ := fun x y ↦
    (coordinateIntegral x y 0 1 - coordinateIntegral x y 1 0) / 2
  have hh : IsConvexBilinear bvPathCombination bvPathCombination realCombination h := by
    constructor
    · intro x t y z
      dsimp only [h]
      rw [coordinateIntegral_combination_right, coordinateIntegral_combination_right]
      simp only [realCombination]
      ring
    · intro x t y z
      dsimp only [h]
      rw [coordinateIntegral_combination_left, coordinateIntegral_combination_left]
      simp only [realCombination]
      ring
  have hf (x : ContinuousBVPaths a b) : curveAreaFunctional x = h x x := rfl
  refine ⟨⟨h, hh, hf⟩, ?_⟩
  intro x y
  rw [(quadratic_directional_derivative bvPathCombination _ h hh hf).2.1]
  dsimp only [h]
  ring

theorem curveArea_variation (a b : ℝ) (hab : a ≤ b) :
    IsQuadraticFunctional bvPathCombination (@curveAreaFunctional a b) ∧
    ∀ x y : ContinuousBVPaths a b,
      convexDirectionalDerivative bvPathCombination curveAreaFunctional x y =
      intervalStieltjesIntegral (continuousBVCoordinate x 1)
          (fun t ↦ y.val t 0 - x.val t 0) Set.univ -
        intervalStieltjesIntegral (continuousBVCoordinate x 0)
          (fun t ↦ y.val t 1 - x.val t 1) Set.univ +
        (segmentArea (x.val ⟨b, hab, le_rfl⟩) (y.val ⟨b, hab, le_rfl⟩) -
          segmentArea (x.val ⟨a, le_rfl, hab⟩) (y.val ⟨a, le_rfl, hab⟩)) := by
  obtain ⟨hq, hd⟩ := curveArea_quadratic_derivative a b
  refine ⟨hq, ?_⟩
  intro x y
  have hc (w : ContinuousBVPaths a b) (i : Fin 2) :
      Continuous (continuousBVCoordinate w i).toFun :=
    (PiLp.continuous_apply 2 _ i).comp w.property.1
  have h01 := intervalStieltjes_integration_by_parts_of_continuous a b hab
    (continuousBVCoordinate x 0) (continuousBVCoordinate y 1) (hc x 0) (hc y 1)
  have h10 := intervalStieltjes_integration_by_parts_of_continuous a b hab
    (continuousBVCoordinate x 1) (continuousBVCoordinate y 0) (hc x 1) (hc y 0)
  change coordinateIntegral y x 1 0 + coordinateIntegral x y 0 1 = _ at h01
  change coordinateIntegral y x 0 1 + coordinateIntegral x y 1 0 = _ at h10
  rw [hd, coordinateIntegral_difference, coordinateIntegral_difference]
  simp only [continuousBVCoordinate] at h01 h10
  simp only [segmentArea, planeCrossProduct]
  linarith

private theorem curveAreaFunctional_eq_coordinateIntegral {a b : ℝ}
    (x : ContinuousBVPaths a b) :
    curveAreaFunctional x = (coordinateIntegral x x 0 1 - coordinateIntegral x x 1 0) / 2 := rfl

/-- Translating a continuous BV path by another one adds the translating path's own signed area
and the two mixed cross integrals. -/
private theorem curveAreaFunctional_add {a b : ℝ}
    (x c : ContinuousBVPaths a b) :
    curveAreaFunctional (x + c) = curveAreaFunctional x + curveAreaFunctional c +
      (coordinateIntegral x c 0 1 - coordinateIntegral x c 1 0 +
        (coordinateIntegral c x 0 1 - coordinateIntegral c x 1 0)) / 2 := by
  have hone : x + c = (1 : ℝ) • x + (1 : ℝ) • c := by rw [one_smul, one_smul]
  simp only [curveAreaFunctional_eq_coordinateIntegral, hone,
    coordinateIntegral_smul_add_smul_left, coordinateIntegral_smul_add_smul_right]
  ring

/-- Translating a continuous BV path by a fixed one changes its signed area by a convex-linear
functional of the path: the two mixed Stieltjes cross integrals are separately linear and the
translating path's own area is constant. -/
theorem curveArea_translation_convexLinear {a b : ℝ}
    (c : ContinuousBVPaths a b) :
    IsConvexLinear bvPathCombination realCombination
      (fun x ↦ curveAreaFunctional (x + c) - curveAreaFunctional x) := by
  intro t x y
  change curveAreaFunctional ((1 - (t : ℝ)) • x + (t : ℝ) • y + c) -
      curveAreaFunctional ((1 - (t : ℝ)) • x + (t : ℝ) • y) =
    realCombination t (curveAreaFunctional (x + c) - curveAreaFunctional x)
      (curveAreaFunctional (y + c) - curveAreaFunctional y)
  rw [curveAreaFunctional_add ((1 - (t : ℝ)) • x + (t : ℝ) • y) c,
    curveAreaFunctional_add x c, curveAreaFunctional_add y c, realCombination]
  simp only [coordinateIntegral_smul_add_smul_left, coordinateIntegral_smul_add_smul_right]
  ring

theorem convexArcArea_variation (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) ∧
    ∀ K L : ConvexBody Point,
      convexDirectionalDerivative convexBodyCombination (fun M ↦ convexArcArea M a b) K L =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        (supportValue L t - supportValue K t) ∂surfaceAreaMeasure K) +
        (segmentArea (edgeVertices K (b : Real.Angle)).2 (edgeVertices L (b : Real.Angle)).2 -
          segmentArea (edgeVertices K (a : Real.Angle)).1 (edgeVertices L (a : Real.Angle)).1) := by
  obtain ⟨hbil0, F, hFtoFun, hFcross, hFarea⟩ := convexArc_bilinear_computation a b hab hba
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let B : ConvexBody Point → ConvexBody Point → ℝ := fun K L ↦
    (1 / 2 : ℝ) * ∫ t in E, supportValue K t ∂surfaceAreaMeasure L
  have hbil : IsConvexBilinear convexBodyCombination convexBodyCombination realCombination B :=
    hbil0
  have hfB : ∀ K : ConvexBody Point, convexArcArea K a b = B K K := fun K ↦
    (hFarea K).trans ((hFcross K K).1).symm
  refine ⟨⟨B, hbil, hfB⟩, ?_⟩
  intro K L
  have hcont (M : ConvexBody Point) : Continuous fun u : Real.Angle ↦ supportValue M u :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hint (M N : ConvexBody Point) :
      Integrable (fun u : Real.Angle ↦ supportValue M u) (surfaceAreaMeasure N) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure N) := (surfaceAreaMeasure_face_union N).1
    exact (hcont M).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hsub : (∫ t in E, (supportValue L t - supportValue K t) ∂surfaceAreaMeasure K) =
      2 * B L K - 2 * B K K := by
    rw [integral_sub (hint L K).restrict (hint K K).restrict]
    simp only [B, E]
    ring
  have hanti : B K L - B L K =
      segmentArea (edgeVertices K (b : Real.Angle)).2 (edgeVertices L (b : Real.Angle)).2 -
        segmentArea (edgeVertices K (a : Real.Angle)).1 (edgeVertices L (a : Real.Angle)).1 := by
    have h1 : B K L = openIntervalCrossIntegral (F L)
        (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) := (hFcross K L).2
    have h2 : B L K = openIntervalCrossIntegral (F K)
        (fun t : Set.Icc a b ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1) := (hFcross L K).1
    rw [h1, h2]
    exact openIntervalCrossIntegral_antisymm hab K L (F K) (F L) (hFtoFun K) (hFtoFun L)
  rw [(quadratic_directional_derivative convexBodyCombination
    (fun M ↦ convexArcArea M a b) B hbil hfB).2.1 K L, hsub]
  linarith

end MovingSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Optimality from the area upper bound

`AreaUpperBound` says that no moving sofa has larger area than Gerver's sofa. Since Gerver's sofa
is itself a moving sofa, the bound gives `sofaConstant = volume gerversSofa`.
-/

public section

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry unitInterval

/-- Every moving sofa has area at most that of Gerver's sofa. This is the upper bound proved in
Baek's paper; together with the fact that Gerver's sofa is a moving sofa it gives optimality. -/
@[expose]
def AreaUpperBound : Prop :=
  ∀ (s : Set ℝ²) (m : I → E(2)), IsMovingSofa s m → volume s ≤ volume gerversSofa

/-- The area upper bound implies that Gerver's sofa attains the sofa constant. -/
theorem optimality_of_areaUpperBound (h : AreaUpperBound) :
    sofaConstant = volume gerversSofa := by
  apply le_antisymm _ volume_gerversSofa_le_sofaConstant
  unfold sofaConstant
  refine iSup_le fun s ↦ iSup_le fun hs ↦ ?_
  obtain ⟨m, hm⟩ := hs
  exact h s m hm

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Motion.CanonicalBridge`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Canonical Bridge
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped unitInterval

private def normalizeMotion (m : I → Point ≃ᵃⁱ[ℝ] Point) (t : I) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (m 0).symm.trans (m t)

private theorem continuous_normalizeMotion (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) : Continuous (normalizeMotion m) := by
  rw [continuous_induced_rng]
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  apply (ContinuousAffineMap.continuous_comp_right
    (m 0).symm.toAffineIsometry.toContinuousAffineMap).comp hmc |>.congr
  intro t
  rfl

/-- A canonical hallway motion is also a paper motion of the same set. -/
theorem IsMovingSofa.isPaperMotion {s : Set Point} {m : I → Point ≃ᵃⁱ[ℝ] Point}
    (h : IsMovingSofa s m) : IsPaperMotion s m := by
  refine ⟨h.isConnected, h.isClosed, h.continuous, ⟨0, ?_⟩,
    exists_motion_rotation m h.continuous h.zero, ?_, h.subset_hallway, h.final⟩
  · intro p
    simp [h.zero]
  · simpa [h.zero] using h.initial

theorem canonical_paper_motion_bridge :
    (∀ s : Set Point, IsPaperMovingSofa s →
      ∃ (q : Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
        IsMovingSofa ((fun p ↦ p + q) '' s) m ∧
        volume ((fun p ↦ p + q) '' s) = volume s) ∧
    (∀ (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
      IsMovingSofa s m → IsPaperMovingSofa s) := by
  constructor
  · rintro s ⟨m, hsconn, hsclosed, hmcont, ⟨q, hq⟩, -, hini, hall, hfinal⟩
    refine ⟨q, normalizeMotion m, ?_, ?_⟩
    · refine
        { isConnected := hsconn.image _ (by fun_prop)
          isClosed := ?_
          continuous := continuous_normalizeMotion m hmcont
          zero := ?_
          initial := ?_
          subset_hallway := ?_
          final := ?_ }
      · change IsClosed ((AffineIsometryEquiv.vaddConst ℝ q) '' s)
        exact (AffineIsometryEquiv.vaddConst ℝ q).toHomeomorph.isClosedMap s hsclosed
      · ext x
        simp [normalizeMotion]
      · rintro _ ⟨x, hx, rfl⟩
        change x + q ∈ horizontalHallway
        rw [← hq x]
        exact hini ⟨x, hx, rfl⟩
      · intro t
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        change normalizeMotion m t (x + q) ∈ hallway
        rw [← hq x]
        exact hall t ⟨x, hx, by simp [normalizeMotion]⟩
      · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        change normalizeMotion m 1 (x + q) ∈ verticalHallway
        rw [← hq x]
        exact hfinal ⟨x, hx, by simp [normalizeMotion]⟩
    · have himage : (fun p ↦ p + q) '' s = (fun p ↦ p - q) ⁻¹' s := by
        ext p
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · intro hp
          exact ⟨p - q, hp, by simp⟩
      rw [himage, ← Measure.map_apply_of_aemeasurable (μ := volume)
        (f := fun p : Point ↦ p - q) (by fun_prop) hsclosed.measurableSet]
      have hmap : Measure.map (fun p : Point ↦ p - q) volume = volume := by
        simpa only [sub_eq_add_neg] using map_add_right_eq_self volume (-q)
      rw [hmap]
  · exact fun s m h ↦ ⟨m, h.isPaperMotion⟩

theorem canonical_motion_compactness (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (h : IsMovingSofa s m) :
    IsCompact s ∧ MeasurableSet s ∧ volume s < ⊤ := by
  have hc : IsCompact s := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨h.isClosed, h.isBounded⟩
  exact ⟨hc, hc.measurableSet, hc.measure_lt_top⟩

theorem real_area_le_iff_volume_le (s t : Set Point)
    (hfinS : volume s < ⊤) (hfinT : volume t < ⊤) :
    ClassicalResults.area s ≤ ClassicalResults.area t ↔ volume s ≤ volume t := by
  exact ENNReal.toReal_le_toReal hfinS.ne hfinT.ne

end MovingSofa

end

end

end

end

end

end
