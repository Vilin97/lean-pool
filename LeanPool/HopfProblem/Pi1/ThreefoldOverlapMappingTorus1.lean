/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods1
public import LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus

/-!
# Hopf problem: pi 1 · threefold overlap mapping torus 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private abbrev ThreefoldOverlapMappingTorus.Circle :=
  AddCircle (1 : ℝ)

/-- Radii whose `n`th powers lie below a prescribed bound. -/
public
abbrev ThreefoldOverlapMappingTorus.Radius (n : ℕ) (r : ℝ) :=
  { a : ℝ // 0 < a ∧ a < 1 ∧ a ^ n < r }

private abbrev ThreefoldOverlapMappingTorus.RootDisc (n : ℕ) (r : ℝ) :=
  { z : SpecialPeriods.Disc // (z : ℂ) ≠ 0 ∧ ‖(z : ℂ)‖ ^ n < r }

private def ThreefoldOverlapMappingTorus.phase (t : ThreefoldOverlapMappingTorus.Circle) :
    _root_.Circle :=
  AddCircle.toCircle t

private theorem ThreefoldOverlapMappingTorus.phase_continuous : Continuous phase :=
  AddCircle.continuous_toCircle

private theorem ThreefoldOverlapMappingTorus.phase_add (s t : ThreefoldOverlapMappingTorus.Circle) :
    phase (s + t) = phase s * phase t :=
  AddCircle.toCircle_add s t

private theorem ThreefoldOverlapMappingTorus.phase_real (t : ℝ) :
    (phase (t : ThreefoldOverlapMappingTorus.Circle) : ℂ) =
      CuspUniformization.exponential (t : ℂ) := by
  rw [phase, AddCircle.toCircle_apply_mk, _root_.Circle.coe_exp, CuspUniformization.exponential]
  congr 1
  push_cast
  ring

private def ThreefoldOverlapMappingTorus.root (n : ℕ) (r : ℝ) (a : Radius n r)
    (t : ThreefoldOverlapMappingTorus.Circle) : SpecialPeriods.Disc :=
  ⟨(a : ℝ) • (phase t : ℂ),
    by
    have hn : ‖(a : ℝ) • (phase t : ℂ)‖ < 1 := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos a.property.1, _root_.Circle.norm_coe,
        mul_one] using a.property.2.1
    simpa [SpecialPeriods.unitDisc] using hn⟩

@[simp]
private theorem ThreefoldOverlapMappingTorus.root_norm (n : ℕ) (r : ℝ) (a : Radius n r)
    (t : ThreefoldOverlapMappingTorus.Circle) : ‖(root n r a t : ℂ)‖ = (a : ℝ) := by
  simp only [root, norm_smul, Real.norm_eq_abs, abs_of_pos a.property.1, _root_.Circle.norm_coe,
    mul_one]

private theorem ThreefoldOverlapMappingTorus.root_ne_zero (n : ℕ) (r : ℝ) (a : Radius n r)
    (t : ThreefoldOverlapMappingTorus.Circle) : (root n r a t : ℂ) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [root_norm]
  exact a.property.1.ne'

private theorem ThreefoldOverlapMappingTorus.root_continuous (n : ℕ) (r : ℝ) :
    Continuous (fun p : Radius n r × ThreefoldOverlapMappingTorus.Circle => root n r p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (phase_continuous.comp continuous_snd))).subtype_mk
    _

private def ThreefoldOverlapMappingTorus.polarRoot (n : ℕ) (r : ℝ)
    (p : Radius n r × ThreefoldOverlapMappingTorus.Circle) : RootDisc n r :=
  ⟨root n r p.1 p.2, root_ne_zero n r p.1 p.2,
    by
    rw [root_norm]
    exact p.1.property.2.2⟩

private theorem ThreefoldOverlapMappingTorus.polarRoot_continuous (n : ℕ) (r : ℝ) :
    Continuous (polarRoot n r) :=
  (root_continuous n r).subtype_mk _

private def
    ThreefoldOverlapMappingTorus.rootRadius (n : ℕ) (r : ℝ) (z : RootDisc n r) : Radius n r :=
  ⟨‖((z : SpecialPeriods.Disc) : ℂ)‖, norm_pos_iff.mpr z.property.1,
    SpecialPeriods.disc_norm_lt_one z.val, z.property.2⟩

private theorem ThreefoldOverlapMappingTorus.rootRadius_continuous (n : ℕ) (r : ℝ) :
    Continuous (rootRadius n r) :=
  (continuous_subtype_val.comp continuous_subtype_val).norm.subtype_mk _

private def
    ThreefoldOverlapMappingTorus.unitPhase (n : ℕ) (r : ℝ) (z : RootDisc n r) : _root_.Circle :=
  ⟨‖((z : SpecialPeriods.Disc) : ℂ)‖⁻¹ • ((z : SpecialPeriods.Disc) : ℂ),
    by
    change
      ‖((z : SpecialPeriods.Disc) : ℂ)‖⁻¹ • ((z : SpecialPeriods.Disc) : ℂ) ∈
        Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr z.property.1))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr z.property.1)⟩

private theorem ThreefoldOverlapMappingTorus.unitPhase_continuous (n : ℕ) (r : ℝ) :
    Continuous (unitPhase n r) := by
  have hz : Continuous (fun z : RootDisc n r => ((z : SpecialPeriods.Disc) : ℂ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ((hz.norm.inv₀ fun z => norm_ne_zero_iff.mpr z.property.1).smul hz).subtype_mk _

private def ThreefoldOverlapMappingTorus.rootAngle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    ThreefoldOverlapMappingTorus.Circle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (unitPhase n r z)

private theorem ThreefoldOverlapMappingTorus.rootAngle_continuous (n : ℕ) (r : ℝ) :
    Continuous (rootAngle n r) :=
  (AddCircle.homeomorphCircle one_ne_zero).symm.continuous.comp (unitPhase_continuous n r)

@[simp]
private theorem ThreefoldOverlapMappingTorus.phase_rootAngle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    phase (rootAngle n r z) = unitPhase n r z := by
  rw [phase, ← AddCircle.homeomorphCircle_apply one_ne_zero]
  exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _

private theorem
    ThreefoldOverlapMappingTorus.polarRoot_radius_angle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    polarRoot n r (rootRadius n r z, rootAngle n r z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ‖((z : SpecialPeriods.Disc) : ℂ)‖ • (phase (rootAngle n r z) : ℂ) =
      ((z : SpecialPeriods.Disc) : ℂ)
  rw [phase_rootAngle]
  change
    ‖((z : SpecialPeriods.Disc) : ℂ)‖ •
        (‖((z : SpecialPeriods.Disc) : ℂ)‖⁻¹ • ((z : SpecialPeriods.Disc) : ℂ)) =
      _
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr z.property.1), one_smul]

@[simp]
private theorem ThreefoldOverlapMappingTorus.rootRadius_polarRoot (n : ℕ) (r : ℝ)
    (p : Radius n r × ThreefoldOverlapMappingTorus.Circle) :
    rootRadius n r (polarRoot n r p) = p.1 :=
  Subtype.ext (root_norm n r p.1 p.2)

@[simp]
private theorem ThreefoldOverlapMappingTorus.rootAngle_polarRoot (n : ℕ) (r : ℝ)
    (p : Radius n r × ThreefoldOverlapMappingTorus.Circle) :
    rootAngle n r (polarRoot n r p) = p.2 := by
  apply (AddCircle.injective_toCircle one_ne_zero)
  change phase (rootAngle n r (polarRoot n r p)) = phase p.2
  rw [phase_rootAngle]
  apply Subtype.ext
  change ‖(root n r p.1 p.2 : ℂ)‖⁻¹ • ((p.1 : ℝ) • (phase p.2 : ℂ)) = _
  rw [root_norm, smul_smul, inv_mul_cancel₀ p.1.property.1.ne', one_smul]

private def ThreefoldOverlapMappingTorus.polarHomeomorph (n : ℕ) (r : ℝ) :
    RootDisc n r ≃ₜ Radius n r × ThreefoldOverlapMappingTorus.Circle
    where
  toFun z := (rootRadius n r z, rootAngle n r z)
  invFun := polarRoot n r
  left_inv := polarRoot_radius_angle n r
  right_inv p := Prod.ext (rootRadius_polarRoot n r p) (rootAngle_polarRoot n r p)
  continuous_toFun := (rootRadius_continuous n r).prodMk (rootAngle_continuous n r)
  continuous_invFun := polarRoot_continuous n r

public
theorem ThreefoldOverlapMappingTorus.radius_nonempty (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    Nonempty (Radius n r) := by
  let a : ℝ := Min.min r 1 / 2
  have ha0 : 0 < a := half_pos (lt_min hr zero_lt_one)
  have ha1 : a < 1 := by
    have h := min_le_right r (1 : ℝ)
    dsimp only [a]
    linarith
  have har : a < r := by
    have h := min_le_left r (1 : ℝ)
    dsimp only [a] at ha0 ⊢
    linarith
  have hpow : a ^ n ≤ a := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha0.le ha1.le) ha0.le).trans_eq (one_mul a)
  exact ⟨⟨a, ha0, ha1, hpow.trans_lt har⟩⟩

private def ThreefoldOverlapMappingTorus.radiusSegment {n : ℕ} {r : ℝ} (a b : Radius n r)
    (t : unitInterval) : Radius n r :=
  ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ),
    by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have ha := a.property
    have hb := b.property
    have hmax : (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ≤ Max.max (a : ℝ) (b : ℝ) := by
      have h₁ := le_max_left (a : ℝ) (b : ℝ)
      have h₂ := le_max_right (a : ℝ) (b : ℝ)
      nlinarith
    have hpos : 0 < (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) := by
      by_cases ht : (t : ℝ) = 1
      · simp only [ht, sub_self, MulZeroClass.zero_mul, one_mul, zero_add]
        exact hb.1
      · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne ht1 ht
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht') ha.1) (mul_nonneg ht0 hb.1.le)
    refine ⟨hpos, hmax.trans_lt (max_lt ha.2.1 hb.2.1), ?_⟩
    apply (pow_le_pow_left₀ hpos.le hmax n).trans_lt
    rcases le_total (a : ℝ) (b : ℝ) with hab | hba
    · rw [max_eq_right hab]
      exact hb.2.2
    · rw [max_eq_left hba]
      exact ha.2.2⟩

@[simp]
private theorem ThreefoldOverlapMappingTorus.radiusSegment_zero {n : ℕ} {r : ℝ} (a b : Radius n r) :
    radiusSegment a b 0 = a := by
  apply Subtype.ext
  simp [radiusSegment]

@[simp]
private theorem ThreefoldOverlapMappingTorus.radiusSegment_one {n : ℕ} {r : ℝ} (a b : Radius n r) :
    radiusSegment a b 1 = b := by
  apply Subtype.ext
  simp [radiusSegment]

private theorem
    ThreefoldOverlapMappingTorus.radiusSegment_continuous {n : ℕ} {r : ℝ} (a : Radius n r) :
    Continuous (fun p : unitInterval × Radius n r => radiusSegment a p.2 p.1) := by
  exact
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
              continuous_const).add
          ((continuous_subtype_val.comp continuous_fst).mul
            (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _

private def ThreefoldOverlapMappingTorus.radiusProductHomotopyEquiv {n : ℕ} {r : ℝ} (a : Radius n r)
    (X : Type*) [TopologicalSpace X] : (Radius n r × X) ≃ₕ X
    where
  toFun := ContinuousMap.snd
  invFun := ⟨fun x => (a, x), continuous_const.prodMk continuous_id⟩
  left_inv :=
    ⟨{  toFun := fun p => (radiusSegment a p.2.1 p.1, p.2.2)
        continuous_toFun :=
          ((radiusSegment_continuous a).comp
                (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
            (continuous_snd.comp continuous_snd)
        map_zero_left := fun p => Prod.ext (radiusSegment_zero a p.1) rfl
        map_one_left := fun p => Prod.ext (radiusSegment_one a p.1) rfl }⟩
  right_inv := ContinuousMap.Homotopic.refl _

private theorem
    MappingTorus.mk_unitCylinder_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    MappingTorus.mk f '' ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ : Set X)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective f q
  refine ⟨deck f (-⌊t⌋) (t, x), ?_, mk_deck f (-⌊t⌋) (t, x)⟩
  change (0 ≤ t + ((-⌊t⌋ : ℤ) : ℝ) ∧ t + ((-⌊t⌋ : ℤ) : ℝ) ≤ 1) ∧ True
  push_cast
  exact ⟨⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩, trivial⟩

private instance MappingTorus.compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X ≃ₜ X) : CompactSpace (Torus f) where
  isCompact_univ := by
    rw [← mk_unitCylinder_surjective f]
    exact (CompactIccSpace.isCompact_Icc.prod isCompact_univ).image (mk_continuous f)

private def ThreefoldOverlapMappingTorus.Elliptic.homeomorphToPerm_mo1973_15505 :
    (RealTorus₄ ≃ₜ RealTorus₄) →* Equiv.Perm RealTorus₄
    where
  toFun := Homeomorph.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.affine_pow_order (j : Elliptic.Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : Elliptic.flatTorusAffine j v ^ j.order = 1 := by
  apply Homeomorph.ext
  intro x
  exact
    congrArg (fun e : Equiv.Perm RealTorus₄ => e x)
      ((homeomorphToPerm_mo1973_15505.map_pow (Elliptic.flatTorusAffine j v) j.order).trans
        (Elliptic.flatTorusPermutation_pow_order j v hv))

private theorem ThreefoldOverlapMappingTorus.Elliptic.affine_symm_pow_order (j : Elliptic.Kind)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : (Elliptic.flatTorusAffine j v).symm ^ j.order = 1 := by
  change (Elliptic.flatTorusAffine j v)⁻¹ ^ j.order = 1
  rw [inv_pow, affine_pow_order j v hv, inv_one]

end Mathoverflow1973

end
