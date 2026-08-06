/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

-- import Mathlib.Topology.CWComplex
import LeanPool.WhiteheadTheorem.Auxiliary
import LeanPool.WhiteheadTheorem.Shapes.Disk
import LeanPool.WhiteheadTheorem.Shapes.Cube
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube`.
-/


open scoped Topology TopCat ENNReal unitInterval

namespace TopCat

universe u v

variable (n : ℕ) (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]

/-- The unit disk in `ℝⁿ` based on the `Lᵖ` norm, where `p ≥ 1`. -/
def pDisk (n : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : PiLp p fun (_ : Fin n) ↦ ℝ) 1

/-- The boundary of the `pDisk`. -/
def pDiskBoundary (n : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : PiLp p fun (_ : Fin n) ↦ ℝ) 1

/-- The inclusion of the boundary of the `pDisk`. -/
def pDiskBoundaryIncl (n : ℕ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    pDiskBoundary.{u} n p ⟶ pDisk.{u} n p :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }


namespace pDisk

-- Note: need to declare the instances manually because `pDisk` and `TopCat` are not `abbrev`s.
instance instT1Space : T1Space (pDisk.{u} n p) :=
  letI : T1Space ↑(Metric.closedBall (0 : PiLp p fun (_ : Fin n) ↦ ℝ) 1) := inferInstance
  ULift.instT1Space
instance boundaryInstT1Space : T1Space (pDiskBoundary.{u} n p) :=
  letI : T1Space ↑(Metric.sphere (0 : PiLp p fun (_ : Fin n) ↦ ℝ) 1) := inferInstance
  ULift.instT1Space

noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (pDisk.{u} n p) :=
  letI : PseudoMetricSpace (ULift _) := inferInstance; ‹_›
noncomputable instance boundaryInstPseudoMetricSpace : PseudoMetricSpace (pDiskBoundary.{u} n p) :=
  letI : PseudoMetricSpace (ULift _) := inferInstance; ‹_›

lemma dist_eq (x y : pDisk.{u} n p) : dist x y = dist x.down.val y.down.val :=
  rfl

/-- Use `0` to denote the center of the disk. -/
instance : OfNat (pDisk.{u} n p) 0 where
  ofNat := ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩⟩

lemma zero_eq : 0 = (0 : pDisk.{u} n p).down.val :=
  rfl

lemma eq_zero_iff (x : pDisk.{u} n p) : x = 0 ↔ x.down.val = 0 :=
  ⟨fun h ↦ by subst h; rfl, fun h ↦ by obtain ⟨x, _⟩ := x; congr⟩

/-- Map `x` to `(‖x‖_p / ‖x‖_q) • x`.
Note that division by zero evaluates to zero (see `toQDisk_zero`). -/
noncomputable def toQDisk : pDisk.{u} n p → pDisk.{u} n q
  | ⟨x, hx⟩ => ⟨ (‖x‖ * ‖WithLp.toLp q (WithLp.ofLp x)‖⁻¹) • WithLp.toLp q (WithLp.ofLp x), by
      simp only [Metric.mem_closedBall, dist_zero_right] at *
      simp only [norm_smul, norm_mul, Real.norm_eq_abs, abs_norm, norm_inv]
      rw [mul_assoc]
      -- The first `‖x‖` is `@norm (PiLp p fun x => ℝ) SeminormedAddGroup.toNorm x : ℝ`
      -- The last `‖x‖` is `@norm (PiLp q fun x => ℝ) (WithLp.toLp q ..) : ℝ`
      -- Hence the goal is interpreted as `‖x‖_p * (‖x‖_q⁻¹ * ‖x‖_q) ≤ 1`
      exact (mul_le_of_le_one_right (norm_nonneg _) inv_mul_le_one).trans hx ⟩

/-- `pDisk.toQDisk` maps `0` to `0`.
Note that division by zero evaluates to zero, due to `GroupWithZero.inv_zero`. -/
lemma toQDisk_zero : pDisk.toQDisk.{u} n p q 0 = 0 := by
  unfold toQDisk
  simp only [norm_zero, zero_mul, zero_smul]
  congr

/-- The map `toQDisk` has a left inverse. -/
lemma toPDisk_comp_toQDisk (x : pDisk.{u} n p) :
    toQDisk n q p (toQDisk n p q x) = x := by
  by_cases hx0 : x = 0
  · subst x
    rw [toQDisk_zero, toQDisk_zero]
  unfold toQDisk
  split; next _ y hy hfx =>
    rcases x with ⟨x, _⟩
    replace hx0 : x ≠ 0 := fun h ↦ hx0 (by congr)
    have hx0' : WithLp.toLp q x.ofLp ≠ 0 := fun h ↦ hx0 (by
      simp_all)
    replace hfx := congrArg ULift.down hfx
    simp only [Subtype.mk.injEq] at hfx
    congr
    simp only [← hfx, WithLp.ofLp_smul, WithLp.toLp_smul]
    simp only [norm_smul, norm_mul, norm_norm, norm_inv, mul_inv_rev, inv_inv, smul_smul]
    rw [mul_assoc ‖x‖]
    conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0')
    simp only [mul_one, ← mul_assoc]
    simp_all

/-- The map `toQDisk` is continuous at `0`. -/
lemma continuousAt_toQDisk_zero :
    ContinuousAt (toQDisk.{u} n p q) (0 : pDisk.{u} n p) := by
  apply continuousAt_of_locally_lipschitz (_ : 0 < (1 : ℝ)) 1
  on_goal 2 => norm_num
  intro x h
  rw [toQDisk_zero]
  simp only [pDisk.dist_eq, ← zero_eq, dist_zero_right, one_mul] at h ⊢
  obtain ⟨x, hx⟩ := x
  simp only [toQDisk, norm_smul, norm_mul, norm_norm, norm_inv]
  by_cases hx0 : x = 0
  · subst x
    simp
  simp_all

/-- The map `toQDisk` is continuous on `{x | x ≠ 0}`. -/
lemma continuousOn_toQDisk_nonzero :
    ContinuousOn (toQDisk.{u} n p q) {x : pDisk.{u} n p | x ≠ 0} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  unfold Set.domRestrict toQDisk
  simp only [ne_eq, Set.coe_ofPred, Set.mem_ofPred_eq]
  refine continuous_uliftUp.comp <| Continuous.subtype_mk ?_ _
  have denominator_ne_zero :
      ∀ x : {x : pDisk.{u} n p // x ≠ 0}, ‖WithLp.toLp q x.val.down.val.ofLp‖ ≠ 0 := by
    intro ⟨x, hx0⟩
    rw [norm_ne_zero_iff]
    intro h
    change WithLp.toLp q x.down.val.ofLp = 0 at h
    have hxz : x.down.val = 0 := by simp_all
    rw [← eq_zero_iff] at hxz
    exact hx0 hxz
  fun_prop (disch := exact denominator_ne_zero _)

/-- The map `toQDisk` is continuous. -/
lemma continuous_toQDisk : Continuous (toQDisk.{u} n p q) :=
  continuous_iff_continuousAt.mpr fun x ↦ by
    by_cases hx0 : x = 0
    · subst x
      exact continuousAt_toQDisk_zero n p q
    exact (continuousOn_toQDisk_nonzero n p q).continuousAt
      (IsOpen.mem_nhds (IsClosed.not isClosed_singleton) hx0)

/-- `pDisk n p` (the unit disk in `ℝⁿ` based on the `Lᵖ` norm) is homeomorphic to
`pDisk n q` (the unit disk in `ℝⁿ` based on the `L^q` norm). -/
noncomputable def homeoQDisk : pDisk.{u} n p ≃ₜ pDisk.{u} n q where
  toFun := toQDisk n p q
  invFun := toQDisk n q p
  left_inv := toPDisk_comp_toQDisk n p q
  right_inv := toPDisk_comp_toQDisk n q p
  continuous_toFun := continuous_toQDisk n p q
  continuous_invFun := continuous_toQDisk n q p

/-- `isoQDisk` -/
noncomputable def isoQDisk : pDisk.{u} n p ≅ pDisk.{u} n q :=
  isoOfHomeo (homeoQDisk n p q)

end pDisk


namespace pDiskBoundary

instance instIsEmptyZero : IsEmpty (pDiskBoundary.{u} 0 p) where
  false := fun ⟨p, p1⟩ ↦ by
    have p0 : p = 0 := Subsingleton.elim _ _
    simp_all

lemma neq_zero (x : pDiskBoundary.{u} n p) : x.down.val ≠ 0 := fun xz ↦ by
  have x0 : ‖x.down.val‖ = 0 := by rw [xz]; apply norm_zero
  have x1 : ‖x.down.val‖ = 1 := by
    simpa only [mem_sphere_iff_norm, sub_zero] using x.down.property
  exact (by norm_num : (0 : ℝ) ≠ 1) (x0.symm.trans x1)

/-- `toQDiskBoundary` -/
noncomputable def toQDiskBoundary : pDiskBoundary.{u} n p → pDiskBoundary.{u} n q
  | ⟨x, hx⟩ => ⟨ (‖x‖ * ‖WithLp.toLp q (WithLp.ofLp x)‖⁻¹) • WithLp.toLp q (WithLp.ofLp x), by
      have xnz := neq_zero.{u} n p ⟨x, hx⟩
      simp only [mem_sphere_iff_norm, sub_zero] at hx ⊢
      rw [hx, one_mul, norm_smul, norm_inv, norm_norm]
      simp_all ⟩

/-- The map `boundaryToQDiskBoundary` has a left inverse. -/
lemma toPDiskBoundary_comp_toQDiskBoundary (x : pDiskBoundary.{u} n p) :
    toQDiskBoundary n q p (toQDiskBoundary.{u} n p q x) = x := by
  unfold toQDiskBoundary
  split; next _ y hy hfx =>
    rcases x with ⟨x, hx⟩
    have hx0 : x ≠ 0 := neq_zero.{u} n p ⟨x, hx⟩
    have hx0' : WithLp.toLp q x.ofLp ≠ 0 := fun h ↦ hx0 (by
      simp_all)
    replace hfx := congrArg ULift.down hfx
    simp only [Subtype.mk.injEq] at hfx
    congr
    simp only [← hfx, WithLp.ofLp_smul, WithLp.toLp_smul]
    simp only [norm_smul, norm_mul, norm_norm, norm_inv, mul_inv_rev, inv_inv, smul_smul]
    simp_all

/-- The map `boundaryToQDiskBoundary` is continuous. -/
lemma continuous_toQDiskBoundary : Continuous (toQDiskBoundary.{u} n p q) := by
  refine continuous_uliftUp.comp <| Continuous.subtype_mk ?_ _
  have denominator_ne_zero :
      ∀ x : pDiskBoundary.{u} n p, ‖WithLp.toLp q x.down.val.ofLp‖ ≠ 0 := by
    intro x
    rw [norm_ne_zero_iff]
    intro h
    change WithLp.toLp q x.down.val.ofLp = 0 at h
    have hxz : x.down.val = 0 := by simp_all
    exact (neq_zero n p x) hxz
  fun_prop (disch := exact denominator_ne_zero _)

/-- `pDiskBounday n p` is homeomorphic to `pDiskBoundary n q`. -/
noncomputable def homeoQDiskBoundary :
    pDiskBoundary.{u} n p ≃ₜ pDiskBoundary.{u} n q where
  toFun := toQDiskBoundary n p q
  invFun := toQDiskBoundary n q p
  left_inv := toPDiskBoundary_comp_toQDiskBoundary.{u} n p q
  right_inv := toPDiskBoundary_comp_toQDiskBoundary.{u} n q p
  continuous_toFun := continuous_toQDiskBoundary.{u} n p q
  continuous_invFun := continuous_toQDiskBoundary.{u} n q p

/-- `isoQDiskBoundary` -/
noncomputable def isoQDiskBoundary : pDiskBoundary.{u} n p ≅ pDiskBoundary.{u} n q :=
  isoOfHomeo (homeoQDiskBoundary n p q)

end pDiskBoundary


namespace pDiskPair

/-- Homeomorphism from the pair (pDisk n p, pDiskBoundary n p)
to the pair (pDisk n q, pDiskBoundary n q) -/
noncomputable def homeoQDiskPair :
    CategoryTheory.Arrow.mk (pDiskBoundaryIncl n p) ≅
    CategoryTheory.Arrow.mk (pDiskBoundaryIncl n q) :=
  CategoryTheory.Arrow.isoMk' _ _
    (pDiskBoundary.isoQDiskBoundary n p q) (pDisk.isoQDisk n p q) rfl

end pDiskPair

end TopCat


namespace TopCat

/-- The large cube $[-1, 1]^n$ is homeomorphic to `pDisk n ∞`
(the disk in `ℝⁿ` according to the `L∞` norm). -/
def largeCubeHomeoPDisk (n : ℕ) : (Fin n → Set.Icc (-1 : ℝ) (1 : ℝ)) ≃ₜ pDisk n ∞ where
  toFun := fun x ↦ ⟨⟨WithLp.toLp ∞ (fun i ↦ (x i : ℝ)), by
    simp only [Metric.mem_closedBall, PiLp.dist_eq_iSup]
    refine Real.iSup_le ?_ (by norm_num)
    intro i
    simp only [PiLp.zero_apply, dist_zero_right, Real.norm_eq_abs, abs_le]
    refine ⟨le_trans (by norm_num) (x i).prop.left, (x i).prop.right⟩ ⟩⟩
  invFun := fun ⟨⟨x, hx⟩⟩ i ↦ ⟨x.ofLp i, by
    simp only [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_ciSup, Real.norm_eq_abs] at hx
    have := Real.forall_le_of_iSup_le_of_finite_domain hx i
    exact ⟨neg_le_of_abs_le this, le_of_max_le_left this⟩ ⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    refine continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)
    refine (PiLp.continuous_toLp ∞ _).comp ?_
    exact continuous_pi fun i ↦ Continuous.subtype_val (continuous_apply i)
  continuous_invFun := continuous_pi fun i ↦
    ((continuous_apply i).comp <| (PiLp.continuous_ofLp ∞ _).comp <|
      continuous_uliftDown.subtype_val).subtype_mk _

/-- The large cube $[-1, 1]^n$ is homeomorphic to the cube $[0, 1]^n$. -/
noncomputable def largeCubeHomeoCube (n : ℕ) :
    (Fin n → Set.Icc (-1 : ℝ) (1 : ℝ)) ≃ₜ I^ Fin n :=
  Homeomorph.piCongrRight fun _ ↦ iccHomeoI _ _ (by norm_num)

/-- The n-disk `𝔻 n` is homeomorphic to the cube $[0, 1]^n$. -/
noncomputable def diskHomeoCube (n : ℕ) : TopCat.disk.{u} n ≃ₜ (I^ Fin n) :=
  (pDisk.homeoQDisk.{u} n 2 ∞).trans <|
    (largeCubeHomeoPDisk n).symm.trans (largeCubeHomeoCube n)

/-- `largeCubeBoundaryHomeoPDiskBoundary` -/
noncomputable def largeCubeBoundaryHomeoPDiskBoundary (n : ℕ) :
    { x : Fin n → Set.Icc (-1 : ℝ) (1 : ℝ) | ∃ i, x i = (-1 : ℝ) ∨ x i = (1 : ℝ) } ≃ₜ
      pDiskBoundary n ∞ where
  toFun := fun ⟨x, hx⟩ ↦ ⟨⟨WithLp.toLp ∞ (fun i ↦ (x i : ℝ)), by
    rw [Metric.mem_sphere, PiLp.dist_eq_iSup]
    apply le_antisymm
    · refine Real.iSup_le ?_ (by norm_num : (0 : ℝ) ≤ (1 : ℝ))
      simp only [PiLp.zero_apply, dist_zero_right, Real.norm_eq_abs]
      exact fun i ↦ abs_le.mpr (x i).property
    · apply Real.le_iSup_of_exists_ge_of_finite_domain
      obtain ⟨i, hi | hi⟩ := hx
      all_goals
        use i
        simp only [PiLp.zero_apply,
          dist_zero_right, Real.norm_eq_abs, hi]
        norm_num ⟩⟩
  invFun := fun ⟨⟨x, hx⟩⟩ ↦
    ⟨fun i ↦ ⟨x.ofLp i, by
      simp only [mem_sphere_iff_norm, sub_zero, PiLp.norm_eq_ciSup, Real.norm_eq_abs] at hx
      have := Real.forall_le_of_iSup_le_of_finite_domain (le_of_eq hx) i
      exact ⟨neg_le_of_abs_le this, le_of_max_le_left this⟩ ⟩,
    by
      simp only [Set.mem_ofPred_eq]
      obtain hn | hn := Nat.eq_zero_or_pos n
      · exfalso
        have h0 : pDiskBoundary.{0} 0 ∞ := by subst hn; exact ⟨x, hx⟩
        exact (pDiskBoundary.instIsEmptyZero ∞).false h0
      simp only [mem_sphere_iff_norm, sub_zero, PiLp.norm_eq_ciSup, Real.norm_eq_abs] at hx
      have : ∃ i, |x.ofLp i| ≥ 0 := by use ⟨0, hn⟩; simp only [ge_iff_le, abs_nonneg]
      have : ∃ i, |x.ofLp i| = 1 := Real.exists_eq_of_iSup_eq_of_finite_domain this hx
      obtain ⟨i, hi⟩ := this
      exact ⟨i, Or.symm (eq_or_eq_neg_of_abs_eq hi)⟩ ⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    refine continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)
    refine (PiLp.continuous_toLp ∞ _).comp ?_
    refine continuous_pi fun i ↦ Continuous.subtype_val ?_
    exact (continuous_apply i).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i ↦ Continuous.subtype_mk ?_ _
    exact (continuous_apply i).comp <| (PiLp.continuous_ofLp ∞ _).comp <|
      continuous_uliftDown.subtype_val

/-- `largeCubeBoundaryHomeoCubeBoundary` -/
noncomputable def largeCubeBoundaryHomeoCubeBoundary (n : ℕ) :
    { x : Fin n → Set.Icc (-1 : ℝ) (1 : ℝ) | ∃ i, x i = (-1 : ℝ) ∨ x i = (1 : ℝ) } ≃ₜ
      Cube.boundary (Fin n) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨fun i ↦ iccHomeoI (-1 : ℝ) (1 : ℝ) (by norm_num) (x i), by
    obtain ⟨i, hin | hip⟩ := hx
    · use i; left; apply Subtype.ext_iff.mpr; simp [hin]
    · use i; right; apply Subtype.ext_iff.mpr; simp [hip] ⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun i ↦ (iccHomeoI (-1 : ℝ) (1 : ℝ) (by norm_num)).symm (x i), by
    obtain ⟨i, hi0 | hi1⟩ := hx
    · use i; left; simp [hi0]
    · use i; right; simp [hi1] ⟩
  left_inv x := by
    simp only [Set.coe_ofPred, Set.mem_ofPred_eq, Homeomorph.symm_apply_apply, Subtype.coe_eta]
  right_inv x := by
    simp only [Homeomorph.apply_symm_apply, Subtype.coe_eta]
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    apply (Homeomorph.continuous _).comp
    exact (continuous_apply i).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    apply (Homeomorph.continuous_symm _).comp
    exact (continuous_apply i).comp continuous_subtype_val

/-- `diskBoundaryHomeoCubeBoundary` -/
noncomputable def diskBoundaryHomeoCubeBoundary (n : ℕ) :
    TopCat.diskBoundary.{u} n ≃ₜ Cube.boundary (Fin n) :=
  (pDiskBoundary.homeoQDiskBoundary.{u} n 2 ∞).trans <|
    (largeCubeBoundaryHomeoPDiskBoundary n).symm.trans (largeCubeBoundaryHomeoCubeBoundary n)

--------------------------------------------------------------------------------------

open CategoryTheory  -- for the notation `≫`

/-- `diskIsoCube` -/
noncomputable def diskIsoCube (n : ℕ) : disk n ≅ TopCat.of (I^ Fin n) :=
  isoOfHomeo (diskHomeoCube n)

/-- `diskBoundaryIsoCubeBoundary` -/
noncomputable def diskBoundaryIsoCubeBoundary (n : ℕ) :
    diskBoundary n ≅ TopCat.of <| Cube.boundary (Fin n) :=
  isoOfHomeo (diskBoundaryHomeoCubeBoundary n)

namespace diskPair

/-- `homeoCubePair` -/
noncomputable def homeoCubePair (n : ℕ) :
    CategoryTheory.Arrow.mk (diskBoundaryIncl n) ≅
    CategoryTheory.Arrow.mk (TopCat.ofHom (Cube.boundaryIncl n)) :=
  CategoryTheory.Arrow.isoMk' _ _
    (diskBoundaryIsoCubeBoundary n) (diskIsoCube n) rfl

lemma homeoCubePair_comm (n : ℕ) :
    (diskBoundaryIncl n) ≫ (homeoCubePair n).hom.right =
    (homeoCubePair n).hom.left ≫ TopCat.ofHom (Cube.boundaryIncl n) := by
  rfl

end diskPair

--------------------------------------------------------------------------------------

/-- `diskHomeoCubeULift` -/
noncomputable def diskHomeoCubeULift (n : ℕ) :
    disk.{u} n ≃ₜ cube.{u} n :=
  (diskHomeoCube n).trans Homeomorph.ulift.symm

/-- `diskIsoCubeULift` -/
noncomputable def diskIsoCubeULift (n : ℕ) : disk.{u} n ≅ cube.{u} n :=
  isoOfHomeo (diskHomeoCubeULift n)

/-- `diskBoundaryHomeoCubeBoundaryULift` -/
noncomputable def diskBoundaryHomeoCubeBoundaryULift (n : ℕ) :
    diskBoundary.{u} n ≃ₜ cubeBoundary.{u} n :=
  (TopCat.diskBoundaryHomeoCubeBoundary n).trans Homeomorph.ulift.symm

/-- `diskBoundaryIsoCubeBoundaryULift` -/
noncomputable def diskBoundaryIsoCubeBoundaryULift (n : ℕ) :
    diskBoundary.{u} n ≅ cubeBoundary.{u} n :=
  isoOfHomeo (diskBoundaryHomeoCubeBoundaryULift n)

namespace diskPair

/-- Homeomorphism from the pair (TopCat.disk.{u} n, TopCat.diskBoundary.{u} n)
to the pair (TopCat.cube.{u} n, TopCat.cubeBoundary.{u} n) -/
noncomputable def homeoCubePairULift (n : ℕ) :
    CategoryTheory.Arrow.mk (diskBoundaryIncl n) ≅
    CategoryTheory.Arrow.mk (cubeBoundaryIncl n) :=
  CategoryTheory.Arrow.isoMk' _ _
    (diskBoundaryIsoCubeBoundaryULift n) (diskIsoCubeULift n) rfl

lemma homeoCubePairULift_comm (n : ℕ) :
    (diskBoundaryIncl.{u} n) ≫ (homeoCubePairULift.{u} n).hom.right =
    (homeoCubePairULift.{u} n).hom.left ≫ (cubeBoundaryIncl.{u} n) := by
  rfl

end diskPair

end TopCat
