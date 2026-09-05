/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspCentralHomology2
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology2

/-!
# Hopf problem: homology theory · sphere homology 1

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

/-- The unit `n`-sphere in Euclidean `(n+1)`-space. -/
public
abbrev SphereHomology.UnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

private theorem SphereHomology.unitSphere_norm {n : ℕ} (x : UnitSphere n) : ‖x.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

private def SphereHomology.basePoint (n : ℕ) : UnitSphere n :=
  ⟨PiLp.single 2 (0 : Fin (n + 1)) (1 : ℝ), by simp⟩

private instance SphereHomology.unitSphere_nonempty (n : ℕ) : Nonempty (UnitSphere n) :=
  ⟨basePoint n⟩

private instance SphereHomology.unitSphere_compactSpace (n : ℕ) : CompactSpace (UnitSphere n) :=
  inferInstance

private def SphereHomology.Latitude.height (t : unitInterval) : ℝ :=
  2 * (t : ℝ) - 1

private def SphereHomology.Latitude.radius (t : unitInterval) : ℝ :=
  Real.sqrt (1 - height t ^ 2)

private theorem SphereHomology.Latitude.height_sq_le_one (t : unitInterval) : height t ^ 2 ≤ 1 := by
  have h0 := t.property.1
  have h1 := t.property.2
  dsimp [height]
  nlinarith

private theorem
    SphereHomology.Latitude.radius_sq (t : unitInterval) : radius t ^ 2 = 1 - height t ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr (height_sq_le_one t))

private theorem SphereHomology.Latitude.radius_nonneg (t : unitInterval) : 0 ≤ radius t :=
  Real.sqrt_nonneg _

@[simp]
private theorem SphereHomology.Latitude.height_zero : height 0 = -1 := by norm_num [height]

@[simp]
private theorem SphereHomology.Latitude.height_one : height 1 = 1 := by norm_num [height]

@[simp]
private theorem SphereHomology.Latitude.radius_zero : radius 0 = 0 := by simp [radius]

@[simp]
private theorem SphereHomology.Latitude.radius_one : radius 1 = 0 := by simp [radius]

private theorem SphereHomology.Latitude.height_injective : Function.Injective height := by
  intro t s h
  apply Subtype.ext
  dsimp [height] at h
  linarith

private theorem SphereHomology.Latitude.radius_pos_of_interior (t : unitInterval) (h0 : t ≠ 0)
    (h1 : t ≠ 1) : 0 < radius t := by
  have ht0 : 0 < (t : ℝ) :=
    lt_of_le_of_ne t.property.1
      (by
        intro h
        exact h0 (Subtype.ext h.symm))
  have ht1 : (t : ℝ) < 1 :=
    lt_of_le_of_ne t.property.2
      (by
        intro h
        exact h1 (Subtype.ext h))
  apply Real.sqrt_pos.mpr
  dsimp [height]
  nlinarith

@[continuity, fun_prop]
private theorem SphereHomology.Latitude.height_continuous : Continuous height := by
  unfold height
  fun_prop

@[continuity, fun_prop]
private theorem SphereHomology.Latitude.radius_continuous : Continuous radius := by
  unfold radius
  exact Real.continuous_sqrt.comp (continuous_const.sub (height_continuous.pow 2))

private def
    SphereHomology.Latitude.vector (n : ℕ) (t : unitInterval) (x : SphereHomology.UnitSphere n) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  WithLp.toLp 2 (Fin.cons (height t) (fun i => radius t * x.val i))

@[simp]
private theorem SphereHomology.Latitude.vector_zero (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) : vector n t x 0 = height t :=
  rfl

@[simp]
private theorem SphereHomology.Latitude.vector_succ (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) (i : Fin (n + 1)) :
    vector n t x i.succ = radius t * x.val i :=
  rfl

private theorem SphereHomology.Latitude.vector_norm_sq (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) : ‖vector n t x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [vector_zero, vector_succ, mul_pow]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq, SphereHomology.unitSphere_norm]
  rw [one_pow, mul_one, radius_sq]
  ring

private theorem SphereHomology.Latitude.vector_mem_sphere (n : ℕ) (t : unitInterval)
    (x : SphereHomology.UnitSphere n) :
    vector n t x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
  have hn := vector_norm_sq n t x
  have hnorm : ‖vector n t x‖ = 1 := by nlinarith [norm_nonneg (vector n t x)]
  simpa only [Metric.mem_sphere, dist_zero_right] using hnorm

private def
    SphereHomology.Latitude.point (n : ℕ) (t : unitInterval) (x : SphereHomology.UnitSphere n) :
    SphereHomology.UnitSphere (n + 1) :=
  ⟨vector n t x, vector_mem_sphere n t x⟩

@[continuity, fun_prop]
private theorem SphereHomology.Latitude.vector_continuous (n : ℕ) :
    Continuous (fun p : unitInterval × SphereHomology.UnitSphere n => vector n p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 2) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact height_continuous.comp continuous_fst
  · exact
      (radius_continuous.comp continuous_fst).mul
        ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) j).comp
          (continuous_subtype_val.comp continuous_snd))

@[continuity, fun_prop]
private theorem SphereHomology.Latitude.point_continuous (n : ℕ) :
    Continuous (fun p : unitInterval × SphereHomology.UnitSphere n => point n p.1 p.2) :=
  (vector_continuous n).subtype_mk _

private theorem SphereHomology.Latitude.point_zero_eq (n : ℕ) (x y : SphereHomology.UnitSphere n) :
    point n 0 x = point n 0 y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change radius 0 * x.val j = radius 0 * y.val j
    rw [radius_zero, MulZeroClass.zero_mul, MulZeroClass.zero_mul]

private theorem SphereHomology.Latitude.point_one_eq (n : ℕ) (x y : SphereHomology.UnitSphere n) :
    point n 1 x = point n 1 y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change radius 1 * x.val j = radius 1 * y.val j
    rw [radius_one, MulZeroClass.zero_mul, MulZeroClass.zero_mul]

private theorem SphereHomology.Latitude.point_eq_iff (n : ℕ) (t s : unitInterval)
    (x y : SphereHomology.UnitSphere n) :
    point n t x = point n s y ↔ t = s ∧ (t = 0 ∨ t = 1 ∨ x = y) := by
  constructor
  · intro h
    have hh := congrArg (fun p : SphereHomology.UnitSphere (n + 1) => p.val 0) h
    change height t = height s at hh
    have ht : t = s := height_injective hh
    subst s
    refine ⟨rfl, ?_⟩
    by_cases h0 : t = 0
    · exact Or.inl h0
    by_cases h1 : t = 1
    · exact Or.inr (Or.inl h1)
    refine Or.inr (Or.inr ?_)
    ext i
    have hi := congrArg (fun p : SphereHomology.UnitSphere (n + 1) => p.val i.succ) h
    change radius t * x.val i = radius t * y.val i at hi
    exact mul_left_cancel₀ (ne_of_gt (radius_pos_of_interior t h0 h1)) hi
  · rintro ⟨rfl, h0 | h1 | rfl⟩
    · subst t
      exact point_zero_eq n x y
    · subst t
      exact point_one_eq n x y
    · rfl

private def SphereHomology.Latitude.tail (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => y.val i.succ)

@[simp]
private theorem SphereHomology.Latitude.tail_apply (n : ℕ) (y : SphereHomology.UnitSphere (n + 1))
    (i : Fin (n + 1)) : tail n y i = y.val i.succ :=
  rfl

private theorem SphereHomology.Latitude.head_tail_norm_sq (n : ℕ)
    (y : SphereHomology.UnitSphere (n + 1)) : y.val 0 ^ 2 + ‖tail n y‖ ^ 2 = 1 := by
  have h : ‖y.val‖ ^ 2 = 1 := by rw [SphereHomology.unitSphere_norm, one_pow]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at h
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [tail_apply] using h

private theorem
    SphereHomology.Latitude.head_bounds (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    -1 ≤ y.val 0 ∧ y.val 0 ≤ 1 := by
  have h := head_tail_norm_sq n y
  constructor
  · nlinarith [sq_nonneg ‖tail n y‖, sq_nonneg (y.val 0 + 1)]
  · nlinarith [sq_nonneg ‖tail n y‖, sq_nonneg (y.val 0 - 1)]

private def SphereHomology.Latitude.parameter (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    unitInterval :=
  ⟨(y.val 0 + 1) / 2, by
    have h := head_bounds n y
    constructor <;> linarith [h.1, h.2]⟩

@[simp]
private theorem
    SphereHomology.Latitude.height_parameter (n : ℕ) (y : SphereHomology.UnitSphere (n + 1)) :
    height (parameter n y) = y.val 0 := by
  change 2 * ((y.val 0 + 1) / 2) - 1 = y.val 0
  ring

private theorem SphereHomology.Latitude.radius_parameter_eq_norm_tail (n : ℕ)
    (y : SphereHomology.UnitSphere (n + 1)) : radius (parameter n y) = ‖tail n y‖ := by
  apply (sq_eq_sq₀ (radius_nonneg _) (norm_nonneg _)).mp
  rw [radius_sq, height_parameter]
  linarith [head_tail_norm_sq n y]

private theorem SphereHomology.Latitude.point_surjective (n : ℕ) :
    Function.Surjective (fun p : unitInterval × SphereHomology.UnitSphere n => point n p.1 p.2) :=
  by
  intro y
  let t := parameter n y
  have hr := radius_parameter_eq_norm_tail n y
  by_cases hzero : radius t = 0
  · have ht : tail n y = 0 := norm_eq_zero.mp (hr.symm.trans hzero)
    refine ⟨(t, SphereHomology.basePoint n), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact height_parameter n y
    · change radius t * (SphereHomology.basePoint n).val j = y.val j.succ
      rw [hzero, MulZeroClass.zero_mul]
      have hj := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v j) ht
      change y.val j.succ = 0 at hj
      exact hj.symm
  · let v : EuclideanSpace ℝ (Fin (n + 1)) := (radius t)⁻¹ • tail n y
    have hv : ‖v‖ = 1 := by
      calc
        ‖v‖ = |(radius t)⁻¹| * ‖tail n y‖ := norm_smul _ _
        _ = (radius t)⁻¹ * radius t := by rw [abs_inv, abs_of_nonneg (radius_nonneg t), ← hr]
        _ = 1 := inv_mul_cancel₀ hzero
    let x : SphereHomology.UnitSphere n :=
      ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩
    refine ⟨(t, x), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact height_parameter n y
    · change radius t * ((radius t)⁻¹ * tail n y j) = y.val j.succ
      rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul, tail_apply]

private def SphereHomology.suspensionSphereMap (n : ℕ) :
    CuspCentralHomology.Suspension (UnitSphere n) → UnitSphere (n + 1) :=
  Quotient.lift (fun p => Latitude.point n p.1 p.2)
    (fun p q h => (Latitude.point_eq_iff n p.1 q.1 p.2 q.2).mpr h)

@[continuity, fun_prop]
private theorem SphereHomology.suspensionSphereMap_continuous (n : ℕ) :
    Continuous (suspensionSphereMap n) :=
  CuspCentralHomology.Suspension.isQuotientMap_mk.continuous_iff.mpr (Latitude.point_continuous n)

private theorem SphereHomology.suspensionSphereMap_injective (n : ℕ) :
    Function.Injective (suspensionSphereMap n) := by
  intro a b
  induction a using Quotient.inductionOn with
  | _ p =>
    induction b using Quotient.inductionOn with
    | _ q =>
      intro h
      exact Quotient.sound ((Latitude.point_eq_iff n p.1 q.1 p.2 q.2).mp h)

private theorem SphereHomology.suspensionSphereMap_surjective (n : ℕ) :
    Function.Surjective (suspensionSphereMap n) := by
  intro y
  obtain ⟨⟨t, x⟩, h⟩ := Latitude.point_surjective n y
  exact ⟨CuspCentralHomology.Suspension.mk t x, h⟩

private def SphereHomology.suspensionSphereHomeomorph (n : ℕ) :
    CuspCentralHomology.Suspension (UnitSphere n) ≃ₜ UnitSphere (n + 1) :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (suspensionSphereMap n)
      ⟨suspensionSphereMap_injective n, suspensionSphereMap_surjective n⟩)
    (suspensionSphereMap_continuous n)

@[simp]
private theorem SphereHomology.suspensionSphereHomeomorph_mk (n : ℕ) (t : unitInterval)
    (x : UnitSphere n) :
    suspensionSphereHomeomorph n (CuspCentralHomology.Suspension.mk t x) = Latitude.point n t x :=
  rfl

private instance SphereHomology.unitSphere_pathConnectedSpace (n : ℕ) :
    PathConnectedSpace (UnitSphere (n + 1)) :=
  (suspensionSphereHomeomorph n).surjective.pathConnectedSpace
    (suspensionSphereHomeomorph n).continuous

private def
    SphereHomology.suspensionHomologyHigherEquiv (X : Type) [TopologicalSpace X] [Nonempty X]
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspCentralHomology.Suspension X) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X (k + 1) :=
  (CuspCentralHomology.contractibleCoverHomologyHigherEquiv
        CuspCentralHomology.Suspension.northOpen CuspCentralHomology.Suspension.southOpen
        CuspCentralHomology.Suspension.northOpen_isOpen
        CuspCentralHomology.Suspension.southOpen_isOpen CuspCentralHomology.Suspension.open_cover
        k).trans
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
      CuspCentralHomology.Suspension.middleBandHomotopyEquiv (k + 1))

private def SphereHomology.unitSphereHomologySuspensionEquiv (n k : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (UnitSphere n) (k + 1) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (suspensionSphereHomeomorph n).symm
        (k + 2)).trans
    (suspensionHomologyHigherEquiv (UnitSphere n) k)

private def SphereHomology.euclideanPlaneComplexIsometry : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private theorem
    SphereHomology.euclideanPlaneComplexIsometry_mem_sphere (x : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) :
    euclideanPlaneComplexIsometry x ∈ Metric.sphere (0 : ℂ) r ↔
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r := by
  simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]

private def SphereHomology.sphereCircleHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ _root_.Circle :=
  euclideanPlaneComplexIsometry.toHomeomorph.subtype
    (fun x => (euclideanPlaneComplexIsometry_mem_sphere x 1).symm)

private def SphereHomology.sphereCircleHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology _root_.Circle n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv sphereCircleHomeomorph n

private theorem SingularMayerVietoris.ModuleHomology.cyclesMk_eq_moduleCatCyclesIso_inv
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hc : (K.d n j).hom c.1 = 0) :
    K.cyclesMk c.1 j hj hc = ((K.sc n).moduleCatCyclesIso.inv).hom c := by
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have h₁ : (K.iCycles n).hom (K.cyclesMk c.1 j hj hc) = c.1 := K.i_cyclesMk c.1 j hj hc
  have h₂ := congrArg (fun f => f.hom c) ((K.sc n).moduleCatCyclesIso_inv_iCycles)
  exact h₁.trans h₂.symm

private theorem SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle_of_next
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hc : (K.d n j).hom c.1 = 0) :
    cycleClass K n c = SingularMayerVietoris.homologyClassOfCycle K c.1 j hj hc := by
  rw [SingularMayerVietoris.homologyClassOfCycle, cyclesMk_eq_moduleCatCyclesIso_inv]
  exact (congrArg (fun f => f.hom c) ((K.sc n).moduleCatCyclesIso_inv_π)).symm

private theorem SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    cycleClass K n c =
      SingularMayerVietoris.homologyClassOfCycle K c.1 (n - 1) (next_nat n)
        (cycle_condition K n c) :=
  cycleClass_eq_homologyClassOfCycle_of_next K n c (n - 1) (next_nat n) (cycle_condition K n c)

private def SphereHomology.unitCircleAddCircleHomeomorph :
    _root_.Circle ≃ₜ PeriodTorusHigherHomology.CircleTopology.Circle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

private def SphereHomology.unitCircleHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology _root_.Circle n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology PeriodTorusHigherHomology.CircleTopology.Circle n :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv unitCircleAddCircleHomeomorph n


end Mathoverflow1973

end
