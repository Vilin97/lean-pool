/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.TwoAffineCharts
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Foundations.TwoAffineCharts

/-!
# Hopf problem: recognition · smale 4

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

private theorem
    MorseCancel.contDiff_cubicAxisParameter (a : ℝ) : ContDiff ℝ ∞ (cubicAxisParameter a) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    have hh : ContDiff ℝ ∞ (fun t => Real.sinh t / Real.cosh t) :=
      Real.contDiff_sinh.div Real.contDiff_cosh (fun t => (Real.cosh_pos t).ne')
    have he : (fun t => Real.sinh t / Real.cosh t) = Real.tanh :=
      funext (fun t => (Real.tanh_eq_sinh_div_cosh t).symm)
    rw [he] at hh
    exact hh
  change ContDiff ℝ ∞ (fun t => a * Real.tanh (a * t))
  exact contDiff_const.mul (ht.comp (contDiff_const.mul contDiff_id))

private def MorseCancel.cubicAxisClock (a s : ℝ) : ℝ :=
  Real.artanh (s / a) / a

private theorem MorseCancel.cubicAxisClock_parameter {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisClock a (cubicAxisParameter a t) = t := by
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel_left₀ _ ha.ne', Real.artanh_tanh]

private theorem
    MorseCancel.cubicAxisParameter_clock {a s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Ioo (-a) a) :
    cubicAxisParameter a (cubicAxisClock a s) = s := by
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

private theorem MorseCancel.contDiffOn_cubicAxisClock {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (cubicAxisClock a) (Set.Ioo (-a) a) := by
  intro s hs
  have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  exact
    (((contDiffAt_artanh hs').comp s (contDiffAt_id.div_const a)).div_const a).contDiffWithinAt

private def MorseCancel.cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (p : (Fin m → ℝ) × ℝ) :
    Model m :=
  (cubicAxisParameter a p.2, fun i => Real.exp (-σ i * p.2) * p.1 i)

private def MorseCancel.cubicFlowCylinderInverse {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (p : Model m) :
    (Fin m → ℝ) × ℝ :=
  (fun i => Real.exp (σ i * cubicAxisClock a p.1) * p.2 i, cubicAxisClock a p.1)

private theorem MorseCancel.cubicFlowCylinder_left_inv {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (p : (Fin m → ℝ) × ℝ) : cubicFlowCylinderInverse σ a (cubicFlowCylinder σ a p) = p := by
  apply Prod.ext
  · funext i
    change
      Real.exp (σ i * cubicAxisClock a (cubicAxisParameter a p.2)) *
          (Real.exp (-σ i * p.2) * p.1 i) =
        p.1 i
    rw [cubicAxisClock_parameter ha, ← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel,
      Real.exp_zero, one_mul]
  · exact cubicAxisClock_parameter ha p.2

private theorem MorseCancel.cubicFlowCylinder_right_inv {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {p : Model m} (hp : p.1 ∈ Set.Ioo (-a) a) :
    cubicFlowCylinder σ a (cubicFlowCylinderInverse σ a p) = p := by
  apply Prod.ext
  · exact cubicAxisParameter_clock ha hp
  · funext i
    change
      Real.exp (-σ i * cubicAxisClock a p.1) * (Real.exp (σ i * cubicAxisClock a p.1) * p.2 i) =
        p.2 i
    rw [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]

private theorem MorseCancel.contDiff_cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) :
    ContDiff ℝ ∞ (cubicFlowCylinder σ a) := by
  apply ((contDiff_cubicAxisParameter a).comp contDiff_snd).prodMk
  apply contDiff_pi.mpr
  intro i
  fun_prop

private theorem MorseCancel.contDiffOn_cubicFlowCylinderInverse {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) : ContDiffOn ℝ ∞ (cubicFlowCylinderInverse σ a) (Set.Ioo (-a) a ×ˢ Set.univ) := by
  have ht :
    ContDiffOn ℝ ∞ (fun p : Model m => cubicAxisClock a p.1) (Set.Ioo (-a) a ×ˢ Set.univ) :=
    (contDiffOn_cubicAxisClock ha).comp contDiffOn_fst (fun _ hp => hp.1)
  apply ContDiffOn.prodMk ?_ ht
  apply contDiffOn_pi.mpr
  intro i
  exact
    (Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul ht)).mul
      (((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn)

private def MorseCancel.cubicFlowCylinderChart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a) :
    PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, Model m) ((Fin m → ℝ) × ℝ) (Model m) ∞
    where
  toFun := cubicFlowCylinder σ a
  invFun := cubicFlowCylinderInverse σ a
  source := Set.univ
  target := Set.Ioo (-a) a ×ˢ Set.univ
  map_source' p _ := ⟨cubicAxisParameter_mem ha p.2, Set.mem_univ _⟩
  map_target' _ _ := Set.mem_univ _
  left_inv' p _ := cubicFlowCylinder_left_inv σ ha p
  right_inv' _ hp := cubicFlowCylinder_right_inv σ ha hp.1
  open_source := isOpen_univ
  open_target := isOpen_Ioo.prod isOpen_univ
  contMDiffOn_toFun := (contDiff_cubicFlowCylinder σ a).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiffOn_cubicFlowCylinderInverse σ ha).contMDiffOn

private theorem
    MorseCancel.hasDerivAt_cubicFlowCylinder {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ)
    (t : ℝ) :
    HasDerivAt (fun s => cubicFlowCylinder σ a (z, s))
      (cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t))) t := by
  have hz :
    HasDerivAt (fun s => fun i => Real.exp (-σ i * s) * z i)
      (fun i => -σ i * (Real.exp (-σ i * t) * z i)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hd :=
      ((Real.hasDerivAt_exp (-σ i * t)).comp t ((hasDerivAt_id t).const_mul (-σ i))).mul_const
        (z i)
    convert! hd using 1
    first
    | rfl
    | ring
  have hd := (hasDerivAt_cubicAxisParameter a t).prodMk hz
  have he :
    cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a (z, t)) =
      (a ^ 2 - cubicAxisParameter a t ^ 2, fun i => -σ i * (Real.exp (-σ i * t) * z i)) := by
    apply Prod.ext
    · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
      ring
    · rfl
  rw [he]
  exact hd

private theorem MorseCancel.cubicFlowCylinder_axis {m : ℕ} (σ : Fin m → ℝ) (a t : ℝ) :
    cubicFlowCylinder σ a (0, t) = cubicModelOrbit a t := by
  simp only [cubicFlowCylinder, cubicModelOrbit, Pi.zero_apply, MulZeroClass.mul_zero]
  rfl

private theorem
    MorseCancel.cubicFlowCylinder_zero_time {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ) :
    cubicFlowCylinder σ a (z, 0) = (0, z) := by
  simp only [cubicFlowCylinder, cubicAxisParameter, MulZeroClass.mul_zero, Real.tanh_zero,
    Real.exp_zero, one_mul]

private theorem MorseCancel.monotone_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    Monotone (cubicAxisParameter a) := by
  intro s t hst
  exact
    mul_le_mul_of_nonneg_left (strictMono_tanh.monotone (mul_le_mul_of_nonneg_left hst ha.le))
      ha.le

private theorem MorseCancel.cubicFlowCylinder_transverse_norm_le_max {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    (z : Fin m → ℝ) {s t u : ℝ} (ht : t ∈ Set.Icc s u) :
    ‖(cubicFlowCylinder σ a (z, t)).2‖ ≤
      Max.max ‖(cubicFlowCylinder σ a (z, s)).2‖ ‖(cubicFlowCylinder σ a (z, u)).2‖ := by
  let Z (r : ℝ) : Fin m → ℝ := (cubicFlowCylinder σ a (z, r)).2
  have hcoord (r : ℝ) (i : Fin m) : ‖Z r i‖ = Real.exp (-σ i * r) * ‖z i‖ := by
    change ‖Real.exp (-σ i * r) * z i‖ = _
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg (Z s)))).mpr
  intro i
  change ‖Z t i‖ ≤ Max.max ‖Z s‖ ‖Z u‖
  by_cases hi : 0 ≤ σ i
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * s) * ‖z i‖ :=
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hi)))
          (norm_nonneg _))
      _ = ‖Z s i‖ := (hcoord s i).symm
      _ ≤ ‖Z s‖ := (norm_le_pi_norm (Z s) i)
      _ ≤ Max.max ‖Z s‖ ‖Z u‖ := le_max_left _ _
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * u) * ‖z i‖ :=
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left ht.2 (neg_nonneg.mpr (le_of_not_ge hi))))
          (norm_nonneg _))
      _ = ‖Z u i‖ := (hcoord u i).symm
      _ ≤ ‖Z u‖ := (norm_le_pi_norm (Z u) i)
      _ ≤ Max.max ‖Z s‖ ‖Z u‖ := le_max_right _ _

private theorem
    MorseCancel.cubicFlowCylinder_stays_axis_ball {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {s t u c r : ℝ} (ht : t ∈ Set.Icc s u)
    (hs : cubicFlowCylinder σ a (z, s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hu : cubicFlowCylinder σ a (z, u) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hs' : |cubicAxisParameter a s - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, s)).2‖ ≤ r := by
    simpa only [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hs
  have hu' : |cubicAxisParameter a u - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, u)).2‖ ≤ r := by
    simpa only [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hu
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right]
  constructor
  · change |cubicAxisParameter a t - c| ≤ r
    apply abs_le.mpr
    have hst := monotone_cubicAxisParameter ha ht.1
    have htu := monotone_cubicAxisParameter ha ht.2
    constructor <;> linarith [(abs_le.mp hs'.1).1, (abs_le.mp hu'.1).2]
  · exact (cubicFlowCylinder_transverse_norm_le_max σ a z ht).trans (max_le hs'.2 hu'.2)

private def Smale.FiberwiseDiffeomorph.retainParameter {X P : Type*} (F : X × P → X) (p : X × P) :
    X × P :=
  (F p, p.2)

private theorem Smale.FiberwiseDiffeomorph.contMDiff_retainParameter {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {F : X × P → X} (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) :
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ (retainParameter F) :=
  hF.prodMk contMDiff_snd

private theorem Smale.FiberwiseDiffeomorph.bijective_retainParameter {X P : Type*} {F : X × P → X}
    (hF : ∀ s, Function.Bijective (fun x => F (x, s))) : Function.Bijective (retainParameter F) :=
  by
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩ heq
    have hst : s = t := congrArg Prod.snd heq
    subst t
    exact Prod.ext ((hF s).1 (congrArg Prod.fst heq)) rfl
  · rintro ⟨y, s⟩
    obtain ⟨x, hx⟩ := (hF s).2 y
    exact ⟨(x, s), Prod.ext hx rfl⟩

private theorem Smale.FiberwiseDiffeomorph.mfderiv_retainParameter_apply {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {F : X × P → X} (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F) (p : X × P) (v : D × P) :
    mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p v =
      (mfderiv I I (fun x => F (x, p.2)) p.1 v.1 +
          mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2 v.2,
        v.2) := by
  change mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (fun z => (F z, z.2)) p v = _
  rw [mfderiv_prodMk (hF.mdifferentiable (by simp) p) mdifferentiableAt_snd, mfderiv_snd]
  change ((mfderiv (I.prod 𝓘(ℝ, P)) I F p) v, v.2) = _
  exact Prod.ext (mfderiv_prod_eq_add_apply (v := v) (hF.mdifferentiable (by simp) p)) rfl

private theorem Smale.FiberwiseDiffeomorph.isInvertible_mfderiv_retainParameter {D H X P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ D] [FiniteDimensional ℝ P] {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s)) (p : X × P) :
    (mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p).IsInvertible := by
  let A : D →L[ℝ] D := mfderiv I I (fun x => F (x, p.2)) p.1
  let B : P →L[ℝ] D := mfderiv 𝓘(ℝ, P) I (fun s => F (p.1, s)) p.2
  have hA : Function.Bijective A := by
    obtain ⟨d, hd⟩ := hslice p.2
    have heq : (fun x => F (x, p.2)) = d := funext (fun x => (hd x).symm)
    change Function.Bijective (mfderiv I I (fun x => F (x, p.2)) p.1)
    rw [heq]
    exact (d.mfderivToContinuousLinearEquiv (by simp) p.1).bijective
  let L : (D × P) →L[ℝ] (D × P) := mfderiv (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (retainParameter F) p
  have hL (v : D × P) : L v = (A v.1 + B v.2, v.2) := mfderiv_retainParameter_apply hF p v
  have hbij : Function.Bijective L := by
    constructor
    · intro u v huv
      have hs : u.2 = v.2 := by simpa only [hL] using congrArg Prod.snd huv
      have hx : A u.1 + B u.2 = A v.1 + B v.2 := by simpa only [hL] using congrArg Prod.fst huv
      rw [hs] at hx
      exact Prod.ext (hA.1 (add_right_cancel hx)) hs
    · intro v
      obtain ⟨x, hx⟩ := hA.2 (v.1 - B v.2)
      refine ⟨(x, v.2), ?_⟩
      rw [hL, hx, sub_add_cancel]
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

private def Smale.FiberwiseDiffeomorph.diffeomorph {D H X P : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace H]
    {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ P] [I.Boundaryless] [IsManifold I ∞ X] {F : X × P → X}
    (hF : ContMDiff (I.prod 𝓘(ℝ, P)) I ∞ F)
    (hslice : ∀ s, ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F (x, s)) :
    Diffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) (X × P) (X × P) ∞ := by
  have hlocal : IsLocalDiffeomorph (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞ (retainParameter F) := by
    intro p
    exact
      Smale.isLocalDiffeomorphAt_boundaryless isOpen_univ (Set.mem_univ p)
        (contMDiff_retainParameter hF).contMDiffOn
        (isInvertible_mfderiv_retainParameter hF hslice p)
  apply hlocal.diffeomorphOfBijective
  apply bijective_retainParameter
  intro s
  obtain ⟨d, hd⟩ := hslice s
  have heq : (fun x => F (x, s)) = d := funext (fun x => (hd x).symm)
  rw [heq]
  exact d.bijective

private def Smale.PartialChart.vectorProduct (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Diffeomorph 𝓘(ℝ, E × F) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (E × F) (E × F) ∞
    where
  toEquiv := Equiv.refl (E × F)
  contMDiff_toFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  contMDiff_invFun := contMDiff_fst.prodMk_space contMDiff_snd

private def
    Smale.PartialChart.prod {E₁ E₂ F₁ F₂ H₁ H₂ G₁ G₂ X₁ X₂ Y₁ Y₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace H₁]
    [TopologicalSpace H₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {J₁ : ModelWithCorners ℝ F₁ G₁} {J₂ : ModelWithCorners ℝ F₂ G₂} [TopologicalSpace X₁]
    [ChartedSpace H₁ X₁] [TopologicalSpace X₂] [ChartedSpace H₂ X₂] [TopologicalSpace Y₁]
    [ChartedSpace G₁ Y₁] [TopologicalSpace Y₂] [ChartedSpace G₂ Y₂]
    (Φ : PartialDiffeomorph I₁ J₁ X₁ Y₁ ∞) (Ψ : PartialDiffeomorph I₂ J₂ X₂ Y₂ ∞) :
    PartialDiffeomorph (I₁.prod I₂) (J₁.prod J₂) (X₁ × X₂) (Y₁ × Y₂) ∞
    where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.prodMap Ψ.contMDiffOn_toFun
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.prodMap Ψ.contMDiffOn_invFun

private theorem Degree.FlowSuspension.exists_isotopy_suspension_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A : ℝ × E → E}
    (hA : ContDiff ℝ ∞ A)
    (hslice : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = A (t, x)) :
    ∃ Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞, ∀ p, Ψ p = (A (p.2, p.1), p.2) :=
  by
  have hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun p : E × ℝ => A (p.2, p.1)) :=
    hA.contMDiff.comp (contMDiff_snd.prodMk_space contMDiff_fst)
  let D := Smale.FiberwiseDiffeomorph.diffeomorph hF hslice
  let V := Smale.PartialChart.vectorProduct E ℝ
  exact ⟨(V.trans D).trans V.symm, fun p => rfl⟩

private def
    Degree.FlowSuspension.suspensionFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) : Flow ℝ (E × ℝ)
    where
  toFun t p := Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)
  cont' := by
    apply Ψ.continuous.comp
    exact
      (Ψ.symm.continuous.comp continuous_snd).fst.prodMk
        ((Ψ.symm.continuous.comp continuous_snd).snd.add continuous_fst)
  map_zero' p := by simp only [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  map_add' s t
    p := by
    simp only [Ψ.symm_apply_apply]
    congr 1
    apply Prod.ext
    · rfl
    · ring

private theorem Degree.FlowSuspension.suspensionFlow_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (t : ℝ)
    (p : E × ℝ) : suspensionFlow Ψ t (Ψ p) = Ψ (p.1, p.2 + t) := by
  change Ψ ((Ψ.symm (Ψ p)).1, (Ψ.symm (Ψ p)).2 + t) = _
  rw [Ψ.symm_apply_apply]

private theorem Degree.FlowSuspension.suspensionFlow_height {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (t : ℝ) (p : E × ℝ) : (suspensionFlow Ψ t p).2 = p.2 + t := by
  have hinv : (Ψ.symm p).2 = p.2 := by
    have hh := hheight (Ψ.symm p)
    rw [Ψ.apply_symm_apply] at hh
    exact hh.symm
  change (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)).2 = _
  rw [hheight, hinv]

private theorem Degree.FlowSuspension.suspensionFlow_endpoint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : ℝ × E → E} (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (hA0 : ∀ x, A (0, x) = x) (x : E) :
    suspensionFlow Ψ 1 (x, 0) = (A (1, x), 1) := by
  have hstart : Ψ (x, (0 : ℝ)) = (x, 0) := by rw [hΨ, hA0]
  rw [← hstart, suspensionFlow_chart, zero_add, hΨ]

private def
    Degree.FlowSuspension.suspensionField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ) : E × ℝ :=
  fderiv ℝ Ψ (Ψ.symm p) (0, 1)

private theorem Degree.FlowSuspension.contDiff_suspensionField {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) :
    ContDiff ℝ ∞ (suspensionField Ψ) := by
  have hΨ : ContDiff ℝ ∞ (Ψ : (E × ℝ) → E × ℝ) := Ψ.contMDiff.contDiff
  have hΨinv : ContDiff ℝ ∞ (Ψ.symm : (E × ℝ) → E × ℝ) := Ψ.symm.contMDiff.contDiff
  exact ((hΨ.fderiv_right (by simp)).comp hΨinv).clm_apply contDiff_const

private theorem Degree.FlowSuspension.hasDerivAt_suspensionFlow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ)
    (t : ℝ) :
    HasDerivAt (fun s => suspensionFlow Ψ s p) (suspensionField Ψ (suspensionFlow Ψ t p)) t := by
  have hb : HasDerivAt (fun s : ℝ => ((Ψ.symm p).1, (Ψ.symm p).2 + s)) (0, 1) t :=
    (hasDerivAt_const t (Ψ.symm p).1).prodMk ((hasDerivAt_id t).const_add (Ψ.symm p).2)
  have hd :=
    (Ψ.contMDiff.contDiff.differentiable (by simp)
          ((Ψ.symm p).1, (Ψ.symm p).2 + t)).hasFDerivAt.comp_hasDerivAt
      t hb
  change
    HasDerivAt (fun s => Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + s))
      (fderiv ℝ Ψ (Ψ.symm (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t))) (0, 1)) t
  rw [Ψ.symm_apply_apply]
  exact hd

private theorem
    Degree.FlowSuspension.hasDerivAt_suspensionFlow_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ) :
    HasDerivAt (fun s => suspensionFlow Ψ s p) (suspensionField Ψ p) 0 := by
  simpa only [(suspensionFlow Ψ).map_zero_apply] using hasDerivAt_suspensionFlow Ψ p 0

private theorem Degree.FlowSuspension.suspensionField_height {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : E × ℝ) : (suspensionField Ψ p).2 = 1 := by
  have hd : HasDerivAt (fun t => (suspensionFlow Ψ t p).2) (suspensionField Ψ p).2 0 :=
    (hasDerivAt_suspensionFlow_zero Ψ p).snd
  have heq : (fun t => (suspensionFlow Ψ t p).2) = fun t => p.2 + t :=
    funext (fun t => suspensionFlow_height Ψ hheight t p)
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_id (0 : ℝ)).const_add p.2)

private theorem Degree.FlowSuspension.suspensionField_eq_vertical_of_stationary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (p : E × ℝ)
    (hstationary : ∀ᶠ s in 𝓝 p.2, ∀ x, A (s, x) = A (p.2, x)) : suspensionField Ψ p = (0, 1) := by
  let q := Ψ.symm p
  have hq : Ψ q = p := Ψ.apply_symm_apply p
  have hqheight : q.2 = p.2 := by
    have hh := congrArg Prod.snd hq
    rw [hΨ] at hh
    exact hh
  have hqfirst : A (p.2, q.1) = p.1 := by
    have hh := congrArg Prod.fst hq
    rw [hΨ] at hh
    change A (q.2, q.1) = p.1 at hh
    rwa [hqheight] at hh
  have ht : Filter.Tendsto (fun t : ℝ => p.2 + t) (𝓝 0) (𝓝 p.2) := by
    have hc : Continuous (fun t : ℝ => p.2 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have heq : (fun t => suspensionFlow Ψ t p) =ᶠ[𝓝 0] (fun t => (p.1, p.2 + t)) := by
    filter_upwards [ht.eventually hstationary] with t hts
    change Ψ (q.1, q.2 + t) = (p.1, p.2 + t)
    rw [hΨ, hqheight, hts q.1, hqfirst]
  have hv : HasDerivAt (fun t : ℝ => (p.1, p.2 + t)) (0, 1) 0 :=
    (hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2)
  exact ((hasDerivAt_suspensionFlow_zero Ψ p).congr_of_eventuallyEq heq.symm).unique hv

private theorem Degree.FlowSuspension.suspensionFlow_vertical_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    {p : E × ℝ} (hp : p.1 ∉ K) (t : ℝ) : suspensionFlow Ψ t p = (p.1, p.2 + t) := by
  have hΨp : Ψ p = p := by rw [hΨ, hfix _ _ hp]
  have hinv : Ψ.symm p = p := by
    have hh := Ψ.symm_apply_apply p
    rwa [hΨp] at hh
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = _
  rw [hinv, hΨ, hfix _ _ hp]

private theorem Degree.FlowSuspension.suspensionField_eq_vertical_off_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    {p : E × ℝ} (hp : p.1 ∉ K) : suspensionField Ψ p = (0, 1) := by
  have heq : (fun t => suspensionFlow Ψ t p) = fun t => (p.1, p.2 + t) :=
    funext (fun t => suspensionFlow_vertical_off_support Ψ hΨ hfix hp t)
  have hd := hasDerivAt_suspensionFlow_zero Ψ p
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2))

private theorem Degree.FlowSuspension.hasCompactSupport_suspensionField_sub_vertical {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hK : IsCompact K)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) {a b : ℝ}
    (hstationary : ∀ s ∉ Set.Icc a b, ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x)) :
    HasCompactSupport (fun p => suspensionField Ψ p - (0, 1)) := by
  apply
    HasCompactSupport.intro (hK.prod (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc a b)))
  intro p hp
  have hv : suspensionField Ψ p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · have ht : p.2 ∉ Set.Icc a b := fun h => hp ⟨hx, h⟩
      exact suspensionField_eq_vertical_of_stationary Ψ hΨ p (hstationary _ ht)
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  rw [hv, sub_self]

private theorem Smale.SupportedDiffeomorph.contMDiff_extendFamily {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {A : ℝ × X → X} (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    (hsource : ∀ t, Set.MapsTo (fun x => A (t, x)) Φ.source Φ.source) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun p : ℝ × Y => extendMap Φ (fun x => A (p.1, x)) p.2) := by
  intro p
  by_cases hp : p.2 ∈ Φ.target
  · have hback :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
        (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource p.1 (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

private theorem Smale.SupportedDiffeomorph.contMDiffAt_extendFamily {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : P × X → X} (hA : ContMDiff (𝓘(ℝ, P).prod I) I ∞ A) {K : Set X} (hK : IsCompact K)
    (hKΦ : K ⊆ Φ.source) (hfix : ∀ t x, x ∉ K → A (t, x) = x) {p : P × Y}
    (hsource : Set.MapsTo (fun x => A (p.1, x)) Φ.source Φ.source) :
    ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ (fun q : P × Y => extendMap Φ (fun x => A (q.1, x)) q.2) p :=
  by
  by_cases hp : p.2 ∈ Φ.target
  · have hback :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
        (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

private def Smale.SupportedDiffeomorph.bumpFamily {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (p : E × M) : M :=
  extendMap Φ (fun x => x + β x • p.1) p.2

private theorem Smale.SupportedDiffeomorph.bumpFamily_zero {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (y : M) : bumpFamily Φ β (0, y) = y := by
  have heq : (fun x : E => x + β x • (0 : E)) = id := by funext x; simp
  change extendMap Φ (fun x => x + β x • (0 : E)) y = y
  rw [heq]
  exact extendMap_id Φ y

private theorem Smale.SupportedDiffeomorph.bumpFamily_chart {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E) {x : E} (hx : x ∈ Φ.source) :
    bumpFamily Φ β (a, Φ x) = Φ (x + β x • a) :=
  extendMap_chart Φ _ hx

private theorem
    Smale.SupportedDiffeomorph.bumpFamily_mem_target {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E)
    (hsource : Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source) {y : M} (hy : y ∈ Φ.target) :
    bumpFamily Φ β (a, y) ∈ Φ.target :=
  extendMap_mem_target Φ hsource hy

private theorem
    Smale.SupportedDiffeomorph.bumpFamily_coordinates {E F H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E)
    (hsource : Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source) {y : M} (hy : y ∈ Φ.target) :
    Φ.symm (bumpFamily Φ β (a, y)) = Φ.symm y + β (Φ.symm y) • a := by
  change Φ.symm (extendMap Φ (fun x => x + β x • a) y) = _
  rw [extendMap_of_mem Φ _ hy]
  exact Φ.left_inv' (hsource (Φ.map_target' hy))

private theorem Smale.SupportedDiffeomorph.bumpFamily_fixed_outside {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (a : E) {y : M}
    (hy : y ∉ Φ '' tsupport β) : bumpFamily Φ β (a, y) = y := by
  apply extendMap_eq_of_notMem_image Φ (K := tsupport β) _ hy
  intro x hx
  have hzero : β x = 0 := by
    by_contra hn
    exact hx (subset_tsupport β hn)
  simp only [hzero, zero_smul, add_zero]

private theorem Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) [FiniteDimensional ℝ E] [T2Space M] {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        (∀ a : E, ‖a‖ < ε → ∃ D : Diffeomorph J J M M ∞, ∀ y, D y = bumpFamily Φ β (a, y)) ∧
          (∀ p : E × M, ‖p.1‖ < ε → ContMDiffAt (𝓘(ℝ, E).prod J) J ∞ (bumpFamily Φ β) p) ∧
            ∀ a : E, ‖a‖ < ε → Set.MapsTo (fun x => x + β x • a) Φ.source Φ.source := by
  obtain ⟨ε, hε, hsmall⟩ := Smale.SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let A : E × E → E := fun p => p.2 + β p.2 • p.1
  have hA : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hβ.contMDiff.comp contMDiff_snd).smul contMDiff_fst)
  have hfix : ∀ a x, x ∉ tsupport β → A (a, x) = x := by
    intro a x hx
    have hzero : β x = 0 := by
      by_contra hn
      exact hx (subset_tsupport β hn)
    simp only [A, hzero, zero_smul, add_zero]
  have hsource (a : E) (ha : ‖a‖ < ε) : Set.MapsTo (fun x => A (a, x)) Φ.source Φ.source := by
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    have heq : (fun x => A (a, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupport hdfix
  refine ⟨ε, hε, ?_, ?_, hsource⟩
  · intro a ha
    obtain ⟨d, hd, hdfix⟩ := hsmall a ha
    refine ⟨extension Φ d hcompact.isCompact hsupport hdfix, ?_⟩
    intro y
    change extendMap Φ d y = extendMap Φ (fun x => x + β x • a) y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext hd)
  · intro p hp
    exact contMDiffAt_extendFamily Φ hA hcompact.isCompact hsupport hfix (hsource p.1 hp)

private theorem
    Smale.SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) [FiniteDimensional ℝ E] [T2Space M] {X : Type*}
    [TopologicalSpace X] {β : E → ℝ} (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) {f : X → M} (hf : Continuous f) {C : Set X}
    (hC : IsCompact C) {O : Set M} (hO : IsOpen O) (hmap : Set.MapsTo f C O) :
    ∀ᶠ a in 𝓝 (0 : E), Set.MapsTo (fun x => bumpFamily Φ β (a, f x)) C O := by
  obtain ⟨δ, hδ, -, hsmooth, -⟩ := exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  apply hC.eventually_forall_of_forall_eventually
  intro x hx
  have hpair : ContinuousAt (fun p : E × X => (p.1, f p.2)) (0, x) :=
    (continuous_fst.prodMk (hf.comp continuous_snd)).continuousAt
  have hbase : ContinuousAt (bumpFamily Φ β) (0, f x) :=
    (hsmooth (0, f x) (by simpa only [norm_zero] using hδ)).continuousAt
  have hfamily : ContinuousAt (fun p : E × X => bumpFamily Φ β (p.1, f p.2)) (0, x) :=
    ContinuousAt.comp (g := bumpFamily Φ β) (f := fun p : E × X => (p.1, f p.2)) hbase hpair
  apply hfamily.preimage_mem_nhds
  apply hO.mem_nhds
  rw [bumpFamily_zero]
  exact hmap hx

private theorem Smale.SupportedDiffeomorph.exists_small_supported_bump_isotopy {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                    (∀ t y, y ∉ Φ '' tsupport β → A (t, y) = y) ∧
                      ∀ x ∈ Φ.source, A (1, Φ x) = Φ (x + β x • a) := by
  obtain ⟨ε, hε, hsmall⟩ := Smale.SmallPerturbation.exists_radius_bumpTranslation hs hcompact
  refine ⟨ε, hε, ?_⟩
  intro a ha
  let B : ℝ × E → E := fun p => p.2 + β p.2 • (Real.smoothTransition p.1 • a)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ B :=
    contMDiff_snd.add
      ((hs.contMDiff.comp contMDiff_snd).smul ((hθ.comp contMDiff_fst).smul contMDiff_const))
  have hmodel :
    ∀ t : ℝ,
      ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ x, d x = B (t, x)) ∧ ∀ x ∉ tsupport β, d x = x := by
    intro t
    have hnorm : ‖Real.smoothTransition t • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact mul_le_of_le_one_left (norm_nonneg a) (Real.smoothTransition.le_one t)
    exact hsmall (Real.smoothTransition t • a) (hnorm.trans_lt ha)
  have hfix : ∀ t x, x ∉ tsupport β → B (t, x) = x := by
    intro t x hx
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    exact (hd x).symm.trans (hdfix x hx)
  have hsource : ∀ t, Set.MapsTo (fun x => B (t, x)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    have heq : (fun x => B (t, x)) = d := funext (fun x => (hd x).symm)
    rw [heq]
    exact mapsTo_source Φ d.toEquiv hsupport hdfix
  let A : ℝ × M → M := fun p => extendMap Φ (fun x => B (p.1, x)) p.2
  refine ⟨A, contMDiff_extendFamily Φ hB hcompact.isCompact hsupport hfix hsource, ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun x => B (0, x)) = id := by
      funext x
      simp only [B, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero, id_eq]
    change extendMap Φ (fun x => B (0, x)) y = y
    rw [hzero]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨d, hd, hdfix⟩ := hmodel t
    refine ⟨extension Φ d hcompact.isCompact hsupport hdfix, ?_⟩
    intro y
    change extendMap Φ (fun x => B (t, x)) y = extendMap Φ d y
    exact congrArg (fun f : E → E => extendMap Φ f y) (funext (fun x => (hd x).symm))
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (hfix t) hy
  · intro x hx
    change extendMap Φ (fun y => B (1, y)) (Φ x) = _
    rw [extendMap_chart Φ (fun y => B (1, y)) hx]
    simp only [B, Real.smoothTransition.one, one_smul]

private def Smale.SupportedDiffeomorph.IsotopicToIdentity {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (e : Diffeomorph J J M M ∞) : Prop :=
  ∃ A : ℝ × M → M,
    ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
      (∀ y, A (0, y) = y) ∧
        (∀ y, A (1, y) = e y) ∧ ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y

private theorem
    Smale.SupportedDiffeomorph.isotopicToIdentity_refl {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] : IsotopicToIdentity (Diffeomorph.refl J M ∞) := by
  refine ⟨Prod.snd, contMDiff_snd, fun _ => rfl, fun _ => rfl, ?_⟩
  exact fun _ => ⟨Diffeomorph.refl J M ∞, fun _ => rfl⟩

private theorem
    Smale.SupportedDiffeomorph.IsotopicToIdentity.trans {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] {e d : Diffeomorph J J M M ∞}
    (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e)
    (hd : Smale.SupportedDiffeomorph.IsotopicToIdentity d) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity (e.trans d) := by
  obtain ⟨A, hA, hA₀, hA₁, hAd⟩ := he
  obtain ⟨B, hB, hB₀, hB₁, hBd⟩ := hd
  refine ⟨fun p => B (p.1, A p), hB.comp (contMDiff_fst.prodMk hA), ?_, ?_, ?_⟩
  · intro y
    change B (0, A (0, y)) = y
    rw [hA₀, hB₀]
  · intro y
    change B (1, A (1, y)) = d (e y)
    rw [hA₁, hB₁]
  · intro t
    obtain ⟨e', he'⟩ := hAd t
    obtain ⟨d', hd'⟩ := hBd t
    refine ⟨e'.trans d', ?_⟩
    intro y
    change B (t, A (t, y)) = d' (e' y)
    rw [he', hd']

private theorem Smale.SupportedDiffeomorph.exists_radius_bumpFamily_isotopy {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∀ e : Diffeomorph J J M M ∞,
              (∀ y, e y = bumpFamily Φ β (a, y)) → IsotopicToIdentity e := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  refine ⟨A, hA, hzero, ?_, hdiff⟩
  intro y
  rw [he]
  by_cases hy : y ∈ Φ.target
  · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
    have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
    rw [hpoint] at hh
    change A (1, y) = extendMap Φ (fun x => x + β x • a) y
    rw [extendMap_of_mem Φ _ hy]
    exact hh
  · have hnot : y ∉ Φ '' tsupport β := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hsupport hx))
    rw [hfix 1 y hnot, bumpFamily_fixed_outside Φ β a hnot]

private structure Smale.SupportedDiffeomorph.SupportedRelativeIsotopy {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] (e : Diffeomorph J J M M ∞) (K S : Set M) where
  family : ℝ × M → M
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ x, family (0, x) = x
  one : ∀ x, family (1, x) = e x
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ x, d x = family (t, x)
  fixedOutside : ∀ t x, x ∉ K → family (t, x) = x
  fixedOn : ∀ t x, x ∈ S → family (t, x) = x

private theorem
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.isotopicToIdentity {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity e := by
  refine ⟨A.family, A.smooth, A.zero, A.one, ?_⟩
  intro t
  obtain ⟨d, hd⟩ := A.slices t
  exact ⟨d, fun x => (hd x).symm⟩

private theorem
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.endpoint_fixed_outside {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) (x : M) (hx : x ∉ K) :
    e x = x :=
  (A.one x).symm.trans (A.fixedOutside 1 x hx)

private theorem
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.endpoint_fixed_on {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {K S : Set M}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) (x : M) (hx : x ∈ S) :
    e x = x :=
  (A.one x).symm.trans (A.fixedOn 1 x hx)

private structure Degree.FlowSuspension.SuspensionCoordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E) (W : (E × ℝ) → E × ℝ)
    (F : Flow ℝ (E × ℝ)) where
  chart : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞
  field_eq : W = suspensionField chart
  flow_eq : F = suspensionFlow chart
  height : ∀ p, (chart p).2 = p.2
  base_iff : ∀ U : Set E, K ⊆ U → ∀ p, (chart p).1 ∈ U ↔ p.1 ∈ U
  lower : ∀ p, p.2 ≤ 0 → chart p = p
  upper : ∀ p, 1 ≤ p.2 → chart p = (D p.1, p.2)

private theorem
    Degree.FlowSuspension.exists_compact_isotopy_suspension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {K S : Set E} (hK : IsCompact K)
    (I : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K S) :
    ∃ (W : (E × ℝ) → E × ℝ) (F : Flow ℝ (E × ℝ)),
      ContDiff ℝ ∞ W ∧
        (∀ p, (W p).2 = 1) ∧
          HasCompactSupport (fun p => W p - (0, 1)) ∧
            tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) ∧
              (∀ p t, HasDerivAt (fun s => F s p) (W (F t p)) t) ∧
                (∀ x, F 1 (x, 0) = (D x, 1)) ∧
                  (∀ t p, (F t p).2 = p.2 + t) ∧
                    (∀ x ∉ K, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
                      (∀ x ∈ S, ∀ s t : ℝ, F t (x, s) = (x, s + t)) ∧
                        Nonempty (SuspensionCoordinates D K W F) := by
  let τ : ℝ → ℝ := fun s => Real.smoothTransition (3 * s - 1)
  have hτ : ContDiff ℝ ∞ τ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hτlower (s : ℝ) (hs : s ≤ 1 / 3) : τ s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hτupper (s : ℝ) (hs : 2 / 3 ≤ s) : τ s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  let A : ℝ × E → E := fun p => I.family (τ p.1, p.2)
  have hInorm : ContDiff ℝ ∞ I.family :=
    (I.smooth.comp (Smale.PartialChart.vectorProduct ℝ E).contMDiff).contDiff
  have hA : ContDiff ℝ ∞ A := hInorm.comp ((hτ.comp contDiff_fst).prodMk contDiff_snd)
  have hslice (s : ℝ) : ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = A (s, x) :=
    I.slices (τ s)
  have hA0 (x : E) : A (0, x) = x := by
    change I.family (τ 0, x) = x
    rw [hτlower 0 (by norm_num)]
    exact I.zero x
  have hA1 (x : E) : A (1, x) = D x := by
    change I.family (τ 1, x) = D x
    rw [hτupper 1 (by norm_num)]
    exact I.one x
  have hfix (s : ℝ) (x : E) (hx : x ∉ K) : A (s, x) = x := I.fixedOutside (τ s) x hx
  have hstationary (s : ℝ) (hs : s ∉ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x) := by
    by_cases hlo : s < 1 / 3
    · filter_upwards [eventually_lt_nhds hlo] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτlower r hr.le, hτlower s hlo.le]
    · have hhi : 2 / 3 < s := lt_of_not_ge (fun h => hs ⟨le_of_not_gt hlo, h⟩)
      filter_upwards [eventually_gt_nhds hhi] with r hr
      intro x
      change I.family (τ r, x) = I.family (τ s, x)
      rw [hτupper r hr.le, hτupper s hhi.le]
  obtain ⟨Ψ, hΨ⟩ := exists_isotopy_suspension_diffeomorph hA hslice
  let W := suspensionField Ψ
  let F := suspensionFlow Ψ
  have hvertical (p : E × ℝ) (hp : p ∉ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3)) : W p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · exact
        suspensionField_eq_vertical_of_stationary Ψ hΨ p (hstationary p.2 (fun h => hp ⟨hx, h⟩))
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  have hsupp : tsupport (fun p => W p - (0, 1)) ⊆ K ×ˢ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
    apply closure_minimal _ (hK.isClosed.prod isClosed_Icc)
    intro p hp
    by_contra hout
    apply hp
    change W p - (0, 1) = 0
    rw [hvertical p hout, sub_self]
  have hcoords : SuspensionCoordinates D K W F := by
    refine ⟨Ψ, rfl, rfl, fun p => by rw [hΨ], ?_, ?_, ?_⟩
    · intro U hKU p
      have hfixU (z : E × ℝ) (hz : z ∉ U ×ˢ Set.univ) : Ψ z = z := by
        have hn : z.1 ∉ K := fun h => hz ⟨hKU h, Set.mem_univ _⟩
        rw [hΨ, hfix z.2 z.1 hn]
      have hmaps := Smale.SupportedDiffeomorph.mapsTo_of_fixed_outside Ψ.toEquiv hfixU
      have hmapsInv :=
        Smale.SupportedDiffeomorph.mapsTo_of_fixed_outside Ψ.symm.toEquiv
          (Smale.SupportedDiffeomorph.inverse_fixed_outside Ψ.toEquiv hfixU)
      constructor
      · intro hp
        have hh := hmapsInv ⟨hp, Set.mem_univ (Ψ p).2⟩
        have hh' : (Ψ.symm (Ψ p)).1 ∈ U := hh.1
        simpa only [Ψ.symm_apply_apply] using hh'
      · intro hp
        exact (hmaps ⟨hp, Set.mem_univ p.2⟩).1
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = p
      rw [hτlower p.2 (by linarith), I.zero]
    · intro p hp
      rw [hΨ]
      change (I.family (τ p.2, p.1), p.2) = (D p.1, p.2)
      rw [hτupper p.2 (by linarith), I.one]
  refine
    ⟨W, F, contDiff_suspensionField Ψ, suspensionField_height Ψ (fun p => by rw [hΨ]),
      hasCompactSupport_suspensionField_sub_vertical Ψ hΨ hK hfix hstationary, hsupp,
      hasDerivAt_suspensionFlow Ψ, ?_, suspensionFlow_height Ψ (fun p => by rw [hΨ]), ?_, ?_,
      ⟨hcoords⟩⟩
  · intro x
    exact
      (suspensionFlow_endpoint Ψ hΨ hA0 x).trans (congrArg (fun y : E => (y, (1 : ℝ))) (hA1 x))
  · intro x hx s t
    exact suspensionFlow_vertical_off_support Ψ hΨ hfix (p := (x, s)) hx t
  · intro x hx s t
    have hΨfix (r : ℝ) : Ψ (x, r) = (x, r) := by
      rw [hΨ]
      change (I.family (τ r, x), r) = (x, r)
      rw [I.fixedOn (τ r) x hx]
    change suspensionFlow Ψ t (x, s) = (x, s + t)
    rw [← hΨfix s, suspensionFlow_chart, hΨfix]

private def Degree.LocalFieldReplacement.replace {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : M) : TangentSpace 𝓘(ℝ, E) x := by
  classical exact if x ∈ Φ.target then W x else V x

private theorem
    Degree.LocalFieldReplacement.replace_of_mem {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) {x : M} (hx : x ∈ Φ.target) :
    replace Φ V W x = W x := by simp [replace, hx]

private theorem
    Degree.LocalFieldReplacement.replace_of_notMem {D E H X M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H} [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x) {x : M} (hx : x ∉ Φ.target) :
    replace Φ V W x = V x := by simp [replace, hx]

private theorem Degree.LocalFieldReplacement.exists_smooth_field_replacement {D E H X M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ D H}
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞) [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (V W : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hW :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M))
        Φ.target)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∈ Φ.target, x ∉ Φ '' K → W x = V x) (hreg : ∀ x ∈ Φ.target, W x ≠ 0) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ Φ.target, V' x = W x) ∧
          (∀ x, V' x = 0 ↔ V x = 0 ∧ x ∉ Φ.target) ∧ ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let V' := replace Φ V W
  have hclosed : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  have hoff (x : M) (hx : x ∉ Φ '' K) : ∀ᶠ y in 𝓝 x, V' y = V y := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    by_cases hyt : y ∈ Φ.target
    · exact (replace_of_mem Φ V W hyt).trans (hfix y hyt hy)
    · exact replace_of_notMem Φ V W hyt
  have hsmooth :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    intro x
    by_cases hx : x ∈ Φ.target
    · apply (hW.contMDiffAt (Φ.open_target.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [Φ.open_target.mem_nhds hx] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M)) (replace_of_mem Φ V W hy)
    · have hnot : x ∉ Φ '' K := by
        rintro ⟨p, hp, rfl⟩
        exact hx (Φ.map_source' (hKΦ hp))
      apply hV.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [hoff x hnot] with y hy
      exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) M)) hy
  refine ⟨V', hsmooth, fun x hx => replace_of_mem Φ V W hx, ?_, hoff⟩
  intro x
  by_cases hx : x ∈ Φ.target
  · rw [show V' x = W x from replace_of_mem Φ V W hx]
    simp only [hreg x hx, hx, not_true_eq_false, and_false]
  · rw [show V' x = V x from replace_of_notMem Φ V W hx]
    simp only [hx, not_false_eq_true, and_true]

private theorem
    Smale.exists_compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : E → ℝ,
      ContDiff ℝ ∞ η ∧
        HasCompactSupport η ∧
          tsupport η ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, η x = 1) ∧ ∀ x, η x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨η, hηone, hηzero, hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hK.isClosed hKL (n := ⊤)
  have hsupp : tsupport (η : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hxL
    exact hx (hηzero x hxL)
  exact
    ⟨η, η.contMDiff.contDiff, HasCompactSupport.intro hL hηzero, hsupp.trans hLU, hηone, hηrange⟩

private def
    MorseCancel.cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) (φ : Model m → ℝ) (p : Model m) :
    Model m :=
  (a ^ 2 - p.1 ^ 2 - 2 * a ^ 2 * φ p, fun i => -σ i * p.2 i)

private theorem
    MorseCancel.contDiff_cancelledDescent {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (cancelledDescent σ a φ) := by
  unfold cancelledDescent
  fun_prop

private theorem
    MorseCancel.cancelledDescent_axis_negative {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {φ : Model m → ℝ} (hφ : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) (s : ℝ) :
    (cancelledDescent σ a φ (s, 0)).1 < 0 := by
  change a ^ 2 - s ^ 2 - 2 * a ^ 2 * φ (s, 0) < 0
  by_cases hs : s ∈ Set.Icc (-a) a
  · rw [hone s hs]
    nlinarith [sq_pos_of_pos ha, sq_nonneg s]
  · have hsq : a ^ 2 < s ^ 2 := by
      by_cases hl : -a ≤ s
      · have hr : a < s := lt_of_not_ge (fun h => hs ⟨hl, h⟩)
        nlinarith
      · have hh : s < -a := lt_of_not_ge hl
        nlinarith
    have hnonneg : 0 ≤ 2 * a ^ 2 * φ (s, 0) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) (hφ (s, 0))
    linarith

private theorem
    MorseCancel.cancelledDescent_ne_zero {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {a : ℝ}
    (ha : 0 < a) {φ : Model m → ℝ} (hφ : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1)
    (p : Model m) : cancelledDescent σ a φ p ≠ 0 := by
  intro hp
  have hz : p.2 = 0 := by
    funext i
    have hi := congrArg (fun q : Model m => q.2 i) hp
    change -σ i * p.2 i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr (hσ i))
  have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
  have hx := congrArg Prod.fst hp
  rw [he] at hx
  exact (cancelledDescent_axis_negative σ ha hφ hone p.1).ne hx

private theorem MorseCancel.cancelledDescent_germ_off_support {m : ℕ} (σ : Fin m → ℝ) (a : ℝ)
    {φ : Model m → ℝ} {p : Model m} (hp : p ∉ tsupport φ) :
    cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
  apply Prod.ext
  · simp only [cancelledDescent, cubicDescent, hq, Pi.zero_apply, MulZeroClass.mul_zero, sub_zero]
    ring
  · rfl

private theorem
    MorseCancel.exists_cubic_field_cancellation {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a) {U : Set (Model m)} (hU : IsOpen U)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ U) :
    ∃ φ : Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ U ∧
            (∀ p, φ p ∈ Set.Icc (0 : ℝ) 1) ∧
              (∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) ∧
                ContDiff ℝ ∞ (cancelledDescent σ a φ) ∧
                  (∀ p, cancelledDescent σ a φ p ≠ 0) ∧
                    ∀ p ∉ tsupport φ, cancelledDescent σ a φ =ᶠ[𝓝 p] cubicDescent σ (-(a ^ 2)) := by
  obtain ⟨φ, hφ, hc, hsupp, hone, hrange⟩ :=
    Smale.exists_compact_smooth_cutoff (CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hU
      haxis
  have hone' (s : ℝ) (hs : s ∈ Set.Icc (-a) a) : φ (s, (0 : Fin m → ℝ)) = 1 := by
    have hn : ∀ᶠ p in 𝓝 (s, (0 : Fin m → ℝ)), φ p = 1 :=
      (nhds_le_nhdsSet (show (s, (0 : Fin m → ℝ)) ∈ Set.Icc (-a) a ×ˢ {0} from ⟨hs, rfl⟩)) hone
    exact hn.self_of_nhds
  exact
    ⟨φ, hφ, hc, hsupp, hrange, hone', contDiff_cancelledDescent σ a hφ,
      cancelledDescent_ne_zero σ hσ ha (fun p => (hrange p).1) hone', fun p hp =>
      cancelledDescent_germ_off_support σ a hp⟩

private theorem MorseCancel.partialChartField_zero_iff {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (W : D → D) {x : M}
    (hx : x ∈ Φ.target) :
    Smale.FlowConstruction.partialChartField Φ.symm W x = 0 ↔ W (Φ.symm x) = 0 := by
  rw [Smale.FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm W hx]
  have hl : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ Φ (Φ.symm x) :=
    ⟨Φ, Φ.map_target' hx, fun _ _ => rfl⟩
  let A := hl.mfderivToContinuousLinearEquiv (by simp)
  let B : D ≃L[ℝ] TangentSpace 𝓘(ℝ, D) (Φ.symm x) :=
    (NormedSpace.fromTangentSpace (Φ.symm x)).symm
  change A (B (W (Φ.symm x))) = 0 ↔ W (Φ.symm x) = 0
  constructor
  · intro h
    have hb : B (W (Φ.symm x)) = 0 := A.injective (h.trans (map_zero A).symm)
    exact B.injective (hb.trans (map_zero B).symm)
  · intro h
    rw [h, map_zero, map_zero]

private theorem
    MorseCancel.cubicDescent_zero_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) (a : ℝ)
    (p : Model m) : cubicDescent σ (-(a ^ 2)) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [← negative_parameter_critical_iff σ hσ a p]
  constructor
  · intro hp
    by_contra hn
    have hh := cubicDescent_strict σ hn
    rw [hp, map_zero] at hh
    exact lt_irrefl _ hh
  · exact cubicDescent_zero_of_critical σ

private theorem
    MorseCancel.exists_native_cubic_field_cancellation_in {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ)
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (hσ : ∀ i, σ i ≠ 0) {a : ℝ}
    (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) {N : Set M}
    (hN : IsOpen N) (haxisN : ∀ s ∈ Set.Icc (-a) a, Φ (s, 0) ∈ N) :
    ∃ φ : Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ Φ.source ∧
            Φ '' tsupport φ ⊆ N ∧
              (∀ p, φ p ∈ Set.Icc (0 : ℝ) 1) ∧
                (∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) ∧
                  ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
                    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                      (∀ x ∈ Φ.target,
                          V' x =
                            Smale.FlowConstruction.partialChartField Φ.symm
                              (cancelledDescent σ a φ) x) ∧
                        (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
                          ∀ x ∉ Φ '' tsupport φ, ∀ᶠ y in 𝓝 x, V' y = V y := by
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' N) := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hN
  have haxis' : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∩ Φ ⁻¹' N := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact ⟨haxis ⟨hs, rfl⟩, haxisN s hs⟩
  obtain ⟨φ, hφ, hc, hsupp', hrange, hone, hD, hnonzero, hoff⟩ :=
    exists_cubic_field_cancellation σ hσ ha hopen haxis'
  have hsupp : tsupport φ ⊆ Φ.source := fun _ hx => (hsupp' hx).1
  have hsuppN : Φ '' tsupport φ ⊆ N := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsupp' hz).2
  let W := Smale.FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ)
  have hW :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M))
      Φ.target :=
    Smale.FlowConstruction.contMDiffOn_partialChartField Φ.symm hD
  have hfix (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' tsupport φ) : W x = V x := by
    have hinv : Φ.symm x ∉ tsupport φ := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    have he := (hoff (Φ.symm x) hinv).eq_of_nhds
    rw [hmodel x hx]
    unfold W nativeCubicDescent Smale.FlowConstruction.partialChartField
    simp only [VectorField.mpullback_apply, he]
  have hreg (x : M) (hx : x ∈ Φ.target) : W x ≠ 0 := by
    intro hz
    exact hnonzero _ ((partialChartField_zero_iff Φ (cancelledDescent σ a φ) hx).mp hz)
  obtain ⟨V', hV', heq, hzero, hkeep⟩ :=
    Degree.LocalFieldReplacement.exists_smooth_field_replacement Φ V W hV hW hc hsupp hfix hreg
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  refine ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, ?_, hkeep⟩
  intro x
  rw [hzero x]
  constructor
  · rintro ⟨hx, hout⟩
    exact ⟨hx, fun he => hout (he ▸ Φ.map_source' hp), fun he => hout (he ▸ Φ.map_source' hq)⟩
  · rintro ⟨hx, hxp, hxq⟩
    refine ⟨hx, ?_⟩
    intro hxt
    have hz : Smale.FlowConstruction.partialChartField Φ.symm (cubicDescent σ (-(a ^ 2))) x = 0 :=
      (hmodel x hxt).symm.trans hx
    have hd := (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) hxt).mp hz
    rcases (cubicDescent_zero_iff σ hσ a (Φ.symm x)).mp hd with hh | hh
    · exact hxp ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))
    · exact hxq ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))

private theorem Degree.FlowSuspension.exists_native_vertical_field_replacement {E B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace M] [ChartedSpace B M] [T2Space M]
    [IsManifold 𝓘(ℝ, B) ∞ M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel :
      ∀ x ∈ Φ.target,
        V x = Smale.FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    {W : (E × ℝ) → E × ℝ} (hW : ContDiff ℝ ∞ W) (hWheight : ∀ p, (W p).2 = 1) {K : Set (E × ℝ)}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ p ∉ K, W p = (0, 1)) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, B) x,
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
        (∀ x ∈ Φ.target, V' x = Smale.FlowConstruction.partialChartField Φ.symm W x) ∧
          (∀ x, V' x = 0 ↔ V x = 0) ∧ ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let Wn := Smale.FlowConstruction.partialChartField Φ.symm W
  have hWn :
    ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞ (fun x => (⟨x, Wn x⟩ : TangentBundle 𝓘(ℝ, B) M))
      Φ.target :=
    Smale.FlowConstruction.contMDiffOn_partialChartField Φ.symm hW
  have hreg (x : M) (hx : x ∈ Φ.target) : Wn x ≠ 0 := by
    intro hz
    have hWzero := (MorseCancel.partialChartField_zero_iff Φ W hx).mp hz
    have hh := congrArg Prod.snd hWzero
    rw [hWheight] at hh
    exact one_ne_zero hh
  have hregV (x : M) (hx : x ∈ Φ.target) : V x ≠ 0 := by
    rw [hmodel x hx]
    intro hz
    have hh := (MorseCancel.partialChartField_zero_iff Φ (fun _ : E × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hkeep (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' K) : Wn x = V x := by
    have hz : Φ.symm x ∉ K := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    rw [hmodel x hx]
    change Smale.FlowConstruction.partialChartField Φ.symm W x = _
    unfold Smale.FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, VectorField.mpullback_apply, hfix _ hz]
  obtain ⟨V', hV', hnew, hzeros, hgerm⟩ :=
    Degree.LocalFieldReplacement.exists_smooth_field_replacement Φ V Wn hV hWn hK hKΦ hkeep hreg
  refine ⟨V', hV', hnew, ?_, hgerm⟩
  intro x
  exact (hzeros x).trans ⟨And.left, fun hx => ⟨hx, fun ht => hregV x ht hx⟩⟩

private theorem
    Degree.FlowSuspension.mvfderiv_native_height_field {E B M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace M]
    [ChartedSpace B M] (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ} (hheight : ∀ p ∈ Φ.source, f (Φ p) = b - p.2)
    (W : (E × ℝ) → E × ℝ) {x : M} (hx : x ∈ Φ.target) :
    mvfderiv 𝓘(ℝ, B) f x (Smale.FlowConstruction.partialChartField Φ.symm W x) =
      -(W (Φ.symm x)).2 := by
  let q := Φ.symm x
  have hq : q ∈ Φ.source := Φ.map_target' hx
  have heq : (f ∘ Φ) =ᶠ[𝓝 q] (fun p : E × ℝ => b - p.2) := by
    filter_upwards [Φ.open_source.mem_nhds hq] with p hp
    exact hheight p hp
  have hd : fderiv ℝ (f ∘ Φ) q = fderiv ℝ (fun p : E × ℝ => b - p.2) q := heq.fderiv_eq
  rw [Smale.FlowConstruction.mvfderiv_partialChartField hf Φ.symm W hx]
  change fderiv ℝ (f ∘ Φ) q (W q) = -(W q).2
  rw [hd]
  have hh := (hasFDerivAt_const (𝕜 := ℝ) b q).sub (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hh' :
    fderiv ℝ (fun p : E × ℝ => b - p.2) q =
      (0 : (E × ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.snd ℝ E ℝ :=
    hh.fderiv
  rw [hh']
  simp

private theorem Degree.FlowCancellation.exists_excursion_interval {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X} (hγ : Continuous γ) {K N : Set X} (hK : IsClosed K) (hKN : K ⊆ N) {a b t : ℝ}
    (ht : t ∈ Set.Icc a b) (ha : γ a ∈ N) (hb : γ b ∈ N) (hout : γ t ∉ N) :
    ∃ s u : ℝ, a ≤ s ∧ s < t ∧ t < u ∧ u ≤ b ∧ γ s ∈ N ∧ γ u ∈ N ∧ ∀ r ∈ Set.Ioo s u, γ r ∉ K := by
  let A := Insert.insert a (Set.Icc a t ∩ γ ⁻¹' K)
  let B := Insert.insert b (Set.Icc t b ∩ γ ⁻¹' K)
  have hA : IsCompact A := (CompactIccSpace.isCompact_Icc.inter_right (hK.preimage hγ)).insert a
  have hB : IsCompact B := (CompactIccSpace.isCompact_Icc.inter_right (hK.preimage hγ)).insert b
  obtain ⟨s, hs⟩ := hA.exists_isGreatest (Set.insert_nonempty _ _)
  obtain ⟨u, hu⟩ := hB.exists_isLeast (Set.insert_nonempty _ _)
  have has : a ≤ s := hs.2 (Set.mem_insert _ _)
  have hub : u ≤ b := hu.2 (Set.mem_insert _ _)
  have hst : s ≤ t := by
    rcases hs.1 with he | hh
    · exact he ▸ ht.1
    · exact hh.1.2
  have htu : t ≤ u := by
    rcases hu.1 with he | hh
    · exact he ▸ ht.2
    · exact hh.1.1
  have hsN : γ s ∈ N := by
    rcases hs.1 with he | hh
    · exact he ▸ ha
    · exact hKN hh.2
  have huN : γ u ∈ N := by
    rcases hu.1 with he | hh
    · exact he ▸ hb
    · exact hKN hh.2
  have hst' : s < t := lt_of_le_of_ne hst (fun he => hout (he ▸ hsN))
  have htu' : t < u := lt_of_le_of_ne htu (fun he => hout (he ▸ huN))
  refine ⟨s, u, has, hst', htu', hub, hsN, huN, ?_⟩
  intro r hr hrK
  by_cases hrt : r ≤ t
  · have hrA : r ∈ A := Or.inr ⟨⟨le_trans has hr.1.le, hrt⟩, hrK⟩
    exact (not_le_of_gt hr.1) (hs.2 hrA)
  · have hrB : r ∈ B := Or.inr ⟨⟨(lt_of_not_ge hrt).le, le_trans hr.2.le hub⟩, hrK⟩
    exact (not_le_of_gt hr.2) (hu.2 hrB)

private theorem Degree.FlowCancellation.native_curve_eq_flow_on_closed_interval {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {γ : ℝ → M}
    (hγcont : Continuous γ) {a b c : ℝ} (hc : c ∈ Set.Ioo a b)
    (hγ : IsMIntegralCurveOn γ V (Set.Ioo a b)) : ∀ t ∈ Set.Icc a b, γ t = F (t - c) (γ c) := by
  have hF : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have he : (fun t => F (t - c) (γ c)) = ((fun t => F t (γ c)) ∘ (· + -c)) := by
      funext t
      simp only [Function.comp_apply, sub_eq_add_neg]
    rw [he]
    exact (hcurve (γ c)).comp_add (-c)
  have heq : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ (hF.isMIntegralCurveOn _)
      (by simp)
  have heqclosed := heq.closure hγcont hF.continuous
  rw [closure_Ioo (lt_trans hc.1 hc.2).ne] at heqclosed
  exact heqclosed

private theorem Degree.FlowCancellation.native_no_return_of_supported_perturbation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V V' : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {K N U : Set M}
    (hK : IsClosed K) (hKN : K ⊆ N) (hNU : N ⊆ U) (hoff : ∀ x ∉ K, V' x = V x)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V') {a b : ℝ} (ha : γ a ∈ N) (hb : γ b ∈ N) :
    ∀ t ∈ Set.Icc a b, γ t ∈ U := by
  intro t ht
  by_contra hout
  obtain ⟨s, u, -, hst, htu, -, hsN, huN, havoid⟩ :=
    exists_excursion_interval hγ.continuous hK hKN ht ha hb (fun hh => hout (hNU hh))
  have hold : IsMIntegralCurveOn γ V (Set.Ioo s u) := by
    intro r hr
    have hd := (hγ r).hasMFDerivWithinAt (s := Set.Ioo s u)
    rw [hoff (γ r) (havoid r hr)] at hd
    exact hd
  have heq :=
    native_curve_eq_flow_on_closed_interval hV F hcurve hγ.continuous
      (show t ∈ Set.Ioo s u from ⟨hst, htu⟩) hold
  have hs : γ s = F (s - t) (γ t) := heq s ⟨le_rfl, (lt_trans hst htu).le⟩
  have hu : γ u = F (u - t) (γ t) := heq u ⟨(lt_trans hst htu).le, le_rfl⟩
  have hend : F (u - s) (γ s) = γ u := by
    rw [hs, ← F.map_add, show u - s + (s - t) = u - t by ring, ← hu]
  have hmid : F (t - s) (γ s) = γ t := by
    rw [hs, ← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply]
  have hh :=
    hnoreturn (γ s) hsN (u - s) (sub_nonneg.mpr (lt_trans hst htu).le) (hend ▸ huN) (t - s)
      ⟨sub_nonneg.mpr hst.le, sub_le_sub_right htu.le s⟩
  exact hout (hmid ▸ hh)

private theorem
    Degree.FlowSuspension.native_flow_segment_endpoints {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) 1 M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, B) x}
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (hγcont : ContinuousOn γ (Set.Icc a b))
    (hγ : IsMIntegralCurveOn γ V (Set.Ioo a b)) : F (b - a) (γ a) = γ b := by
  let c := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by constructor <;> dsimp [c] <;> linarith
  have hη : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have hh := (hcurve (γ c)).comp_add (-c)
    simpa only [sub_eq_add_neg, Function.comp_def] using hh
  have heq : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ (hη.isMIntegralCurveOn _)
      (by simp)
  have heqclosed : Set.EqOn γ (fun t => F (t - c) (γ c)) (Set.Icc a b) :=
    heq.of_subset_closure hγcont hη.continuous.continuousOn Set.Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  have ha := heqclosed (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
  have hb := heqclosed (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩)
  change γ a = F (a - c) (γ c) at ha
  change γ b = F (b - c) (γ c) at hb
  rw [ha, ← F.map_add, show b - a + (a - c) = b - c by ring, ← hb]

private theorem
    MorseCancel.native_cubic_flow_between_box_points {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c r : ℝ}
    (hbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source) (z : Fin m → ℝ) {s t : ℝ}
    (hs : cubicFlowCylinder σ a (z, s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (ht : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    F (t - s) (Φ (cubicFlowCylinder σ a (z, s))) = Φ (cubicFlowCylinder σ a (z, t)) := by
  let γ : ℝ → M := fun u => Φ (cubicFlowCylinder σ a (z, u))
  have hforward {u v : ℝ} (huv : u < v)
    (hu : cubicFlowCylinder σ a (z, u) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r)
    (hv : cubicFlowCylinder σ a (z, v) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) :
    F (v - u) (γ u) = γ v := by
    have hstay (w : ℝ) (hw : w ∈ Set.Icc u v) : cubicFlowCylinder σ a (z, w) ∈ Φ.source :=
      hbox (cubicFlowCylinder_stays_axis_ball σ ha z hw hu hv)
    have hcont : ContinuousOn γ (Set.Icc u v) :=
      Φ.contMDiffOn_toFun.continuousOn.comp
        (((contDiff_cubicFlowCylinder σ a).continuous.comp
            (continuous_const.prodMk continuous_id)).continuousOn)
        hstay
    have hcurve : IsMIntegralCurveOn γ V (Set.Ioo u v) := by
      intro w hw
      have hp := hstay w ⟨hw.1.le, hw.2.le⟩
      have hd :=
        Smale.FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
          (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicFlowCylinder σ a z w) hp
      have hd' :
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ w
          ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeCubicDescent σ Φ (-(a ^ 2)) (γ w))) :=
        hd
      rw [← hmodel (γ w) (Φ.map_source' hp)] at hd'
      exact hd'.hasMFDerivWithinAt
    exact Degree.FlowSuspension.native_flow_segment_endpoints hV F hF huv hcont hcurve
  rcases lt_trichotomy s t with hst | hst | hts
  · exact hforward hst hs ht
  · subst t
    rw [sub_self, F.map_zero_apply]
  · have hh := congrArg (F (t - s)) (hforward hts ht hs)
    rw [← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply] at hh
    exact hh.symm

private theorem
    MorseCancel.exists_cubic_slice_in_axis_ball {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {c r : ℝ} (hc : c ∈ Set.Icc (-a) a) (hr : 0 < r) :
    ∃ (T δ : ℝ),
      0 < δ ∧
        ∀ z : Fin m → ℝ,
          ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r := by
  have hcl : c ∈ closure (Set.Ioo (-a) a) := by
    rw [closure_Ioo (by linarith : -a ≠ a)]
    exact hc
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp hcl r hr
  let T := cubicAxisClock a s
  have hpoint : cubicFlowCylinder σ a (0, T) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hnear : cubicFlowCylinder σ a (0, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r := by
    rw [hpoint, Metric.mem_ball, Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg : 0 ≤ Dist.dist s c)]
    simpa only [dist_comm] using hdist
  have hcont : Continuous (fun z : Fin m → ℝ => cubicFlowCylinder σ a (z, T)) :=
    (contDiff_cubicFlowCylinder σ a).continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      (hcont.continuousAt (Metric.isOpen_ball.mem_nhds hnear))
  refine ⟨T, δ, hδ, ?_⟩
  intro z hz
  exact hδsub (mem_closedBall_zero_iff.mpr hz)

private theorem MorseCancel.exists_native_cubic_endpoint_flow_coordinates {m : ℕ} {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) :
    ∃ (r δ T : ℝ),
      0 < r ∧
        0 < δ ∧
          Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
            (∀ z : Fin m → ℝ,
                ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
              ∀ p ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r,
                p.1 ∈ Set.Ioo (-a) a →
                  ‖(cubicFlowCylinderInverse σ a p).1‖ ≤ δ →
                    Φ p =
                      F (cubicAxisClock a p.1 - T)
                        (Φ (cubicFlowCylinder σ a ((cubicFlowCylinderInverse σ a p).1, T))) := by
  obtain ⟨r, hr, hbox⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds hcΦ)
  obtain ⟨T, δ, hδ, hslice⟩ := exists_cubic_slice_in_axis_ball σ ha hc hr
  refine ⟨r, δ, T, hr, hδ, hbox, hslice, ?_⟩
  intro p hp hpa hpδ
  let z := (cubicFlowCylinderInverse σ a p).1
  have hinit := Metric.ball_subset_closedBall (hslice z hpδ)
  have hpoint : cubicFlowCylinder σ a (z, cubicAxisClock a p.1) = p :=
    cubicFlowCylinder_right_inv σ ha hpa
  have hfinish :
    cubicFlowCylinder σ a (z, cubicAxisClock a p.1) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    hpoint.symm ▸ hp
  have hh := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox z hinit hfinish
  rw [hpoint] at hh
  exact hh.symm

private theorem
    MorseCancel.exists_endpoint_slice_on_actual_orbit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ} [Filter.NeBot l]
    (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (r δ T τ : ℝ),
      0 < r ∧
        0 < δ ∧
          Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
            (∀ z : Fin m → ℝ,
                ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
              Φ (cubicFlowCylinder σ a (0, T)) = F τ x := by
  obtain ⟨r, δ, T, hr, hδ, hbox, hslice, _⟩ :=
    exists_native_cubic_endpoint_flow_coordinates σ ha Φ hV hmodel F hF hc hcΦ
  have hcont := Φ.toOpenPartialHomeomorph.symm.continuousAt (Φ.map_source' hcΦ)
  have hcoord : Filter.Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (c, (0 : Fin m → ℝ))) := by
    have hh : Filter.Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (Φ.symm (Φ (c, 0)))) :=
      hcont.tendsto.comp hlim
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    rwa [hinv] at hh
  have hnear : ∀ᶠ t in l, Φ.symm (F t x) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hcoord.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨t, htnear, s, hs, hsΦ, hsorbit⟩ := (hnear.and htail).exists
  have hinv : Φ.symm (F t x) = (s, (0 : Fin m → ℝ)) := by
    rw [← hsorbit]
    exact Φ.left_inv' hsΦ
  rw [hinv] at htnear
  have hpoint : cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hstart :
    cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    hpoint.symm ▸ Metric.ball_subset_closedBall htnear
  have hfinish : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    Metric.ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hflow := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox 0 hstart hfinish
  rw [hpoint, hsorbit, ← F.map_add] at hflow
  exact ⟨r, δ, T, T - cubicAxisClock a s + t, hr, hδ, hbox, hslice, hflow.symm⟩

private theorem Degree.SmoothODE.exists_smooth_fixedPoint_germ {P E : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × E → E} {p : P} {x : E} (hF : ContDiffAt ℝ ∞ F (p, x)) (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) :
    ∃ g : P → E,
      g p = x ∧
        ContDiffAt ℝ ∞ g p ∧
          (∀ᶠ q in 𝓝 p, F (q, g q) = g q) ∧ ∀ᶠ v in 𝓝 (p, x), F v = v.2 ↔ g v.1 = v.2 := by
  let G : P × E → E := fun v => v.2 - F v
  have hG : ContDiffAt ℝ ∞ G (p, x) := contDiffAt_snd.sub hF
  have hdG : HasFDerivAt G (ContinuousLinearMap.snd ℝ P E - fderiv ℝ F (p, x)) (p, x) :=
    (ContinuousLinearMap.snd ℝ P E).hasFDerivAt.sub (hF.differentiableAt (by simp)).hasFDerivAt
  have hpartial :
    (fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E) =
      1 - (fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E) := by
    rw [hdG.fderiv]
    ext z
    rfl
  have hinv : ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hpartial]
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hsmall
    exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
  let g := hG.implicitFunction (by simp) hinv
  have hgp : g p = x := hG.implicitFunction_apply_self (by simp) hinv
  have hg : ContDiffAt ℝ ∞ g p := hG.contDiffAt_implicitFunction (by simp) hinv
  refine ⟨g, hgp, hg, ?_, ?_⟩
  · filter_upwards [hG.eventually_apply_implicitFunction (by simp) hinv] with q hq
    change g q - F (q, g q) = x - F (p, x) at hq
    rw [hfix, sub_self] at hq
    exact (sub_eq_zero.mp hq).symm
  · filter_upwards [hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv] with v hv
    change (v.2 - F v = x - F (p, x) ↔ g v.1 = v.2) at hv
    rw [hfix, sub_self, sub_eq_zero] at hv
    exact eq_comm.trans hv

private theorem
    Degree.SmoothODE.contDiffAt_of_continuous_fixedPoint {P E : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × E → E} {p : P} {x : E} (hF : ContDiffAt ℝ ∞ F (p, x)) (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) {g : P → E}
    (hg : ContinuousAt g p) (hgp : g p = x) (heq : ∀ᶠ q in 𝓝 p, F (q, g q) = g q) :
    ContDiffAt ℝ ∞ g p := by
  obtain ⟨ψ, -, hψ, -, huniq⟩ := exists_smooth_fixedPoint_germ hF hfix hsmall
  have hgraph : Filter.Tendsto (fun q => (q, g q)) (𝓝 p) (𝓝 (p, x)) := by
    have hh : Filter.Tendsto (fun q => (q, g q)) (𝓝 p) (𝓝 (p, g p)) := continuousAt_id.prodMk hg
    rwa [hgp] at hh
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hgraph huniq, heq] with q hq hfixq
  exact ((hq.mp hfixq).symm)

private theorem Degree.SmoothODE.exists_smooth_fixedPoint_neighborhood {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : P × E → E} {p : P} {x : E} (hF : ContDiff ℝ ∞ F)
    (hfix : F (p, x) = x)
    (hsmall : ‖(fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)‖ < 1) :
    ∃ (U : Set P) (g : P → E),
      IsOpen U ∧ p ∈ U ∧ g p = x ∧ ContDiffOn ℝ ∞ g U ∧ ∀ q ∈ U, F (q, g q) = g q := by
  obtain ⟨g, hgp, hg, heq, -⟩ := exists_smooth_fixedPoint_germ hF.contDiffAt hfix hsmall
  let A (v : P × E) := (fderiv ℝ F v).comp (ContinuousLinearMap.inr ℝ P E)
  have hA : Continuous A := (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  have hgraph : ContinuousAt (fun q => (q, g q)) p := continuousAt_id.prodMk hg.continuousAt
  have hn : ContinuousAt (fun q => ‖A (q, g q)‖) p := (hA.continuousAt.comp hgraph).norm
  have hbase : ‖A (p, g p)‖ < 1 := by simpa only [hgp, A] using hsmall
  have hsmall' : ∀ᶠ q in 𝓝 p, ‖A (q, g q)‖ < 1 := hn (eventually_lt_nhds hbase)
  have hg₁ : ContDiffAt ℝ 1 g p := hg.of_le (by simp)
  have hcont : ∀ᶠ q in 𝓝 p, ContinuousAt g q :=
    (hg₁.eventually (by simp)).mono (fun _ h => h.continuousAt)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp ((heq.and hsmall').and hcont)
  refine ⟨U, g, hU, hpU, hgp, ?_, fun q hq => (hUsub hq).1.1⟩
  intro q hq
  apply
    (contDiffAt_of_continuous_fixedPoint hF.contDiffAt (hUsub hq).1.1 (hUsub hq).1.2 (hUsub hq).2
        rfl ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds hq] with r hr
  exact (hUsub hr).1.1

private def Degree.SmoothODE.pathOperator {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
      map_add' := by intro u v; ext t; exact map_add (A t) (u t) (v t)
      map_smul' := by intro r u; ext t; exact map_smul (A t) r (u t) } ‖A‖
    (by
      intro u
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact
        ((A t).le_opNorm (u t)).trans
          (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _)
            (norm_nonneg _)))

private theorem Degree.SmoothODE.norm_pathOperator_le {K E F : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : C(K, E →L[ℝ] F)) : ‖pathOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact
    ((A t).le_opNorm (u t)).trans
      (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

private def Degree.SmoothODE.pathOperatorCLM {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := pathOperator
      map_add' := by intro A B; ext u t; rfl
      map_smul' := by intro r A; ext u t; rfl } 1
    (by
      intro A
      change ‖pathOperator A‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact norm_pathOperator_le A)

private theorem
    Degree.SmoothODE.exists_quadratic_remainder_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (R : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ x y : E, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdcont : Continuous (fderiv ℝ (fderiv ℝ f)) := hdf.continuous_fderiv (by simp)
  obtain ⟨C₀, hC₀⟩ :=
    (ProperSpace.isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hdcont.continuousOn
  let C := Max.max C₀ 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (z : E) (hz : z ∈ Metric.closedBall (0 : E) R) : ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C := by
    exact (hC₀ z hz).trans (by dsimp [C]; linarith [le_max_left C₀ 0])
  have hlip {x z : E} (hx : x ∈ Metric.closedBall (0 : E) R)
    (hz : z ∈ Metric.closedBall (0 : E) R) : ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖z - x‖ :=
    (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf.differentiable (by simp) z) hbound hx hz
  refine ⟨C, hC, ?_⟩
  intro x y hx hy
  have hxR : x ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hyR : y ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hseg : segment ℝ x y ⊆ Metric.closedBall (0 : E) R :=
    (convex_closedBall _ _).segment_subset hxR hyR
  have hdist : segment ℝ x y ⊆ Metric.closedBall x ‖y - x‖ := by
    apply (convex_closedBall x ‖y - x‖).segment_subset
    · exact Metric.mem_closedBall_self (norm_nonneg _)
    · simp only [Metric.mem_closedBall, dist_eq_norm, le_refl]
  have hh :=
    (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ => hf.differentiable (by simp) z)
      (fun z hz =>
        (hlip hxR (hseg hz)).trans
          (mul_le_mul_of_nonneg_left
            (show ‖z - x‖ ≤ ‖y - x‖ from by
              simpa only [Metric.mem_closedBall, dist_eq_norm] using hdist hz)
            hC.le))
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using hh

private def
    Degree.SmoothODE.pathDerivative {K E F : Type*} [TopologicalSpace K] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f)
    (u : C(K, E)) : C(K, E →L[ℝ] F) :=
  ⟨fun t => fderiv ℝ f (u t), (hf.continuous_fderiv (by simp)).comp u.continuous⟩

private theorem
    Degree.SmoothODE.hasFDerivAt_pathPostcomposition {K E F : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    HasFDerivAt (fun v : C(K, E) => f.comp v) (pathOperator (pathDerivative f hf u)) u := by
  obtain ⟨C, hC, hrem⟩ := exists_quadratic_remainder_bound hf (‖u‖ + 1)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let δ := Min.min 1 (ε / C)
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε hC)
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, E)) hδ] with h hh
  have hhnorm : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hhnorm (min_le_left _ _)
  have hhε : C * ‖h‖ ≤ ε := by
    have hhdiv : ‖h‖ < ε / C := lt_of_lt_of_le hhnorm (min_le_right _ _)
    have hh' := (lt_div_iff₀ hC).mp hhdiv
    nlinarith
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro t
  change ‖f (u t + h t) - f (u t) - fderiv ℝ f (u t) (h t)‖ ≤ ε * ‖h‖
  have hxu : ‖u t‖ ≤ ‖u‖ + 1 := (u.norm_coe_le_norm t).trans (by linarith)
  have hyu : ‖u t + h t‖ ≤ ‖u‖ + 1 :=
    (norm_add_le _ _).trans (by linarith [u.norm_coe_le_norm t, h.norm_coe_le_norm t])
  have hr := hrem (u t) (u t + h t) hxu hyu
  simp only [add_sub_cancel_left] at hr
  calc
    _ ≤ C * ‖h t‖ ^ 2 := hr
    _ ≤ C * ‖h‖ ^ 2 :=
      (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h.norm_coe_le_norm t)) hC.le)
    _ ≤ ε * ‖h‖ := by
      have hh' := mul_le_mul_of_nonneg_right hhε (norm_nonneg h)
      simpa only [pow_two, mul_assoc] using hh'

private theorem Degree.SmoothODE.fderiv_pathPostcomposition {K E F : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    fderiv ℝ (fun v : C(K, E) => f.comp v) u = pathOperator (pathDerivative f hf u) :=
  (hasFDerivAt_pathPostcomposition f hf u).fderiv

private theorem Degree.SmoothODE.contDiff_pathPostcomposition_nat {K : Type v} [TopologicalSpace K]
    [CompactSpace K] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F],
      ∀ (f : C(E, F)), ContDiff ℝ ∞ f → ContDiff ℝ n (fun w : C(K, E) => f.comp w) := by
  induction n with
  | zero =>
    intro F _ _ f _
    exact contDiff_zero.mpr f.continuous_postcomp
  | succ n ih =>
    intro F _ _ f hf
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun w => (hasFDerivAt_pathPostcomposition f hf w).differentiableAt, by simp, ?_⟩
    let df : C(E, E →L[ℝ] F) := ⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩
    have hdf : ContDiff ℝ ∞ df := hf.fderiv_right (by simp)
    have hi := ih df hdf
    have heq : fderiv ℝ (fun w : C(K, E) => f.comp w) = fun w => pathOperator (df.comp w) := by
      funext w
      rw [fderiv_pathPostcomposition f hf w]
      rfl
    rw [heq]
    exact (pathOperatorCLM (K := K) (E := E) (F := F)).contDiff.comp hi

private theorem Degree.SmoothODE.contDiff_pathPostcomposition {K : Type v} [TopologicalSpace K]
    [CompactSpace K] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : C(E, F)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun w : C(K, E) => f.comp w) :=
  contDiff_infty.mpr (fun n => contDiff_pathPostcomposition_nat n f hf)

private abbrev Degree.SmoothODE.PathTime :=
  Set.Icc (-2 : ℝ) 2

private def Degree.SmoothODE.pathClamp : ℝ → PathTime :=
  Set.projIcc (-2) 2 (by norm_num)

private theorem Degree.SmoothODE.continuous_pathClamp : Continuous pathClamp :=
  continuous_projIcc

private def
    Degree.SmoothODE.pathExtend {E : Type*} [NormedAddCommGroup E] (u : C(PathTime, E)) : ℝ → E :=
  u ∘ pathClamp

private theorem Degree.SmoothODE.continuous_pathExtend {E : Type*} [NormedAddCommGroup E]
    (u : C(PathTime, E)) : Continuous (pathExtend u) :=
  u.continuous.comp continuous_pathClamp

private def Degree.SmoothODE.pathPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (u : C(PathTime, E)) : C(PathTime, E) :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s,
    (intervalIntegral.differentiable_integral_of_continuous
          (continuous_pathExtend u)).continuous.comp
      continuous_subtype_val⟩

private theorem Degree.SmoothODE.norm_pathPrimitive_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (u : C(PathTime, E)) : ‖pathPrimitive u‖ ≤ 2 * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg u))).mpr
  intro t
  have hh :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ)) (f :=
      pathExtend u) (fun s _ => u.norm_coe_le_norm (pathClamp s))
  have ht : |(t : ℝ)| ≤ 2 := abs_le.mpr t.property
  simp only [sub_zero] at hh
  change ‖∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s‖ ≤ 2 * ‖u‖
  simpa only [sub_zero, mul_comm] using hh.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg u))

private def Degree.SmoothODE.pathPrimitiveCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] : C(PathTime, E) →L[ℝ] C(PathTime, E) :=
  LinearMap.mkContinuous
    { toFun := pathPrimitive
      map_add' := by
        intro u v
        ext t
        change
          (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s + pathExtend v s) =
            (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s) + (∫ s in (0 : ℝ)..(t : ℝ), pathExtend v s)
        exact
          intervalIntegral.integral_add ((continuous_pathExtend u).intervalIntegrable _ _)
            ((continuous_pathExtend v).intervalIntegrable _ _)
      map_smul' := by
        intro r u
        ext t
        change
          (∫ s in (0 : ℝ)..(t : ℝ), r • pathExtend u s) =
            r • (∫ s in (0 : ℝ)..(t : ℝ), pathExtend u s)
        exact intervalIntegral.integral_smul r (pathExtend u) }
    2 (fun u => norm_pathPrimitive_le u)

private theorem Degree.SmoothODE.hasDerivAt_pathPrimitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (u : C(PathTime, E)) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, pathExtend u s) (pathExtend u t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_pathExtend u).intervalIntegrable _ _)
    (continuous_pathExtend u).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_pathExtend u).continuousAt

private def Degree.SmoothODE.picardPathMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (v : C(E, E)) (q : (E × ℝ) × C(PathTime, E)) : C(PathTime, E) :=
  ContinuousMap.const PathTime q.1.1 + q.1.2 • pathPrimitiveCLM (v.comp q.2)

private theorem Degree.SmoothODE.contDiff_picardPathMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (picardPathMap v) := by
  exact
    ((ContinuousLinearMap.const ℝ PathTime : E →L[ℝ] C(PathTime, E)).contDiff.comp
          contDiff_fst.fst).add
      (contDiff_fst.snd.smul
        ((pathPrimitiveCLM (E := E)).contDiff.comp
          ((contDiff_pathPostcomposition v hv).comp contDiff_snd)))

private theorem
    Degree.SmoothODE.picardPathMap_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (v : C(E, E)) (x : E) (u : C(PathTime, E)) :
    picardPathMap v ((x, 0), u) = ContinuousMap.const PathTime x := by
  simp only [picardPathMap, zero_smul, add_zero]

private theorem Degree.SmoothODE.picardPathMap_partial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E)
    (u : C(PathTime, E)) :
    (fderiv ℝ (picardPathMap v) ((x, 0), u)).comp
        (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E)) =
      0 := by
  have hQ := contDiff_picardPathMap v hv
  have hd :=
    (hQ.differentiable (by simp) ((x, 0), u)).hasFDerivAt.comp u
      ((hasFDerivAt_const (x, (0 : ℝ)) u).prodMk (hasFDerivAt_id u))
  change
    HasFDerivAt (fun w => picardPathMap v ((x, 0), w))
      ((fderiv ℝ (picardPathMap v) ((x, 0), u)).comp
        (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E)))
      u at hd
  have he : (fun w => picardPathMap v ((x, 0), w)) = fun _ => ContinuousMap.const PathTime x :=
    funext (picardPathMap_zero v x)
  rw [he] at hd
  exact hd.unique (hasFDerivAt_const (ContinuousMap.const PathTime x) u)

private theorem Degree.SmoothODE.exists_smooth_picard_paths {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ∃ (U : Set (E × ℝ)) (u : E × ℝ → C(PathTime, E)),
      IsOpen U ∧
        (x, 0) ∈ U ∧
          u (x, 0) = ContinuousMap.const PathTime x ∧
            ContDiffOn ℝ ∞ u U ∧
              ∀ q ∈ U,
                ∀ t : PathTime,
                  u q t = q.1 + q.2 • (∫ s in (0 : ℝ)..(t : ℝ), v (u q (pathClamp s))) := by
  have hsmall :
    ‖(fderiv ℝ (picardPathMap v) ((x, 0), ContinuousMap.const PathTime x)).comp
          (ContinuousLinearMap.inr ℝ (E × ℝ) C(PathTime, E))‖ <
      1 := by
    rw [picardPathMap_partial_zero v hv x, norm_zero]
    exact zero_lt_one
  obtain ⟨U, u, hU, hx, hu, hcont, hfix⟩ :=
    exists_smooth_fixedPoint_neighborhood (contDiff_picardPathMap v hv)
      (picardPathMap_zero v x (ContinuousMap.const PathTime x)) hsmall
  refine ⟨U, u, hU, hx, hu, hcont, ?_⟩
  intro q hq t
  have hh := congrArg (fun w : C(PathTime, E) => w t) (hfix q hq)
  exact hh.symm

private def Degree.SmoothODE.picardCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E)) (t : ℝ) : E :=
  p + τ • (∫ s in (0 : ℝ)..t, v (u (pathClamp s)))

private theorem
    Degree.SmoothODE.picardCurve_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E)) : picardCurve v p τ u 0 = p := by
  simp only [picardCurve, intervalIntegral.integral_same, smul_zero, add_zero]

private theorem Degree.SmoothODE.hasDerivAt_picardCurve {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E))
    (t : ℝ) : HasDerivAt (picardCurve v p τ u) (τ • v (u (pathClamp t))) t :=
  ((hasDerivAt_pathPrimitive (v.comp u) t).const_smul τ).const_add p

private theorem
    Degree.SmoothODE.picardCurve_eq_path {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : C(E, E)) {p : E} {τ : ℝ} {u : C(PathTime, E)}
    (heq : ∀ t : PathTime, u t = p + τ • (∫ s in (0 : ℝ)..(t : ℝ), v (u (pathClamp s)))) {t : ℝ}
    (ht : t ∈ Set.Icc (-2 : ℝ) 2) : picardCurve v p τ u t = u (pathClamp t) := by
  have hc : pathClamp t = ⟨t, ht⟩ := Set.projIcc_of_mem _ ht
  rw [hc]
  exact (heq ⟨t, ht⟩).symm

private theorem
    Degree.SmoothODE.hasDerivAt_picardCurve_of_fixedPoint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) {p : E} {τ : ℝ} {u : C(PathTime, E)}
    (heq : ∀ t : PathTime, u t = p + τ • (∫ s in (0 : ℝ)..(t : ℝ), v (u (pathClamp s)))) {t : ℝ}
    (ht : t ∈ Set.Icc (-2 : ℝ) 2) :
    HasDerivAt (picardCurve v p τ u) (τ • v (picardCurve v p τ u t)) t := by
  rw [picardCurve_eq_path v heq ht]
  exact hasDerivAt_picardCurve v p τ u t

private theorem Degree.SmoothODE.exists_smooth_picard_endpoints {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ∃ (U : Set (E × ℝ)) (u : E × ℝ → C(PathTime, E)) (g : E × ℝ → E),
      IsOpen U ∧
        (x, 0) ∈ U ∧
          u (x, 0) = ContinuousMap.const PathTime x ∧
            ContDiffOn ℝ ∞ u U ∧
              ContDiffOn ℝ ∞ g U ∧
                (∀ q, g q = u q ⟨1, by norm_num⟩) ∧
                  ∀ q ∈ U,
                    (picardCurve v q.1 q.2 (u q) 0 = q.1) ∧
                      (picardCurve v q.1 q.2 (u q) 1 = g q) ∧
                        (∀ t ∈ Set.Icc (-2 : ℝ) 2,
                            picardCurve v q.1 q.2 (u q) t = u q (pathClamp t)) ∧
                          ∀ t ∈ Set.Icc (-2 : ℝ) 2,
                            HasDerivAt (picardCurve v q.1 q.2 (u q))
                              (q.2 • v (picardCurve v q.1 q.2 (u q) t)) t := by
  obtain ⟨U, u, hU, hx, hux, hu, heq⟩ := exists_smooth_picard_paths v hv x
  let g (q : E × ℝ) := u q ⟨1, by norm_num⟩
  let L : C(PathTime, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (⟨1, by norm_num⟩ : PathTime)
  have hg : ContDiffOn ℝ ∞ g U := L.contDiff.comp_contDiffOn hu
  refine ⟨U, u, g, hU, hx, hux, hu, hg, fun _ => rfl, ?_⟩
  intro q hq
  refine
    ⟨picardCurve_zero v _ _ _, ?_, fun t ht => picardCurve_eq_path v (heq q hq) ht, fun t ht =>
      hasDerivAt_picardCurve_of_fixedPoint v (heq q hq) ht⟩
  have hh := picardCurve_eq_path v (heq q hq) (t := 1) (by norm_num)
  have hc : pathClamp 1 = (⟨1, by norm_num⟩ : PathTime) := Set.projIcc_of_mem _ (by norm_num)
  exact hh.trans (congrArg (u q) hc)

private theorem Degree.SmoothODE.ordinary_curve_eqOn_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E → E} (hv : ContDiff ℝ 1 v) {γ η : ℝ → E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo a b) (hγ : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (v (γ t)) t)
    (hη : ∀ t ∈ Set.Ioo a b, HasDerivAt η (v (η t)) t) (heq : γ t₀ = η t₀) :
    Set.EqOn γ η (Set.Ioo a b) := by
  let V : (x : E) → TangentSpace 𝓘(ℝ, E) x := fun x => v x
  have hV :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceDiffeomorph 𝓘(ℝ, E) 1).symm.contMDiff.comp
      (contDiff_id.prodMk hv).contMDiff
  have hγM : IsMIntegralCurveOn γ V (Set.Ioo a b) := by
    intro t ht
    exact (hγ t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hηM : IsMIntegralCurveOn η V (Set.Ioo a b) := by
    intro t ht
    exact (hη t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hV hγM hηM heq

private theorem
    Degree.SmoothODE.picard_endpoint_eq_local_solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) {p : E} {τ ε : ℝ} (hτ : |τ| < ε / 2)
    {u : C(PathTime, E)} {g : E} (hzero : picardCurve v p τ u 0 = p)
    (hend : picardCurve v p τ u 1 = g)
    (hcurve :
      ∀ t ∈ Set.Icc (-2 : ℝ) 2,
        HasDerivAt (picardCurve v p τ u) (τ • v (picardCurve v p τ u t)) t)
    {α : ℝ → E} (hαzero : α 0 = p) (hα : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (v (α t)) t) :
    g = α τ := by
  have hscaled : ContDiff ℝ 1 (fun y : E => τ • v y) := contDiff_const.smul (hv.of_le (by simp))
  have hη (r : ℝ) (hr : r ∈ Set.Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun s : ℝ => α (s * τ)) (τ • v (α (r * τ))) r := by
    have hrt : r * τ ∈ Set.Ioo (-ε) ε := by
      apply abs_lt.mp
      rw [abs_mul]
      have hrabs : |r| ≤ 2 := (abs_lt.mpr hr).le
      have hh := mul_le_mul_of_nonneg_right hrabs (abs_nonneg τ)
      linarith
    have hd := (hα (r * τ) hrt).scomp r ((hasDerivAt_id r).mul_const τ)
    change HasDerivAt (fun s : ℝ => α (s * τ)) ((1 * τ) • v (α (r * τ))) r at hd
    simpa only [one_mul] using hd
  have heq :=
    ordinary_curve_eqOn_of_contDiff hscaled (show (0 : ℝ) ∈ Set.Ioo (-2) 2 by norm_num)
      (fun t ht => hcurve t ⟨ht.1.le, ht.2.le⟩) hη
      (by simpa only [MulZeroClass.zero_mul] using hzero.trans hαzero.symm)
  have hh := heq (x := 1) (by norm_num)
  simpa only [hend, one_mul] using hh

private theorem Degree.SmoothODE.contDiffAt_ordinary_localFlow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (v : C(E, E)) (hv : ContDiff ℝ ∞ v) {P : Set E}
    (hP : IsOpen P) {x : E} (hx : x ∈ P) {ε : ℝ} (hε : 0 < ε) {H : E × ℝ → E}
    (hinit : ∀ p ∈ P, H (p, 0) = p)
    (hH : ∀ p ∈ P, ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s : ℝ => H (p, s)) (v (H (p, t))) t) :
    ContDiffAt ℝ ∞ H (x, 0) := by
  obtain ⟨U, u, g, hU, hxU, -, -, hg, -, hpaths⟩ := exists_smooth_picard_endpoints v hv x
  apply (hg.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
  have hsmall : Set.Ioo (-(ε / 2)) (ε / 2) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (neg_lt_zero.mpr (half_pos hε)) (half_pos hε)
  filter_upwards [hU.mem_nhds hxU, prod_mem_nhds (hP.mem_nhds hx) hsmall] with q hq hqsmall
  obtain ⟨hzero, hend, -, hcurve⟩ := hpaths q hq
  exact
    (picard_endpoint_eq_local_solution v hv (abs_lt.mpr hqsmall.2) hzero hend hcurve
        (hinit q.1 hqsmall.1) (hH q.1 hqsmall.1)).symm

private theorem Smale.DiskFraming.starConvex_thickening_zero {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {K : Set D} (hK : StarConvex ℝ (0 : D) K) (δ : ℝ) :
    StarConvex ℝ (0 : D) (Metric.thickening δ K) := by
  rw [starConvex_zero_iff]
  intro x hx a ha₀ ha₁
  obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.mp hx
  apply Metric.mem_thickening_iff.mpr
  refine ⟨a • z, hK.smul_mem hz ha₀ ha₁, ?_⟩
  calc
    Dist.dist (a • x) (a • z) = a * Dist.dist x z := by
      simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha₀]
    _ ≤ Dist.dist x z := (mul_le_of_le_one_left dist_nonneg ha₁)
    _ < δ := hxz

private theorem
    Smale.DiskFraming.exists_smooth_map_into_neighborhood {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] {K U : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : D → D,
      ContDiff ℝ ∞ ρ ∧
        Set.MapsTo ρ Set.univ U ∧ ∃ V : Set D, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ Set.EqOn ρ id V := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  let W := Metric.thickening δ K
  have hW : IsOpen W := Metric.isOpen_thickening
  have hKW : K ⊆ W := Metric.self_subset_thickening hδ K
  have hstarW : StarConvex ℝ (0 : D) W := starConvex_thickening_zero hstar δ
  obtain ⟨L, hL, hKL, hLW⟩ := exists_compact_between hK hW hKW
  obtain ⟨β, hβ, hβrange, hβsupport, hβone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, D)) (n := (⊤ : ℕ∞)) hW hL.isClosed hLW
  let ρ : D → D := fun x => β x • x
  refine
    ⟨ρ, hβ.contDiff.smul contDiff_id, ?_, interior L, isOpen_interior, hKL, fun x hx =>
      hδU (hLW (interior_subset hx)), ?_⟩
  · intro x _
    have hb := hβrange (Set.mem_range_self x)
    by_cases hx : x ∈ W
    · exact hδU (hstarW.smul_mem hx hb.1 hb.2)
    · have hb0 : β x = 0 := by
        by_contra hn
        have hxs : x ∈ Function.support β := hn
        rw [hβsupport] at hxs
        exact hx hxs
      change β x • x ∈ U
      rw [hb0, zero_smul]
      exact hKU hz
  · intro x hx
    change β x • x = x
    rw [(hβone x).mp (interior_subset hx), one_smul]

private theorem
    Smale.exists_smooth_extension_near_starConvex {D G H N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    {f : D → N} {K U : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, D) J ∞ f U) :
    ∃ g : D → N,
      ContMDiff 𝓘(ℝ, D) J ∞ g ∧ ∃ V : Set D, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ Set.EqOn g f V := by
  obtain ⟨ρ, hρ, hρU, V, hV, hKV, hVU, hρid⟩ :=
    DiskFraming.exists_smooth_map_into_neighborhood hK hz hstar hU hKU
  refine ⟨f ∘ ρ, contMDiffOn_univ.mp (hf.comp hρ.contMDiff.contMDiffOn hρU), V, hV, hKV, hVU, ?_⟩
  intro x hx
  exact congrArg f (hρid hx)

private theorem Smale.exists_smooth_extension_near_point {D G H N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    {f : D → N} {U : Set D} {x₀ : D} (hf : ContMDiffOn 𝓘(ℝ, D) J ∞ f U) (hU : IsOpen U)
    (hx₀ : x₀ ∈ U) : ∃ g : D → N, ContMDiff 𝓘(ℝ, D) J ∞ g ∧ g =ᶠ[𝓝 x₀] f := by
  let shift : D → D := fun x => x + x₀
  have hshift : ContDiff ℝ ∞ shift := contDiff_id.add contDiff_const
  have hf' : ContMDiffOn 𝓘(ℝ, D) J ∞ (f ∘ shift) (shift ⁻¹' U) :=
    hf.comp hshift.contMDiff.contMDiffOn (fun _ hx => hx)
  have hzero : ({0} : Set D) ⊆ shift ⁻¹' U := by
    intro x hx
    have hx0 : x = 0 := hx
    subst x
    simpa only [shift, Set.mem_preimage, zero_add] using hx₀
  obtain ⟨g, hg, V, hV, h0V, _, heq⟩ :=
    exists_smooth_extension_near_starConvex isCompact_singleton (Set.mem_singleton 0)
      (starConvex_singleton (0 : D)) (hU.preimage hshift.continuous) hzero hf'
  let g' : D → N := fun x => g (x - x₀)
  have hg' : ContMDiff 𝓘(ℝ, D) J ∞ g' := hg.comp (contDiff_id.sub contDiff_const).contMDiff
  have htime : Filter.Tendsto (fun x : D => x - x₀) (𝓝 x₀) (𝓝 0) := by
    have htime' : Filter.Tendsto (fun x : D => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)) :=
      (continuous_id.sub continuous_const : Continuous (fun x : D => x - x₀)).continuousAt.tendsto
    rwa [sub_self] at htime'
  refine ⟨g', hg', ?_⟩
  filter_upwards [htime (hV.mem_nhds (h0V (Set.mem_singleton 0)))] with x hx
  change g (x - x₀) = f x
  simpa only [Function.comp_apply, shift, sub_add_cancel] using heq hx

private theorem Degree.SmoothODE.contDiffAt_local_field_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {v : E → E} {O P : Set E} (hv : ContDiffOn ℝ ∞ v O)
    (hO : IsOpen O) {x : E} (hxO : x ∈ O) (hP : IsOpen P) (hxP : x ∈ P) {ε : ℝ} (hε : 0 < ε)
    {H : E × ℝ → E} (hc : ContinuousAt H (x, 0)) (hinit : ∀ p ∈ P, H (p, 0) = p)
    (hH : ∀ p ∈ P, ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun s : ℝ => H (p, s)) (v (H (p, t))) t) :
    ContDiffAt ℝ ∞ H (x, 0) := by
  obtain ⟨w, hwM, heq⟩ := Smale.exists_smooth_extension_near_point hv.contMDiffOn hO hxO
  have hw : ContDiff ℝ ∞ w := contMDiff_iff_contDiff.mp hwM
  have hevent : ∀ᶠ q in 𝓝 (x, (0 : ℝ)), w (H q) = v (H q) := by
    have heq' : w =ᶠ[𝓝 (H (x, 0))] v := by rwa [hinit x hxP]
    exact hc heq'
  have hdom : P ×ˢ Set.Ioo (-ε) ε ∈ 𝓝 (x, (0 : ℝ)) :=
    prod_mem_nhds (hP.mem_nhds hxP) (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
  have hdom' : ∀ᶠ q in 𝓝 (x, (0 : ℝ)), q ∈ P ×ˢ Set.Ioo (-ε) ε := hdom
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.mp (hdom'.and hevent)
  have hrect (p : E) (hp : p ∈ Metric.ball x δ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
    (p, t) ∈ P ×ˢ Set.Ioo (-ε) ε ∧ w (H (p, t)) = v (H (p, t)) := by
    apply hsub
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hp, by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht⟩
  let W : C(E, E) := ⟨w, hw.continuous⟩
  apply contDiffAt_ordinary_localFlow W hw Metric.isOpen_ball (Metric.mem_ball_self hδ) hδ
  · intro p hp
    exact hinit p (hrect p hp 0 ⟨neg_lt_zero.mpr hδ, hδ⟩).1.1
  · intro p hp t ht
    have hh := hrect p hp t ht
    have hd := hH p hh.1.1 t hh.1.2
    change HasDerivAt (fun s => H (p, s)) (w (H (p, t))) t
    rw [hh.2]
    exact hd

private def MorseCancel.coordinateField {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) (z : E) : E :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm V z

private theorem
    MorseCancel.coordinateField_chart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) {x : M} (hx : x ∈ e.source) :
    coordinateField (V := V) e (e x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (V x) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₂ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₂
  have hi := ContinuousLinearMap.inverse_eq (he.symm_comp_deriv hx) h₂
  let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm (e' x)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e' x
  have hAB : A.inverse = B := hi
  have hvx : (show E from V (e'.symm (e' x))) = V x :=
    congrArg (fun y : M => (show E from V y)) (e'.left_inv hx)
  change A.inverse (V (e'.symm (e' x))) = B (V x)
  rw [hAB]
  exact congrArg B hvx

private theorem MorseCancel.contDiffOn_coordinateField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) :
    ContDiffOn ℝ ∞ (coordinateField (V := V) e) e.target := by
  apply contMDiffOn_vectorSpace_iff_contDiffOn.mp
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  intro z hz
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z).IsInvertible := ⟨he.symm.mfderiv hz, rfl⟩
  exact
    ((hV (e.symm z)).mpullback_vectorField_preimage
        ((e.symm.contMDiffOn z hz).contMDiffAt (e.open_target.mem_nhds hz)) hinv
        (by simp)).contMDiffWithinAt

private theorem MorseCancel.hasDerivAt_coordinate_integralCurve {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ} (ht : γ t ∈ e.source) :
    HasDerivAt (e ∘ γ) (coordinateField (V := V) e (e (γ t))) t := by
  have he :=
    ((e.contMDiffOn (γ t) ht).contMDiffAt (e.open_source.mem_nhds ht)).mdifferentiableAt (by simp)
  have hd := he.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (γ t) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) • coordinateField (V := V) e (e (γ t))
  rw [map_smul, coordinateField_chart e ht]
  rfl

private theorem Degree.SmoothODE.contMDiffAt_native_flow_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (p : M) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun q : M × ℝ => F q.2 q.1) (p, 0) := by
  let e := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz : e p ∈ e.target := e.map_source' hp
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e p :=
    (e.contMDiffOn p hp).contMDiffAt (e.open_source.mem_nhds hp)
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e p) :=
    (e.symm.contMDiffOn (e p) hz).contMDiffAt (e.open_target.mem_nhds hz)
  let C (q : E × ℝ) : M := F q.2 (e.symm q.1)
  let H (q : E × ℝ) : E := e (C q)
  have hC0 : C (e p, 0) = p := by
    change F 0 (e.symm (e p)) = p
    rw [F.map_zero_apply]
    exact e.left_inv' hp
  have hFC : Continuous (fun q : ℝ × M => F q.1 q.2) := F.continuous continuous_fst continuous_snd
  have hic : ContinuousAt (fun q : E × ℝ => e.symm q.1) (e p, 0) :=
    hi.continuousAt.comp_of_eq
      (show ContinuousAt (Prod.fst : E × ℝ → E) (e p, 0) from continuousAt_fst) rfl
  have hC : ContinuousAt C (e p, 0) := hFC.continuousAt.comp (continuousAt_snd.prodMk hic)
  have hHC : ContinuousAt H (e p, 0) := by
    have heC : ContinuousAt e (C (e p, 0)) := by rw [hC0]; exact he.continuousAt
    exact heC.comp hC
  have htarget : ∀ᶠ q : E × ℝ in 𝓝 (e p, 0), q.1 ∈ e.target :=
    continuousAt_fst (e.open_target.mem_nhds hz)
  have hstay : ∀ᶠ q : E × ℝ in 𝓝 (e p, 0), C q ∈ e.source := by
    apply hC
    rw [hC0]
    exact e.open_source.mem_nhds hp
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp (htarget.and hstay)
  have hrect (z : E) (hz' : z ∈ Metric.ball (e p) δ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
    z ∈ e.target ∧ C (z, t) ∈ e.source := by
    apply hδsub (y := (z, t))
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hz', by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht⟩
  have hinit (z : E) (hz' : z ∈ Metric.ball (e p) δ) : H (z, 0) = z := by
    change e (F 0 (e.symm z)) = z
    rw [F.map_zero_apply]
    exact e.right_inv' (hrect z hz' 0 ⟨neg_lt_zero.mpr hδ, hδ⟩).1
  have hODE (z : E) (hz' : z ∈ Metric.ball (e p) δ) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :
    HasDerivAt (fun s => H (z, s)) (MorseCancel.coordinateField (V := V) e (H (z, t))) t :=
    MorseCancel.hasDerivAt_coordinate_integralCurve e (hcurve (e.symm z)) (hrect z hz' t ht).2
  have hH : ContDiffAt ℝ ∞ H (e p, 0) :=
    contDiffAt_local_field_flow (MorseCancel.contDiffOn_coordinateField hV e) e.open_target hz
      Metric.isOpen_ball (Metric.mem_ball_self hδ) hδ hHC hinit hODE
  let A (q : M × ℝ) : E × ℝ := (e q.1, q.2)
  have hA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞ A (p, 0) := by
    apply (contMDiffAt_prod_module_iff A).mpr
    have hefst :
      ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (e ∘ (Prod.fst : M × ℝ → M)) (p, 0) :=
      he.comp (p, 0) contMDiffAt_fst
    exact ⟨hefst, contMDiffAt_snd⟩
  have hHA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (H ∘ A) (p, 0) :=
    hH.contMDiffAt.comp (p, 0) hA
  have hHA0 : (H ∘ A) (p, 0) = e p := congrArg e hC0
  have hi' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm ((H ∘ A) (p, 0)) := by
    rw [hHA0]
    exact hi
  apply (hi'.comp (p, 0) hHA).congr_of_eventuallyEq
  have hstart : ∀ᶠ q : M × ℝ in 𝓝 (p, 0), q.1 ∈ e.source :=
    continuousAt_fst (e.open_source.mem_nhds hp)
  have hfinish : ∀ᶠ q : M × ℝ in 𝓝 (p, 0), F q.2 q.1 ∈ e.source := by
    have hc : Continuous (fun q : M × ℝ => F q.2 q.1) :=
      F.continuous continuous_snd continuous_fst
    apply hc.continuousAt
    simpa only [F.map_zero_apply] using e.open_source.mem_nhds hp
  filter_upwards [hstart, hfinish] with q hq hFq
  have heq : e.symm (e q.1) = q.1 := e.left_inv' hq
  change F q.2 q.1 = e.symm (e (F q.2 (e.symm (e q.1))))
  rw [heq]
  exact (e.left_inv' hFq).symm

private theorem
    Degree.SmoothODE.exists_uniform_smalltime_contMDiff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (F : Flow ℝ M) (n : ℕ)
    (hzero :
      ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F t) := by
  let U : Set (M × ℝ) :=
    {q | ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun r : M × ℝ => F r.2 r.1) q}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    exact (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hq
  let T : Set ℝ := {t | ∀ p ∈ (Set.univ : Set M), (t, p) ∈ Prod.swap ⁻¹' U}
  have hT : IsOpen T :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact isCompact_univ (hU.preimage continuous_swap)
  have h0 : (0 : ℝ) ∈ T := fun p _ => hzero p
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0)
  refine ⟨ε, hε, ?_⟩
  intro t ht p
  have htT : t ∈ T :=
    hεsub (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
  have hj : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, t) :=
    htT p (Set.mem_univ p)
  have hι : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) n (fun x : M => (x, t)) p :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have hh := hj.comp p hι
  exact hh

private theorem Degree.SmoothODE.contMDiff_flow_time_of_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (F : Flow ℝ M) (n : ℕ)
    (hzero :
      ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, 0))
    (t : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F t) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_uniform_smalltime_contMDiff F n hzero
  let S : Set ℝ := {s | ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : Dist.dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Set.Ioo (-ε) ε := abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => F (u - s) (F s x)) = F u := by
      funext x
      rw [← F.map_add, sub_add_cancel]
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F u)
    rw [← heq]
    exact hc
  have hS : IsOpen S :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε)
        (fun u hu h =>
          hs
            (hstep h
              (by
                change Dist.dist u s < ε at hu
                rwa [dist_comm])))
  have h0 : (0 : ℝ) ∈ S := by
    have heq : F 0 = id := funext F.map_zero_apply
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F 0)
    rw [heq]
    exact contMDiff_id
  have hSuniv : S = Set.univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, h0⟩
  have ht : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
  exact ht

private theorem Degree.SmoothODE.contMDiff_joint_flow_of_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (F : Flow ℝ M) (n : ℕ)
    (hzero :
      ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) (p, 0)) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) := by
  intro q
  let A (r : M × ℝ) := (F q.2 r.1, r.2 - q.2)
  have hA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) n A q :=
    ((contMDiff_flow_time_of_zero F n hzero q.2).contMDiffAt.comp q contMDiffAt_fst).prodMk
      (contMDiffAt_snd.sub contMDiffAt_const)
  have hG : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun r : M × ℝ => F r.2 r.1) (A q) := by
    simpa only [A, sub_self] using hzero (F q.2 q.1)
  have hc := hG.comp q hA
  have heq : ((fun r : M × ℝ => F r.2 r.1) ∘ A) = (fun r : M × ℝ => F r.2 r.1) := by
    funext r
    change F (r.2 - q.2) (F q.2 r.1) = F r.2 r.1
    rw [← F.map_add, sub_add_cancel]
  exact heq ▸ hc

private theorem Degree.SmoothODE.contMDiff_native_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] [FiniteDimensional ℝ E] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun q : M × ℝ => F q.2 q.1) :=
  contMDiff_infty.mpr
    (fun n =>
      contMDiff_joint_flow_of_zero F n
        (fun p => contMDiffAt_infty.mp (contMDiffAt_native_flow_zero hV F hcurve p) n))

private def Degree.SmoothODE.nativeFlowTimeDiffeomorph {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) (t : ℝ) : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M
    where
  toFun := F t
  invFun := F (-t)
  left_inv x := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  right_inv x := by rw [← F.map_add, add_neg_cancel, F.map_zero_apply]
  contMDiff_toFun := hs t
  contMDiff_invFun := hs (-t)

private theorem Degree.SmoothODE.mfderiv_flow_time_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) (x : M) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x (V x) = V (F t x) := by
  have hd := ((hs t).mdifferentiableAt (by simp) (x := F 0 x)).hasMFDerivAt.comp 0 (hF x 0)
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (F t ∘ fun s => F s x) 0
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) (F 0 x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (V (F 0 x)))) at hd
  rw [F.map_zero_apply] at hd
  have hcomm : (F t ∘ fun s => F s x) = (fun s => F s (F t x)) := by
    funext s
    change F t (F s x) = F s (F t x)
    rw [← F.map_add, ← F.map_add, add_comm]
  rw [hcomm] at hd
  have hd' := hF (F t x) 0
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => F s (F t x)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (F 0 (F t x)))) at hd'
  rw [F.map_zero_apply] at hd'
  have hh := hd.mfderiv.symm.trans hd'.mfderiv
  have hv := congrArg (fun A : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F t x) => A 1) hh
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x ((1 : ℝ) • V x) = (1 : ℝ) • V (F t x) at hv
  simpa only [one_smul] using hv

private def Degree.SmoothODE.nativeFlowTimeDiffeomorph_of_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) :
    M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  nativeFlowTimeDiffeomorph F
    (fun _ => (contMDiff_native_flow hV F hF).comp (contMDiff_id.prodMk contMDiff_const)) t

private theorem Degree.SmoothODE.mpullback_flow_time {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) (x : M) :
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) V x = V x := by
  let D := nativeFlowTimeDiffeomorph F hs t
  let e := D.toPartialDiffeomorph
  have hdiff : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.mdifferentiableOn (by simp), e.symm.mdifferentiableOn (by simp)⟩
  have hi : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x).IsInvertible :=
    ⟨hdiff.mfderiv (Set.mem_univ x), rfl⟩
  rw [VectorField.mpullback_apply, ← mfderiv_flow_time_field F hs hF t x]
  exact hi.inverse_apply_self (V x)

private theorem Degree.SmoothODE.partialChartField_flow_shift {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (Φ : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞) (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (W : B → B)
    (hmodel : ∀ x ∈ Φ.target, V x = Smale.FlowConstruction.partialChartField Φ.symm W x) (t : ℝ)
    {x : M} (hx : x ∈ (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).target) :
    V x =
      Smale.FlowConstruction.partialChartField
        (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).symm W x := by
  have hxΦ : F (-t) x ∈ Φ.target := hx.2
  have hdiff : Φ.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, B) :=
    ⟨Φ.symm.mdifferentiableOn (by simp), Φ.mdifferentiableOn (by simp)⟩
  have hinv : (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, B) Φ.symm Set.univ (F (-t) x)).IsInvertible := by
    rw [mfderivWithin_univ]
    exact ⟨hdiff.mfderiv hxΦ, rfl⟩
  have hh :=
    VectorField.mpullbackWithin_comp_of_left (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, B)) (f :=
      F (-t)) (g := (Φ.symm : M → B)) (V := fun y => (NormedSpace.fromTangentSpace y).symm (W y))
      (s := Set.univ) (t := Set.univ)
      ((hs (-t)).mdifferentiableAt (by simp)).mdifferentiableWithinAt (Set.mapsTo_univ _ _)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hinv
  simp only [VectorField.mpullbackWithin_univ] at hh
  change
    V x =
      VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, B) (Φ.symm ∘ F (-t))
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) x
  rw [hh, VectorField.mpullback_apply]
  change
    V x =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F (-t)) x).inverse
        (Smale.FlowConstruction.partialChartField Φ.symm W (F (-t) x))
  rw [← hmodel _ hxΦ]
  exact (mpullback_flow_time F hs hF (-t) x).symm

private theorem Degree.SmoothODE.flow_shifted_chart_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] (Φ : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞) (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) (t : ℝ) :
    (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).source = Φ.source := by
  ext p
  change p ∈ Φ.source ∧ Φ p ∈ Set.univ ↔ p ∈ Φ.source
  simp

private theorem
    MorseCancel.exists_clock_normalized_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcrit : c ^ 2 = a ^ 2) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (r δ T : ℝ),
      Ψ.source = Φ.source ∧
        Ψ (c, 0) = Φ (c, 0) ∧
          0 < r ∧
            0 < δ ∧
              Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source ∧
                (∀ z : Fin m → ℝ,
                    ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
                  (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y) ∧
                    (∀ t : ℝ,
                        cubicFlowCylinder σ a (0, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
                          Ψ (cubicFlowCylinder σ a (0, t)) = F t x) ∧
                      ∃ d : ℝ, ∀ z : Model m, Ψ z = F d (Φ z) := by
  have hV₁ := hV.of_le (by simp : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω))
  obtain ⟨r, δ, T, τ, hr, hδ, hbox, hslice, hcenter⟩ :=
    exists_endpoint_slice_on_actual_orbit σ ha Φ hV₁ hmodel F hF hc hcΦ x hlim htail
  have hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t) := fun t =>
    (Degree.SmoothODE.contMDiff_native_flow hV F hF).comp (contMDiff_id.prodMk contMDiff_const)
  let Ψ := Φ.trans (Degree.SmoothODE.nativeFlowTimeDiffeomorph F hs (T - τ)).toPartialDiffeomorph
  have hsource : Ψ.source = Φ.source := Degree.SmoothODE.flow_shifted_chart_source Φ F hs (T - τ)
  have hΨmodel : ∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y := by
    intro y hy
    exact
      Degree.SmoothODE.partialChartField_flow_shift Φ F hs hF (cubicDescent σ (-(a ^ 2))) hmodel
        (T - τ) hy
  have hzero : V (Φ (c, 0)) = 0 := by
    rw [hmodel _ (Φ.map_source' hcΦ)]
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    have hw : cubicDescent σ (-(a ^ 2)) (Φ.symm (Φ (c, 0))) = 0 := by
      rw [hinv]
      ext i <;> simp [cubicDescent, hcrit]
    unfold nativeCubicDescent Smale.FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, hw, map_zero, map_zero]
  have hvalue : Ψ (c, 0) = Φ (c, 0) :=
    Smale.FlowConstruction.flow_fixed_of_zero hV₁ F hF hzero (T - τ)
  have hΨbox : Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source := hsource.symm ▸ hbox
  have hbase : Ψ (cubicFlowCylinder σ a (0, T)) = F T x := by
    change F (T - τ) (Φ (cubicFlowCylinder σ a (0, T))) = F T x
    rw [hcenter, ← F.map_add, sub_add_cancel]
  refine ⟨Ψ, r, δ, T, hsource, hvalue, hr, hδ, hΨbox, hslice, hΨmodel, ?_, T - τ, fun _ => rfl⟩
  intro t ht
  have hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r :=
    Metric.ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hh := native_cubic_flow_between_box_points σ ha Ψ hV₁ hΨmodel F hF hΨbox 0 hstart ht
  rw [hbase, ← F.map_add, sub_add_cancel] at hh
  exact hh.symm

public
theorem MorseCancel.flow_time_atTop_limit_iff {M : Type*} [TopologicalSpace M] (F : Flow ℝ M)
    (d : ℝ) (x p : M) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atTop (𝓝 p) ↔
      Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) := by
  have hshift {x p : M} (d : ℝ) (h : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atTop (𝓝 p) := by
    simpa only [Function.comp_def, id_eq, F.map_add] using
      h.comp (Filter.tendsto_atTop_add_const_right Filter.atTop d Filter.tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

private theorem
    MorseCancel.flow_time_atBot_limit_iff {M : Type*} [TopologicalSpace M] (F : Flow ℝ M)
    (d : ℝ) (x p : M) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atBot (𝓝 p) ↔
      Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) := by
  have hshift {x p : M} (d : ℝ) (h : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) :
    Filter.Tendsto (fun t => F t (F d x)) Filter.atBot (𝓝 p) := by
    simpa only [Function.comp_def, id_eq, F.map_add] using
      h.comp (Filter.tendsto_atBot_add_const_right Filter.atBot d Filter.tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

private theorem MorseCancel.exists_basin_preserving_endpoint_clock {M : Type*} [TopologicalSpace M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ} (hc : c ∈ Set.Icc (-a) a)
    (hcrit : c ^ 2 = a ^ 2) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (x : M) {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail :
      ∀ᶠ t in l, ∃ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (r δ T : ℝ),
      Ψ.source = Φ.source ∧
        Ψ (c, 0) = Φ (c, 0) ∧
          0 < r ∧
            0 < δ ∧
              Metric.closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source ∧
                (∀ z : Fin m → ℝ,
                    ‖z‖ ≤ δ → cubicFlowCylinder σ a (z, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r) ∧
                  (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y) ∧
                    (∀ t : ℝ,
                        cubicFlowCylinder σ a (0, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
                          Ψ (cubicFlowCylinder σ a (0, t)) = F t x) ∧
                      ∀ z : Model m,
                        ∀ p : M,
                          (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atTop (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t (Φ z)) Filter.atTop (𝓝 p)) ∧
                            (Filter.Tendsto (fun t => F t (Ψ z)) Filter.atBot (𝓝 p) ↔
                              Filter.Tendsto (fun t => F t (Φ z)) Filter.atBot (𝓝 p)) := by
  obtain ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, d, hmap⟩ :=
    exists_clock_normalized_cubic_endpoint σ ha Φ hV hmodel F hF hc hcrit hcΦ x hlim htail
  refine ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, ?_⟩
  intro z p
  rw [hmap]
  exact ⟨flow_time_atTop_limit_iff F d (Φ z) p, flow_time_atBot_limit_iff F d (Φ z) p⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    AdaptedWindows.flow_belt_passage {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f) {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    S.flow (Degree.BeltPassage.time s)
        ((S.data q).chart.splitChart.symm
          (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)) =
      (S.data q).chart.splitChart.symm
        (Degree.BeltPassage.lower (S.data q).radius s u.val v.val) := by
  let d := S.data q
  let z := Degree.BeltPassage.upper d.radius s u.val v.val
  have htime := Degree.BeltPassage.time_nonneg hs
  have hstay (t : ℝ) (ht : t ∈ Set.uIcc 0 (Degree.BeltPassage.time s)) :
    Smale.MorseHandle.descentFlow t z ∈
      Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
        Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    rw [Set.uIcc_of_le htime] at ht
    exact
      Degree.BeltPassage.descentFlow_mem_block d.radius_pos hs hs₁
        (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property) ht
  have hz : z ∈ d.chart.splitChart.target := by
    have hh := d.block (hstay 0 Set.left_mem_uIcc)
    simpa only [Smale.MorseHandle.descentFlow.map_zero_apply] using hh
  have hcoords : d.chart.splitChart (d.chart.splitChart.symm z) = z :=
    d.chart.splitChart.right_inv' hz
  have hflow :=
    d.chart.flow_eq_descentModel_of_mem_uIcc (S.smooth.of_le (by simp)) S.flow S.integral (x :=
      d.chart.splitChart.symm z) (d.chart.splitChart.map_target' hz) (t :=
      Degree.BeltPassage.time s) (fun t ht => by rw [hcoords]; exact d.block (hstay t ht))
      (fun t ht => by rw [hcoords]; exact S.model_germ q _ (hstay t ht))
  change
    S.flow (Degree.BeltPassage.time s) (d.chart.splitChart.symm z) =
      d.chart.splitChart.symm
        (Smale.MorseHandle.descentFlow (Degree.BeltPassage.time s)
          (d.chart.splitChart (d.chart.splitChart.symm z))) at hflow
  rw [hcoords, Degree.BeltPassage.descentFlow_time d.radius hs u.val v.val] at hflow
  exact hflow

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.belt_passage_forward_limit_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f) {s : ℝ}
    (hs : 0 < s) (hs₁ : s ≤ 1) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (p : M) :
    Filter.Tendsto
        (fun t =>
          S.flow t
            ((S.data q).chart.splitChart.symm
              (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)))
        Filter.atTop (𝓝 p) ↔
      Filter.Tendsto
        (fun t =>
          S.flow t
            ((S.data q).chart.splitChart.symm
              (Degree.BeltPassage.lower (S.data q).radius s u.val v.val)))
        Filter.atTop (𝓝 p) := by
  rw [← S.flow_belt_passage q hs hs₁ u v]
  exact (MorseCancel.flow_time_atTop_limit_iff S.flow (Degree.BeltPassage.time s) _ p).symm

private theorem
    MorseCancel.compact_partial_chart_image_nowhereDense {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [T2Space X] (e : OpenPartialHomeomorph X A) {K : Set A}
    (hK : IsCompact K) (hKt : K ⊆ e.target) (hKi : interior K = ∅) :
    IsNowhereDense (e.symm '' K) := by
  have hclosed : IsClosed (e.symm '' K) :=
    (hK.image_of_continuousOn (e.symm.continuousOn.mono hKt)).isClosed
  apply hclosed.isNowhereDense_iff.mpr
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hKt hz)
  have hopen : IsOpen (e '' interior (e.symm '' K)) :=
    e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hsource)
  have hsub : e '' interior (e.symm '' K) ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := interior_subset hx
    rw [← hzx, e.right_inv (hKt hz)]
    exact hz
  have hinto : e '' interior (e.symm '' K) ⊆ interior K := hopen.subset_interior_iff.mpr hsub
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := hinto (Set.mem_image_of_mem e hx)
  exact (Set.eq_empty_iff_forall_notMem.mp hKi) _ hh

private theorem MorseCancel.interior_zero_product_empty {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [Nontrivial A] [TopologicalSpace B] (s : Set B) :
    interior (({0} : Set A) ×ˢ s) = ∅ := by
  rw [interior_prod_eq, interior_singleton, Set.empty_prod]

private theorem
    MorseCancel.native_positive_plane_piece_nowhereDense {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hindex : 0 < Module.finrank ℝ c.NegativeCoordinates) {r : ℝ}
    (hblock :
      ({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target) :
    IsNowhereDense
      (c.splitChart.symm ''
        (({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) r)) :=
  by
  let : Nontrivial c.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  exact
    compact_partial_chart_image_nowhereDense c.splitChart.toOpenPartialHomeomorph
      (isCompact_singleton.prod (ProperSpace.isCompact_closedBall _ _)) hblock
      (interior_zero_product_empty _)

private theorem MorseCancel.exists_backward_morse_quadratic_level_exit {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ}
    (hr : 0 < r) {z : N × P} (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ s : ℝ,
      s < 0 ∧
        Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow s z) = r ^ 2 ∧
          (∀ t ∈ Set.Icc s (0 : ℝ),
              Smale.MorseHandle.descentFlow t z ∈
                Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r)) ∧
            ‖(Smale.MorseHandle.descentFlow s z).1‖ ≤ ‖z.1‖ := by
  let R := 3 * r / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  let T := -Real.log (R / ‖z.2‖)
  have hn : 0 < ‖z.2‖ := norm_pos_iff.mpr hne
  have hratio : 1 < R / ‖z.2‖ := (one_lt_div hn).mpr (hzp.trans hrR)
  have hT : T < 0 := neg_neg_of_pos (Real.log_pos hratio)
  have hexp : Real.exp (-T) = R / ‖z.2‖ := by
    dsimp [T]
    rw [neg_neg, Real.exp_log (div_pos hR hn)]
  have hnorm : ‖(Smale.MorseHandle.descentFlow T z).2‖ = R := by
    rw [Smale.MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ R hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(Smale.MorseHandle.descentFlow t z).1‖ ≤ ‖z.1‖ := by
    rw [Smale.MorseHandle.norm_descentFlow_fst]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)
  have hstay (t : ℝ) (ht : t ∈ Set.Icc T (0 : ℝ)) :
    Smale.MorseHandle.descentFlow t z ∈
      Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r) := by
    constructor
    · exact mem_closedBall_zero_iff.mpr ((hsmall t ht.2).trans (by linarith))
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = R := by rw [hexp, div_mul_cancel₀ R hn.ne']
        _ ≤ 2 * r := by dsimp [R]; linarith
  have hheightT : r ^ 2 < Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z) := by
    change
      r ^ 2 <
        -‖(Smale.MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(Smale.MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr ((hsmall T hT.le).trans_lt hzn)
    dsimp [R]
    nlinarith [sq_pos_of_pos hr]
  have hheight0 : Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow 0 z) < r ^ 2 := by
    rw [Flow.map_zero_apply]
    change -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hzp
    nlinarith [sq_nonneg ‖z.1‖]
  have hc :
    Continuous (fun t : ℝ => Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow t z)) := by
    change
      Continuous
        (fun t : ℝ =>
          -‖(Smale.MorseHandle.descentFlow t z).1‖ ^ 2 +
            ‖(Smale.MorseHandle.descentFlow t z).2‖ ^ 2)
    exact
      (((Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const).fst.norm.pow
              2).neg).add
        ((Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const).snd.norm.pow 2)
  obtain ⟨s, hs, hlevel⟩ :=
    intermediate_value_Icc' hT.le hc.continuousOn
      (show
        r ^ 2 ∈
          Set.Icc (Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow 0 z))
            (Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z))
        from ⟨hheight0.le, hheightT.le⟩)
  have hs0 : s < 0 :=
    lt_of_le_of_ne hs.2
      (by
        intro heq
        rw [heq] at hlevel
        linarith)
  exact ⟨s, hs0, hlevel, fun t ht => hstay t ⟨hs.1.trans ht.1, ht.2⟩, hsmall s hs0.le⟩

private theorem
    MorseCancel.morse_descentFlow_swap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (t : ℝ) (z : N × P) :
    Smale.MorseHandle.descentFlow t z.swap = (Smale.MorseHandle.descentFlow (-t) z).swap := by
  simp only [Smale.MorseHandle.descentFlow, neg_neg, Prod.swap]

private theorem
    MorseCancel.morse_quadratic_swap {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : N × P) :
    Smale.MorseHandle.quadratic z.swap = -Smale.MorseHandle.quadratic z := by
  change -‖z.2‖ ^ 2 + ‖z.1‖ ^ 2 = -(-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  ring

private theorem
    MorseCancel.exists_forward_morse_quadratic_level_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ s : ℝ,
      0 < s ∧
        Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow s z) = -(r ^ 2) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s,
              Smale.MorseHandle.descentFlow t z ∈
                Metric.closedBall (0 : N) (2 * r) ×ˢ Metric.closedBall (0 : P) (2 * r)) ∧
            ‖(Smale.MorseHandle.descentFlow s z).2‖ ≤ ‖z.2‖ := by
  obtain ⟨s, hs, hlevel, hstay, hsmall⟩ :=
    exists_backward_morse_quadratic_level_exit (z := z.swap) hr hzp hzn hne
  rw [morse_descentFlow_swap, morse_quadratic_swap] at hlevel
  rw [morse_descentFlow_swap] at hsmall
  refine ⟨-s, neg_pos.mpr hs, by linarith, ?_, hsmall⟩
  intro t ht
  have hh :=
    hstay (-t) (show -t ∈ Set.Icc s (0 : ℝ) from ⟨by linarith [ht.2], neg_nonpos.mpr ht.1⟩)
  rw [morse_descentFlow_swap, neg_neg] at hh
  exact ⟨hh.2, hh.1⟩

private theorem MorseCancel.exists_uniform_small_of_zero_set {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {g : X → ℝ} (hg : Continuous g) (hnonneg : ∀ x, 0 ≤ g x) {U : Set X}
    (hU : IsOpen U) (hzero : ∀ x, g x = 0 → x ∈ U) : ∃ δ : ℝ, 0 < δ ∧ ∀ x, g x < δ → x ∈ U := by
  have hpos : ∀ x ∈ Uᶜ, 0 < g x := by
    intro x hx
    exact lt_of_le_of_ne (hnonneg x) (fun hh => hx (hzero x hh.symm))
  obtain ⟨δ, hδ, hbound⟩ := hU.isClosed_compl.isCompact.exists_forall_le' hg.continuousOn hpos
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_contra hnot
  exact (not_lt_of_ge (hbound x hnot)) hx

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_upper_morse_section_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀
          z ∈
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
          Smale.MorseHandle.quadratic z = r ^ 2 → ‖z.1‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
      {z | Smale.MorseHandle.quadratic z = r ^ 2}
  have hK : IsCompact K :=
    ((ProperSpace.isCompact_closedBall _ _).prod
          (ProperSpace.isCompact_closedBall _ _)).inter_right
      (isClosed_eq Smale.MorseHandle.continuous_quadratic continuous_const)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ψ : K → M := fun z => c.splitChart.symm z
  have hψ : Continuous ψ := by
    exact
      (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono
          (fun z hz => hblock hz.1)).domRestrict
  have hg : Continuous (fun z : K => ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖) :=
    continuous_subtype_val.fst.norm
  have hzero :
    ∀ z : K, ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ = 0 → z ∈ ψ ⁻¹' U := by
    intro z hz
    have hn : (z : c.NegativeCoordinates × c.PositiveCoordinates).1 = 0 := norm_eq_zero.mp hz
    have hq := z.property.2
    change
      -‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ ^ 2 +
          ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ ^ 2 =
        r ^ 2 at hq
    rw [hn, norm_zero] at hq
    have hp : ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ = r := by
      nlinarith [norm_nonneg (z : c.NegativeCoordinates × c.PositiveCoordinates).2]
    let v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates :=
      ⟨r⁻¹ • (z : c.NegativeCoordinates × c.PositiveCoordinates).2,
        by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
          hp]
        exact inv_mul_cancel₀ hr.ne'⟩
    have hv :
      r • (v : c.PositiveCoordinates) = (z : c.NegativeCoordinates × c.PositiveCoordinates).2 := by
      change r • (r⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hh := hcore v
    rw [c.beltCoreMap_coe, hv] at hh
    change c.splitChart.symm (z : c.NegativeCoordinates × c.PositiveCoordinates) ∈ U
    convert! hh using 1
    exact congrArg c.splitChart.symm (Prod.ext hn rfl)
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_uniform_small_of_zero_set hg (fun _ => norm_nonneg _) (hU.preimage hψ) hzero
  exact ⟨δ, hδ, fun z hz hlevel hs => hsmall ⟨z, hz, hlevel⟩ hs⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_lower_morse_section_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀
          z ∈
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
          Smale.MorseHandle.quadratic z = -(r ^ 2) → ‖z.2‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
      {z | Smale.MorseHandle.quadratic z = -(r ^ 2)}
  have hK : IsCompact K :=
    ((ProperSpace.isCompact_closedBall _ _).prod
          (ProperSpace.isCompact_closedBall _ _)).inter_right
      (isClosed_eq Smale.MorseHandle.continuous_quadratic continuous_const)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ψ : K → M := fun z => c.splitChart.symm z
  have hψ : Continuous ψ := by
    exact
      (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono
          (fun z hz => hblock hz.1)).domRestrict
  have hg : Continuous (fun z : K => ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖) :=
    continuous_subtype_val.snd.norm
  have hzero :
    ∀ z : K, ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ = 0 → z ∈ ψ ⁻¹' U := by
    intro z hz
    have hp : (z : c.NegativeCoordinates × c.PositiveCoordinates).2 = 0 := norm_eq_zero.mp hz
    have hq := z.property.2
    change
      -‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ ^ 2 +
          ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ ^ 2 =
        -(r ^ 2) at hq
    rw [hp, norm_zero] at hq
    have hn : ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ = r := by
      nlinarith [norm_nonneg (z : c.NegativeCoordinates × c.PositiveCoordinates).1]
    let v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates :=
      ⟨r⁻¹ • (z : c.NegativeCoordinates × c.PositiveCoordinates).1,
        by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
          hn]
        exact inv_mul_cancel₀ hr.ne'⟩
    have hv :
      r • (v : c.NegativeCoordinates) = (z : c.NegativeCoordinates × c.PositiveCoordinates).1 := by
      change r • (r⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hh := hcore v
    rw [c.attachingCoreMap_coe, hv] at hh
    change c.splitChart.symm (z : c.NegativeCoordinates × c.PositiveCoordinates) ∈ U
    convert! hh using 1
    exact congrArg c.splitChart.symm (Prod.ext rfl hp)
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_uniform_small_of_zero_set hg (fun _ => norm_nonneg _) (hU.preimage hψ) hzero
  exact ⟨δ, hδ, fun z hz hlevel hs => hsmall ⟨z, hz, hlevel⟩ hs⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_native_backward_morse_level_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).2 ≠ 0) :
    ∃ T : ℝ,
      T < 0 ∧
        f (F T x) = f p + r ^ 2 ∧
          F T x ∈ c.splitChart.source ∧
            ‖(c.splitChart (F T x)).1‖ ≤ ‖(c.splitChart x).1‖ ∧
              c.splitChart (F T x) ∈
                Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
  obtain ⟨T, hT, hlevel, hstay, hsmall⟩ := exists_backward_morse_quadratic_level_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :=
    hstay s (by simpa only [Set.uIcc_of_ge hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  have htarget := hbox (hstay T ⟨le_rfl, hT.le⟩)
  have hsource : F T x ∈ c.splitChart.source := by
    rw [hflow]
    exact c.splitChart.map_target' htarget
  have hcoord : c.splitChart (F T x) = Smale.MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change
      -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
          ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 =
        r ^ 2 at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨le_rfl, hT.le⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_native_forward_morse_level_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).1 ≠ 0) :
    ∃ T : ℝ,
      0 < T ∧
        f (F T x) = f p - r ^ 2 ∧
          F T x ∈ c.splitChart.source ∧
            ‖(c.splitChart (F T x)).2‖ ≤ ‖(c.splitChart x).2‖ ∧
              c.splitChart (F T x) ∈
                Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
  obtain ⟨T, hT, hlevel, hstay, hsmall⟩ := exists_forward_morse_quadratic_level_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :=
    hstay s (by simpa only [Set.uIcc_of_le hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  have htarget := hbox (hstay T ⟨hT.le, le_rfl⟩)
  have hsource : F T x ∈ c.splitChart.source := by
    rw [hflow]
    exact c.splitChart.map_target' htarget
  have hcoord : c.splitChart (F T x) = Smale.MorseHandle.descentFlow T (c.splitChart x) := by
    rw [hflow]
    exact c.splitChart.right_inv' htarget
  refine ⟨T, hT, ?_, hsource, ?_, ?_⟩
  · rw [hflow, c.splitChart_inverse_equation htarget]
    change
      -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
          ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 =
        -(r ^ 2) at hlevel
    linarith
  · simpa only [hcoord] using hsmall
  · rw [hcoord]
    exact hstay T ⟨hT.le, le_rfl⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.morse_coordinate_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source ∧ ‖(c.splitChart x).1‖ < a ∧ ‖(c.splitChart x).2‖ < b := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hn : ‖(c.splitChart p).1‖ < a := by
    simpa only [c.splitChart_center, Prod.fst_zero, norm_zero] using ha
  have hp : ‖(c.splitChart p).2‖ < b := by
    simpa only [c.splitChart_center, Prod.snd_zero, norm_zero] using hb
  have hs : ∀ᶠ x in 𝓝 p, x ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hna : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).1‖ < a := hc.fst.norm (eventually_lt_nhds hn)
  have hpb : ∀ᶠ x in 𝓝 p, ‖(c.splitChart x).2‖ < b := hc.snd.norm (eventually_lt_nhds hp)
  exact hs.and (hna.and hpb)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.eventually_backward_exit_in_belt_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).2 ≠ 0 → ∃ T : ℝ, T < 0 ∧ f (F T x) = f p + r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_upper_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c (lt_min hr hδ) hr] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_backward_morse_level_exit c hV F hF hr hblock hfield hx.1
      (hx.2.1.trans_le (min_le_left _ _)) hx.2.2 hne
  have hq : Smale.MorseHandle.quadratic (c.splitChart (F T x)) = r ^ 2 := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = r ^ 2
    linarith
  have hh :=
    hsection (c.splitChart (F T x)) hbox hq (hsmall.trans_lt (hx.2.1.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x := c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.eventually_forward_exit_in_attaching_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {U : Set M} (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∀ᶠ x in 𝓝 p, (c.splitChart x).1 ≠ 0 → ∃ T : ℝ, 0 < T ∧ f (F T x) = f p - r ^ 2 ∧ F T x ∈ U := by
  obtain ⟨δ, hδ, hsection⟩ := exists_lower_morse_section_neighborhood c hr hblock hU hcore
  filter_upwards [morse_coordinate_neighborhood c hr (lt_min hr hδ)] with x hx
  intro hne
  obtain ⟨T, hT, hlevel, hsource, hsmall, hbox⟩ :=
    exists_native_forward_morse_level_exit c hV F hF hr hblock hfield hx.1 hx.2.1
      (hx.2.2.trans_le (min_le_left _ _)) hne
  have hq : Smale.MorseHandle.quadratic (c.splitChart (F T x)) = -(r ^ 2) := by
    have heq := c.splitChart_equation hsource
    change -‖(c.splitChart (F T x)).1‖ ^ 2 + ‖(c.splitChart (F T x)).2‖ ^ 2 = -(r ^ 2)
    linarith
  have hh :=
    hsection (c.splitChart (F T x)) hbox hq (hsmall.trans_lt (hx.2.2.trans_le (min_le_right _ _)))
  have hinv : c.splitChart.symm (c.splitChart (F T x)) = F T x := c.splitChart.left_inv' hsource
  rw [hinv] at hh
  exact ⟨T, hT, hlevel, hh⟩

private theorem MorseCancel.quadratic_germ_derivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (Q : QuadraticForm ℝ A)
    (R : QuadraticForm ℝ B) (hR : Continuous R) {F : A → B} {L : A →L[ℝ] B}
    (hF : HasFDerivAt F L 0) (hF0 : F 0 = 0) (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) (v : A) :
    R (L v) = Q v := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hcurve : HasDerivAt (fun t : ℝ => F (t • v)) (L v) 0 :=
    hF.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ • F (t • v)) (𝓝[≠] 0) (𝓝 (L v)) := by
    simpa only [zero_add, zero_smul, hF0, sub_zero] using hcurve.tendsto_slope_zero
  have hpath : Filter.Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 (0 : A)) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa only [zero_smul] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have heq : (fun t : ℝ => R (t⁻¹ • F (t • v))) =ᶠ[𝓝[≠] 0] fun _ => Q v := by
    filter_upwards [hquad.comp_tendsto hpath, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    change R (F (t • v)) = Q (t • v) at ht
    rw [R.map_smul, ht, Q.map_smul]
    simp only [smul_eq_mul]
    field_simp
  exact
    tendsto_nhds_unique (hR.continuousAt.tendsto.comp hslope)
      ((Filter.tendsto_congr' heq).mpr tendsto_const_nhds)

private theorem MorseCancel.equivalent_quadratic_germs_of_bijective_derivative {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : QuadraticForm ℝ A) (R : QuadraticForm ℝ B) (hR : Continuous R) {F : A → B}
    {L : A →L[ℝ] B} (hF : HasFDerivAt F L 0) (hF0 : F 0 = 0) (hL : Function.Bijective L)
    (hquad : (fun x => R (F x)) =ᶠ[𝓝 0] Q) : Q.Equivalent R := by
  let e := LinearEquiv.ofBijective L.toLinearMap hL
  exact ⟨{ e with map_app' := quadratic_germ_derivative Q R hR hF hF0 hquad }⟩

private theorem MorseCancel.surgery_pair_band_isolation {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
      f z ∈ Set.Icc (S.lower p) (S.upper q) → z = p.val ∨ z = q.val := by
  intro z hz hband
  by_cases hzp : f z ≤ f p
  · exact Or.inl (S.isolated p z hz ⟨hband.1, hzp.trans (S.value_lt_upper p).le⟩)
  by_cases hqz : f q ≤ f z
  · exact Or.inr (S.isolated q z hz ⟨(S.lower_lt_value q).le.trans hqz, hband.2⟩)
  exact (hconsecutive ⟨z, hz⟩ ⟨lt_of_not_ge hzp, lt_of_not_ge hqz⟩).elim

private theorem MorseCancel.surgery_pair_inner_band_regular {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    {a b : ℝ} (ha : f p < a) (hb : b < f q) :
    ∀ z, f z ∈ Set.Icc a b → z ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro z hz hcrit
  exact hconsecutive ⟨z, hcrit⟩ ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩

private theorem
    MorseCancel.surviving_critical_germs_of_pair_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {l u : ℝ}
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hexterior : ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f := by
  intro z hz
  obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
  apply hexterior z
  intro hband
  exact (hpair z hzf ⟨hband.1.le, hband.2.le⟩).elim hzp hzq

private theorem MorseCancel.distinct_critical_values_of_surviving_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hsub : Smale.ManifoldMorse.criticalPoints E g ⊆ Smale.ManifoldMorse.criticalPoints E f)
    (hgerms : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) :
    Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
  intro x hx y hy hxy
  apply hinj (hsub hx) (hsub hy)
  rw [← (hgerms x hx).self_of_nhds, ← (hgerms y hy).self_of_nhds]
  exact hxy

private theorem MorseCancel.exists_signed_morse_chart_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p,
      d.weights = c.weights ∧
        d.chart.source ⊆ c.chart.source ∧
          (∀ x, d.chart x = c.chart x) ∧ ∀ z, d.chart.symm z = c.chart.symm z := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let P := Smale.PartialChart.restrictSource c.chart hU
  let d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p :=
    { weights := c.weights
      signs := c.signs
      chart := P
      mem_source := ⟨c.mem_source, hpU⟩
      center := c.center
      equation := by
        intro x hx
        have hxs : x ∈ c.chart.source ∩ U := hx
        have hxeq : g x = f x := hUsub hxs.2
        change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
        rw [hxeq, hgerm.self_of_nhds]
        exact c.equation x hxs.1
      inverse_equation := by
        intro z hz
        have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
        have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
        change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
        rw [hzeq, hgerm.self_of_nhds]
        exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl, Set.inter_subset_left, fun _ => rfl, fun _ => rfl⟩

private theorem
    MorseCancel.adapted_surgeries_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val)
    (hexterior : ∀ z, f z ∉ Set.Ioo (S.lower p) (S.upper q) → g =ᶠ[𝓝 z] f) :
    (∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) ∧
      Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation S p q hconsecutive) hcrit
      hexterior
  have hinj :=
    distinct_critical_values_of_surviving_germs S.distinct (fun z hz => ((hcrit z).mp hz).1) hkeep
  exact ⟨hkeep, hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

private theorem
    MorseCancel.signed_morse_chart_quadratic_equivalent {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    (QuadraticMap.weightedSumSquares ℝ c.weights).Equivalent
      (QuadraticMap.weightedSumSquares ℝ d.weights) := by
  let Z := Fin (Module.finrank ℝ E) → ℝ
  let Q : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ c.weights
  let R : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ d.weights
  have hQ (z : Z) : Q z = ∑ i, c.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) c.weights z)
  have hR (z : Z) : R z = ∑ i, d.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) d.weights z)
  have hRcont : Continuous R := by
    change Continuous (fun z : Z => R z)
    simp_rw [hR]
    fun_prop
  let P := c.chart.symm.trans d.chart
  have hc0 : c.chart.symm (0 : Z) = p := by
    rw [← c.center]
    exact c.chart.left_inv' c.mem_source
  have h0 : (0 : Z) ∈ P.source := by
    refine ⟨?_, ?_⟩
    · rw [← c.center]
      exact c.chart.map_source' c.mem_source
    · change c.chart.symm (0 : Z) ∈ d.chart.source
      rw [hc0]
      exact d.mem_source
  have hP0 : P (0 : Z) = 0 := by
    change d.chart (c.chart.symm (0 : Z)) = 0
    rw [hc0, d.center]
  have hdiff := (P.mdifferentiableAt (by simp) h0).differentiableAt
  have hbij : Function.Bijective (fderiv ℝ P (0 : Z)) := by
    have hh := Smale.PartialChart.bijective_mfderiv P h0
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hquad : (fun z => R (P z)) =ᶠ[𝓝 (0 : Z)] Q := by
    filter_upwards [P.open_source.mem_nhds h0] with z hz
    have hzs : z ∈ c.chart.target ∧ c.chart.symm z ∈ d.chart.source := hz
    rw [hR, hQ]
    change (∑ i, d.weights i * (d.chart (c.chart.symm z) i) ^ 2) = ∑ i, c.weights i * (z i) ^ 2
    linarith [c.inverse_equation z hzs.1, d.equation (c.chart.symm z) hzs.2]
  exact
    equivalent_quadratic_germs_of_bijective_derivative Q R hRcont hdiff.hasFDerivAt hP0 hbij hquad

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.signed_morse_chart_negative_card_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Fintype.card { i // c.weights i = -1 } = Fintype.card { i // d.weights i = -1 } := by
  have hs := (signed_morse_chart_quadratic_equivalent c d).sigNeg_eq
  rw [QuadraticForm.sigNeg_weightedSumSquares, QuadraticForm.sigNeg_weightedSumSquares] at hs
  have hc : {i | c.weights i < 0} = {i | c.weights i = -1} := by
    ext i
    rcases c.signs i with h | h <;> norm_num [h]
  have hd : {i | d.weights i < 0} = {i | d.weights i = -1} := by
    ext i
    rcases d.signs i with h | h <;> norm_num [h]
  rw [hc, hd] at hs
  calc
    Fintype.card { i // c.weights i = -1 } = {i | c.weights i = -1}.ncard :=
      Set.fintypeCard_eq_ncard _
    _ = {i | d.weights i = -1}.ncard := hs
    _ = Fintype.card { i // d.weights i = -1 } := (Set.fintypeCard_eq_ncard _).symm

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.signed_morse_chart_negative_finrank_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c d : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using
    signed_morse_chart_negative_card_eq c d

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.signed_morse_chart_negative_finrank_eq_of_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p) (hgerm : g =ᶠ[𝓝 p] f) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  obtain ⟨c', hw, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
  have heq := signed_morse_chart_negative_card_eq c' d
  rw [hw] at heq
  simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using heq

attribute [local instance 100] Classical.propDecidable in
private def
    MorseCancel.nativeMorseIndex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) : ℕ :=
  if h : Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) f p) then
    Module.finrank ℝ (Classical.choice h).NegativeCoordinates
  else 0

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeMorseIndex_eq_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    nativeMorseIndex E f p = Module.finrank ℝ c.NegativeCoordinates := by
  unfold nativeMorseIndex
  rw [dite_eq_left ⟨c⟩]
  exact signed_morse_chart_negative_finrank_eq _ c

private theorem MorseCancel.nativeMorseIndex_congr_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hgerm : g =ᶠ[𝓝 p] f) : nativeMorseIndex E g p = nativeMorseIndex E f p := by
  classical
  by_cases h : Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    obtain ⟨d, -, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
    rw [nativeMorseIndex_eq_chart c, nativeMorseIndex_eq_chart d]
    exact (signed_morse_chart_negative_finrank_eq_of_germ c d hgerm).symm
  · have hg : ¬Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) g p) := by
      rintro ⟨d⟩
      obtain ⟨c, -, -, -, -⟩ := exists_signed_morse_chart_of_germ d hgerm.symm
      exact h ⟨c⟩
    simp only [nativeMorseIndex, dite_eq_right h, dite_eq_right hg]

private theorem
    MorseCancel.nativeMorseIndex_le {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} :
    nativeMorseIndex E f p ≤ Module.finrank ℝ E := by
  classical
  by_cases h : Nonempty (Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
  · obtain ⟨c⟩ := h
    rw [nativeMorseIndex_eq_chart c]
    have hc := c.finrank_negative_add_positive
    omega
  · simp only [nativeMorseIndex, dite_eq_right h, Nat.zero_le]

private theorem AdaptedWindows.nonminimum_forward_basin_meagre {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : 0 < MorseCancel.nativeMorseIndex E f p) :
    IsMeagre {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancel.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  let K :=
    c.splitChart.symm ''
      (({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) (r / 2))
  have hKt :
    ({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) (r / 2) ⊆
      c.splitChart.target := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha0 : a = 0 := ha
    subst a
    exact
      hblock
        ⟨Metric.mem_closedBall_self hr.le,
          Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r) hb⟩
  have hi : 0 < Module.finrank ℝ c.NegativeCoordinates := by
    rwa [MorseCancel.nativeMorseIndex_eq_chart c] at hindex
  have hK : IsNowhereDense K := MorseCancel.native_positive_plane_piece_nowhereDense c hi hKt
  have hcover :
    {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} ⊆
      ⋃ n : ℕ, S.flow (-(n : ℝ)) '' K := by
    intro x hx
    have hlim : Filter.Tendsto (fun n : ℕ => S.flow (n : ℝ) x) Filter.atTop (𝓝 p.val) :=
      hx.comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hs, hn, hp⟩ :=
      (hlim.eventually
          (MorseCancel.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
    have hnew : Filter.Tendsto (fun t => S.flow t (S.flow (n : ℝ) x)) Filter.atTop (𝓝 p.val) :=
      (MorseCancel.flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
    have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
      ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp.trans (half_lt_self hr))).1).mp hnew
    have hmem : S.flow (n : ℝ) x ∈ K := by
      refine ⟨c.splitChart (S.flow (n : ℝ) x), ?_, c.splitChart.left_inv' hs⟩
      exact ⟨Set.mem_singleton_iff.mpr hz, mem_closedBall_zero_iff.mpr hp.le⟩
    exact
      Set.mem_iUnion.mpr
        ⟨n, S.flow (n : ℝ) x, hmem, (S.flow.toHomeomorph (n : ℝ)).symm_apply_apply x⟩
  apply IsMeagre.mono hcover
  apply isMeagre_iUnion
  intro n
  exact ((S.flow.toHomeomorph (-(n : ℝ))).isInducing.isNowhereDense_image hK).isMeagre

private theorem Degree.FlowCancellation.height_eq_of_mem_omegaLimit {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {κ : Filter ℝ} {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) {y : X}
    (hy : y ∈ omegaLimit κ F { x }) : f y = l := by
  have hc : MapClusterPt y κ (fun t => F t x) :=
    (mem_omegaLimit_singleton_iff_mapClusterPt κ F x y).mp hy
  have hh := hc.continuousAt_comp hf.continuousAt
  have hl : Filter.map (f ∘ (fun t => F t x)) κ ≤ 𝓝 l := hlim
  exact eq_of_nhds_neBot (hh.clusterPt.mono hl)

private theorem Degree.FlowCancellation.omegaLimit_subset_of_strict_height {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {κ : Filter ℝ}
    (hshift : ∀ t : ℝ, Filter.Tendsto (t + ·) κ κ) {S : Set X}
    (hstrict : ∀ y ∉ S, f (F 1 y) < f y) {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) : omegaLimit κ F { x } ⊆ S := by
  intro y hy
  by_contra hnot
  have hy' : F 1 y ∈ omegaLimit κ F { x } := (F.isInvariant_omegaLimit κ { x } hshift) 1 hy
  have h0 := height_eq_of_mem_omegaLimit F hf hlim hy
  have h1 := height_eq_of_mem_omegaLimit F hf hlim hy'
  have hs := hstrict y hnot
  rw [h0, h1] at hs
  exact lt_irrefl _ hs

private theorem
    Degree.FlowCancellation.exists_flow_limit_of_injective_exceptional_height {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {κ : Filter ℝ} [Filter.NeBot κ] (hshift : ∀ t : ℝ, Filter.Tendsto (t + ·) κ κ) {S : Set X}
    (hstrict : ∀ y ∉ S, f (F 1 y) < f y) (hinj : Set.InjOn f S) {x : X} {l : ℝ}
    (hlim : Filter.Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) :
    ∃ p ∈ S, f p = l ∧ Filter.Tendsto (fun t : ℝ => F t x) κ (𝓝 p) := by
  have hsub := omegaLimit_subset_of_strict_height F hf hshift hstrict hlim
  obtain ⟨p, hp⟩ := nonempty_omegaLimit κ F { x } (Set.singleton_nonempty x)
  have hpl := height_eq_of_mem_omegaLimit F hf hlim hp
  have hsingle : omegaLimit κ F { x } ⊆ { p } := by
    intro y hy
    exact hinj (hsub hy) (hsub hp) ((height_eq_of_mem_omegaLimit F hf hlim hy).trans hpl.symm)
  refine ⟨p, hsub hp, hpl, ?_⟩
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  have hωV : omegaLimit κ F { x } ⊆ V := hsingle.trans (Set.singleton_subset_iff.mpr hpV)
  have hEv := eventually_mapsTo_of_isOpen_of_omegaLimit_subset κ F { x } hV hωV
  filter_upwards [hEv] with t ht
  exact hVU (ht (Set.mem_singleton x))

private theorem Degree.FlowCancellation.exists_strict_descent_flow_endpoints {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {S : Set X} (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) (x : X) :
    ∃ p ∈ S,
      ∃ q ∈ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 q) ∧
            (x ∉ S → f q < f x ∧ f x < f p) := by
  have hrange : Set.range (fun t : ℝ => f (F t x)) ⊆ Set.range f := by
    rintro y ⟨t, rfl⟩
    exact ⟨F t x, rfl⟩
  have hbelow : BddBelow (Set.range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddBelow.mono hrange
  have habove : BddAbove (Set.range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddAbove.mono hrange
  have htop := tendsto_atTop_ciInf (hmono x) hbelow
  have hbot := tendsto_atBot_ciSup (hmono x) habove
  have hshiftTop (t : ℝ) : Filter.Tendsto (t + ·) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b - t)] with s hs
    linarith
  have hshiftBot (t : ℝ) : Filter.Tendsto (t + ·) Filter.atBot Filter.atBot := by
    apply Filter.tendsto_atBot.mpr
    intro b
    filter_upwards [Filter.eventually_le_atBot (b - t)] with s hs
    linarith
  have hstep (y : X) (hy : y ∉ S) : f (F 1 y) < f y := by
    have hh := hstrict y hy (show (0 : ℝ) < 1 by norm_num)
    simpa only [F.map_zero_apply] using hh
  obtain ⟨p, hp, hfp, hplim⟩ :=
    exists_flow_limit_of_injective_exceptional_height F hf hshiftBot hstep hinj hbot
  obtain ⟨q, hq, hfq, hqlim⟩ :=
    exists_flow_limit_of_injective_exceptional_height F hf hshiftTop hstep hinj htop
  refine ⟨p, hp, q, hq, hplim, hqlim, ?_⟩
  intro hx
  have hlow : f q ≤ f (F 1 x) := by
    rw [hfq]
    exact ciInf_le hbelow 1
  have hhigh : f (F (-1) x) ≤ f p := by
    rw [hfp]
    exact le_ciSup habove (-1)
  have hdec : f (F 1 x) < f x := hstep x hx
  have hinc : f x < f (F (-1) x) := by
    have hh := hstrict x hx (show (-1 : ℝ) < 0 by norm_num)
    simpa only [F.map_zero_apply] using hh
  exact ⟨hlow.trans_lt hdec, hinc.trans_le hhigh⟩

private theorem Degree.FlowCancellation.exists_uniform_flow_escape {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {C : Set X} (hC : IsCompact C) {c d : ℝ}
    (hescape : ∀ x ∈ C, ∃ t : ℝ, f (F t x) ∉ Set.Icc c d) :
    ∃ T : ℝ,
      0 < T ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∃ t ∈ Set.Icc (-T) T, f (F t x) < c - δ ∨ d + δ < f (F t x) := by
  classical
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, by norm_num, 1, by norm_num, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  let J := { p : ℝ × ℝ // 0 < p.2 }
  let O : J → Set X := fun p =>
    {x | f (F p.val.1 x) < c - p.val.2 ∨ d + p.val.2 < f (F p.val.1 x)}
  have hO (p : J) : IsOpen (O p) :=
    (isOpen_lt (hf.comp (F.continuous_toFun p.val.1)) continuous_const).union
      (isOpen_lt continuous_const (hf.comp (F.continuous_toFun p.val.1)))
  have hcover : C ⊆ ⋃ p, O p := by
    intro x hx
    obtain ⟨t, ht⟩ := hescape x hx
    by_cases hl : c ≤ f (F t x)
    · have hr : d < f (F t x) := lt_of_not_ge (fun h => ht ⟨hl, h⟩)
      have hδ : 0 < (f (F t x) - d) / 2 := by linarith
      apply Set.mem_iUnion.mpr
      refine ⟨⟨(t, (f (F t x) - d) / 2), hδ⟩, Or.inr ?_⟩
      change d + (f (F t x) - d) / 2 < f (F t x)
      linarith
    · have hl' : f (F t x) < c := lt_of_not_ge hl
      have hδ : 0 < (c - f (F t x)) / 2 := by linarith
      apply Set.mem_iUnion.mpr
      refine ⟨⟨(t, (c - f (F t x)) / 2), hδ⟩, Or.inl ?_⟩
      change f (F t x) < c - (c - f (F t x)) / 2
      linarith
  obtain ⟨S, hScover⟩ := hC.elim_finite_subcover O hO hcover
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, -⟩ := Set.mem_iUnion₂.mp (hScover hx)
    exact ⟨p, hp⟩
  let T := S.sup' hS (fun p => |p.val.1|) + 1
  let δ := S.inf' hS (fun p => p.val.2) / 2
  have hmin : 0 < S.inf' hS (fun p => p.val.2) :=
    (Finset.lt_inf'_iff hS).mpr (fun p _ => p.property)
  have hT : 0 < T := by
    obtain ⟨p, hp⟩ := hS
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    have habs := abs_nonneg p.val.1
    dsimp [T]
    linarith
  have hδ : 0 < δ := div_pos hmin (by norm_num)
  refine ⟨T, hT, δ, hδ, ?_⟩
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Set.mem_iUnion₂.mp (hScover hx)
  have ht : |p.val.1| ≤ T := by
    have hh := Finset.le_sup' (fun p : J => |p.val.1|) hp
    dsimp [T]
    linarith
  have hd : δ ≤ p.val.2 := by
    have hh := Finset.inf'_le (fun p : J => p.val.2) hp
    dsimp [δ]
    linarith
  refine ⟨p.val.1, abs_le.mp ht, ?_⟩
  rcases hpx with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

private theorem Degree.FlowCancellation.exists_flow_no_return_neighborhood {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {c d : ℝ} {K U : Set X} (hU : IsOpen U)
    (hKU : K ⊆ U) (hband : ∀ x ∈ K, f x ∈ Set.Icc c d) (hinvariant : ∀ t x, x ∈ K → F t x ∈ K)
    (hmaximal : ∀ x, (∀ t : ℝ, f (F t x) ∈ Set.Icc c d) → x ∈ K) :
    ∃ N : Set X,
      IsOpen N ∧
        K ⊆ N ∧
          N ⊆ U ∧ ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  have hescape : ∀ x ∈ Uᶜ, ∃ t : ℝ, f (F t x) ∉ Set.Icc c d := by
    intro x hx
    by_contra hh
    apply hx
    apply hKU
    apply hmaximal x
    intro t
    by_contra ht
    exact hh ⟨t, ht⟩
  obtain ⟨T, hT, δ, hδ, hEsc⟩ :=
    exists_uniform_flow_escape F hf hU.isClosed_compl.isCompact hescape
  let N : Set X := {x | ∀ s ∈ Set.Icc (-T) T, F s x ∈ U} ∩ f ⁻¹' Set.Ioo (c - δ) (d + δ)
  have hN : IsOpen N :=
    (Smale.MorsePerturbation.isOpen_forall_mem_compact CompactIccSpace.isCompact_Icc
          (hU.preimage (F.continuous continuous_snd continuous_fst))).inter
      (isOpen_Ioo.preimage hf)
  have hKN : K ⊆ N := by
    intro x hx
    refine ⟨fun s _ => hKU (hinvariant s x hx), ?_⟩
    have hh := hband x hx
    constructor <;> linarith [hh.1, hh.2]
  have hNU : N ⊆ U := by
    intro x hx
    have hh := hx.1 0 (show (0 : ℝ) ∈ Set.Icc (-T) T from ⟨by linarith, hT.le⟩)
    simpa only [F.map_zero_apply] using hh
  refine ⟨N, hN, hKN, hNU, ?_⟩
  intro x hx t ht htx s hs
  by_cases hshort : s ≤ T
  · exact hx.1 s ⟨by linarith [hs.1], hshort⟩
  have hTs : T < s := lt_of_not_ge hshort
  by_cases hshort' : t - s ≤ T
  · have hh := htx.1 (s - t) (show s - t ∈ Set.Icc (-T) T from ⟨by linarith, by linarith [hs.2]⟩)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  have hTs' : T < t - s := lt_of_not_ge hshort'
  by_contra hout
  obtain ⟨v, hv, hleave⟩ := hEsc (F s x) hout
  have htime : s + v ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hlo := hmono x htime.1
  have hhi := hmono x htime.2
  change f (F (s + v) x) ≤ f (F 0 x) at hlo
  change f (F t x) ≤ f (F (s + v) x) at hhi
  rw [F.map_zero_apply] at hlo
  rw [← F.map_add, add_comm v s] at hleave
  have hxheight : f x ∈ Set.Ioo (c - δ) (d + δ) := hx.2
  have htheight : f (F t x) ∈ Set.Ioo (c - δ) (d + δ) := htx.2
  rcases hleave with h | h
  · linarith [htheight.1]
  · linarith [hxheight.2]

private theorem
    Degree.FlowCancellation.invariant_band_subset_connection {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {S : Set X}
    (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q z : X}
    (hpair : ∀ x ∈ S, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hunique :
      ∀ x ∉ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {x : X} (hstay : ∀ t : ℝ, f (F t x) ∈ Set.Icc (f p) (f q)) :
    x ∈ ({ p, q } : Set X) ∪ Set.range (fun t : ℝ => F t z) := by
  have hxband : f x ∈ Set.Icc (f p) (f q) := by simpa only [F.map_zero_apply] using hstay 0
  by_cases hxS : x ∈ S
  · rcases hpair x hxS hxband with rfl | rfl <;> exact Or.inl (by simp)
  obtain ⟨r, hr, s, hs, hrlim, hslim, hsep⟩ :=
    exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrband : f r ∈ Set.Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hrlim)
      (Filter.Eventually.of_forall hstay)
  have hsband : f s ∈ Set.Icc (f p) (f q) :=
    isClosed_Icc.mem_of_tendsto (hf.continuousAt.tendsto.comp hslim)
      (Filter.Eventually.of_forall hstay)
  have hsep' := hsep hxS
  have hrq : r = q :=
    (hpair r hr hrband).resolve_left
      (by
        intro he
        rw [he] at hsep'
        linarith [hxband.1])
  have hsp : s = p :=
    (hpair s hs hsband).resolve_right
      (by
        intro he
        rw [he] at hsep'
        linarith [hxband.2])
  obtain ⟨t, ht⟩ :=
    hunique x hxS (by simpa only [hrq] using hrlim) (by simpa only [hsp] using hslim)
  exact Or.inr ⟨t, ht⟩

private theorem Degree.FlowCancellation.exists_isolated_connection_no_return {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {S : Set X} (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x)))
    (hfixed : ∀ x ∈ S, ∀ t : ℝ, F t x = x) {p q z : X} (hp : p ∈ S) (hq : q ∈ S) (hpq : f p < f q)
    (hpair : ∀ x ∈ S, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Set.Icc (f p) (f q))
    (hunique :
      ∀ x ∉ S,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set X} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U) (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set X,
      IsOpen N ∧
        N ⊆ U ∧
          p ∈ N ∧
            q ∈ N ∧
              (∀ t : ℝ, F t z ∈ N) ∧
                ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  let K : Set X := {x | ∀ t : ℝ, f (F t x) ∈ Set.Icc (f p) (f q)}
  have hKU : K ⊆ U := by
    intro x hx
    rcases invariant_band_subset_connection F hf hinj hmono hstrict hpair hunique hx with h |
      ⟨t, rfl⟩
    · rcases h with h | h
      · exact h ▸ hpU
      · exact (show x = q from h) ▸ hqU
    · exact hzU t
  have hKband (x : X) (hx : x ∈ K) : f x ∈ Set.Icc (f p) (f q) := by
    simpa only [F.map_zero_apply] using hx 0
  have hKi (t : ℝ) (x : X) (hx : x ∈ K) : F t x ∈ K := by
    intro s
    rw [← F.map_add]
    exact hx (s + t)
  obtain ⟨N, hN, hKN, hNU, hreturn⟩ :=
    exists_flow_no_return_neighborhood F hf hmono hU hKU hKband hKi (fun _ h => h)
  have hpK : p ∈ K := by
    intro t
    rw [hfixed p hp t]
    exact ⟨le_rfl, hpq.le⟩
  have hqK : q ∈ K := by
    intro t
    rw [hfixed q hq t]
    exact ⟨hpq.le, le_rfl⟩
  exact ⟨N, hN, hNU, hKN hpK, hKN hqK, fun t => hKN (hKi t z hzband), hreturn⟩

private theorem Degree.FlowCancellation.exists_native_descent_endpoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) (x : M) :
    ∃ p ∈ Smale.ManifoldMorse.criticalPoints E f,
      ∃ q ∈ Smale.ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 q) ∧
            (x ∉ Smale.ManifoldMorse.criticalPoints E f → f q < f x ∧ f x < f p) := by
  exact
    exists_strict_descent_flow_endpoints F hf.continuous hinj
      (Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
      (fun x hx =>
        Smale.FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hcurve hzero hdesc
          hx)
      x

private theorem Degree.FlowCancellation.exists_native_connection_no_return {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {p q z : M}
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hpair :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc (f p) (f q) → x = p ∨ x = q)
    (hzband : ∀ t : ℝ, f (F t z) ∈ Set.Icc (f p) (f q))
    (hunique :
      ∀ x ∉ Smale.ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 p) → ∃ t : ℝ, F t z = x)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) (hqU : q ∈ U) (hzU : ∀ t : ℝ, F t z ∈ U) :
    ∃ N : Set M,
      IsOpen N ∧
        N ⊆ U ∧
          p ∈ N ∧
            q ∈ N ∧
              (∀ t : ℝ, F t z ∈ N) ∧
                ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  exact
    exists_isolated_connection_no_return F hf.continuous hinj
      (Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc)
      (fun x hx => Smale.FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx)
      (fun x hx t => Smale.FlowConstruction.flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t) hp hq
      hpq hpair hzband hunique hU hpU hqU hzU

private theorem AdaptedWindows.isOpen_minimum_forward_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : MorseCancel.nativeMorseIndex E f p = 0) :
    IsOpen {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  have hi : Module.finrank ℝ c.NegativeCoordinates = 0 :=
    (MorseCancel.nativeMorseIndex_eq_chart c).symm.trans hindex
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hi
  obtain ⟨r, hr, -, hbasin⟩ :=
    MorseCancel.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have hnear : ∀ᶠ y in 𝓝 p.val, Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val) := by
    filter_upwards [MorseCancel.morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => S.flow t y) := S.flow.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (MorseCancel.flow_time_atTop_limit_iff S.flow t y p.val).mp hy

private theorem AdaptedWindows.dense_minimum_forward_basins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    Dense
      {x : M |
        ∃ p : Smale.ManifoldMorse.criticalPoints E f,
          MorseCancel.nativeMorseIndex E f p = 0 ∧
            Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let : Finite (Smale.ManifoldMorse.criticalPoints E f) := S.finite.to_subtype
  let I :=
    { p : Smale.ManifoldMorse.criticalPoints E f // 0 < MorseCancel.nativeMorseIndex E f p }
  let B := ⋃ p : I, {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val.val)}
  have hm : IsMeagre B :=
    isMeagre_iUnion (fun p : I => S.nonminimum_forward_basin_meagre hf p.val p.property)
  have hd : Dense Bᶜ := dense_of_mem_residual hm
  apply hd.mono
  intro x hx
  obtain ⟨r, hr, p, hp, -, hlim, -⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x
  have hi : MorseCancel.nativeMorseIndex E f p = 0 := by
    by_contra hi
    apply hx
    exact Set.mem_iUnion.mpr ⟨(⟨⟨p, hp⟩, Nat.pos_of_ne_zero hi⟩ : I), hlim⟩
  exact ⟨⟨p, hp⟩, hi, hlim⟩

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.exists_positive_belt_branch_in_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranch :
      Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          ∀ s : ℝ,
            0 < s →
              s < ε →
                Filter.Tendsto
                  (fun t =>
                    S.flow t
                      ((S.data q).chart.splitChart.symm
                        (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)))
                  Filter.atTop (𝓝 p.val) := by
  let d := S.data q
  have h0target : Degree.BeltPassage.lower d.radius 0 u.val v.val ∈ d.chart.splitChart.target := by
    rw [Degree.BeltPassage.lower_zero]
    apply d.block
    constructor
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos d.radius_pos,
        mem_sphere_zero_iff_norm.mp u.property, mul_one]
      linarith [d.radius_pos]
    · exact Metric.mem_closedBall_self (by linarith [d.radius_pos])
  have h0value :
    d.chart.splitChart.symm (Degree.BeltPassage.lower d.radius 0 u.val v.val) =
      (d.surgery.attachingSphere u).val := by
    rw [Degree.BeltPassage.lower_zero, d.attaching_eq, d.chart.attachingCoreMap_coe]
  have hc :
    ContinuousAt
      (fun s : ℝ => d.chart.splitChart.symm (Degree.BeltPassage.lower d.radius s u.val v.val))
      0 :=
    (d.chart.splitChart.contMDiffOn_invFun.continuousOn.continuousAt
          (d.chart.splitChart.open_target.mem_nhds h0target)).comp
      (f := fun s : ℝ => Degree.BeltPassage.lower d.radius s u.val v.val)
      (Degree.BeltPassage.contDiff_lower d.radius u.val v.val).continuous.continuousAt
  have hbasin :
    d.chart.splitChart.symm (Degree.BeltPassage.lower d.radius 0 u.val v.val) ∈
      {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
    rw [h0value]
    exact hbranch
  have hnear := hc.tendsto.eventually ((S.isOpen_minimum_forward_basin hf p hp).mem_nhds hbasin)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨Min.min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro s hs hsε
  have hs₁ : s ≤ 1 := (hsε.trans_le (min_le_right _ _)).le
  apply (S.belt_passage_forward_limit_iff q hs hs₁ u v p.val).mpr
  apply hδsub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs]
  exact hsε.trans_le (min_le_left _ _)

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.exists_two_sided_belt_branch_in_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          ∀ s : ℝ,
            0 < |s| →
              |s| < ε →
                Filter.Tendsto
                  (fun t =>
                    S.flow t
                      ((S.data q).chart.splitChart.symm
                        (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)))
                  Filter.atTop (𝓝 p.val) := by
  let u' : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 :=
    ⟨-u.val,
      mem_sphere_zero_iff_norm.mpr
        (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp u.property)⟩
  obtain ⟨εp, hεp, hεp1, hplus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u v (hbranches u)
  obtain ⟨εn, hεn, -, hminus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u' v (hbranches u')
  refine ⟨Min.min εp εn, lt_min hεp hεn, (min_le_left _ _).trans hεp1, ?_⟩
  intro s hs hsmall
  by_cases hpos : 0 < s
  · apply hplus s hpos
    rw [abs_of_pos hpos] at hsmall
    exact hsmall.trans_le (min_le_left _ _)
  · have hneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (abs_pos.mp hs)
    have heq :
      Degree.BeltPassage.upper (S.data q).radius s u.val v.val =
        Degree.BeltPassage.upper (S.data q).radius (-s) u'.val v.val := by
      simpa only [neg_neg] using Degree.BeltPassage.upper_neg (S.data q).radius (-s) u.val v.val
    rw [heq]
    apply hminus (-s) (neg_pos.mpr hneg)
    rw [abs_of_neg hneg] at hsmall
    exact hsmall.trans_le (min_le_right _ _)

attribute [local instance 100] Classical.propDecidable in
private def MorseCancel.nativeBeltArc {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) : M :=
  (S.data q).chart.splitChart.symm (Degree.BeltPassage.upper (S.data q).radius s u.val v.val)

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.nativeBeltArc_coordinates_mem_target {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    Degree.BeltPassage.upper (S.data q).radius s u.val v.val ∈
      (S.data q).chart.splitChart.target :=
  (S.data q).block
    (Degree.BeltPassage.upper_mem_block (S.data q).radius_pos hs
      (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property))

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.nativeBeltArc_height {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    f (nativeBeltArc S q u v s) = S.toSurgeryWindows.upper q := by
  rw [nativeBeltArc,
    (S.data q).chart.splitChart_inverse_equation
      (nativeBeltArc_coordinates_mem_target S q u v hs)]
  have hh :=
    Degree.BeltPassage.upper_height (S.data q).radius s (mem_sphere_zero_iff_norm.mp u.property)
      (mem_sphere_zero_iff_norm.mp v.property)
  change
    -‖(Degree.BeltPassage.upper (S.data q).radius s u.val v.val).1‖ ^ 2 +
        ‖(Degree.BeltPassage.upper (S.data q).radius s u.val v.val).2‖ ^ 2 =
      (S.data q).radius ^ 2 at hh
  dsimp only [Smale.ManifoldMorse.SurgeryWindows.upper]
  linarith

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.nativeBeltArc_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeBeltArc S q u v 0 = ((S.data q).surgery.beltSphere v).val := by
  rw [nativeBeltArc, Degree.BeltPassage.upper_zero, (S.data q).belt_eq,
    (S.data q).chart.beltCoreMap_coe]

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeBeltArc_belt_eq_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v w : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val ↔ s = 0 ∧ v = w := by
  constructor
  · intro heq
    have hzero := nativeBeltArc_coordinates_mem_target S q u w (s := 0) (by simp)
    rw [Degree.BeltPassage.upper_zero] at hzero
    rw [nativeBeltArc, (S.data q).belt_eq, (S.data q).chart.beltCoreMap_coe] at heq
    have hcoords :=
      (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
        (nativeBeltArc_coordinates_mem_target S q u v hs) hzero heq
    have hu : u.val ≠ 0 := by
      intro h
      have hn := mem_sphere_zero_iff_norm.mp u.property
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    have hs0 : s = 0 := by
      have hfst : ((S.data q).radius * s) • u.val = 0 := congrArg Prod.fst hcoords
      have hz : (S.data q).radius * s = 0 := (smul_eq_zero.mp hfst).resolve_right hu
      exact (mul_eq_zero.mp hz).resolve_left (S.data q).radius_pos.ne'
    refine ⟨hs0, ?_⟩
    rw [hs0, Degree.BeltPassage.upper_zero] at hcoords
    exact
      Subtype.ext (smul_right_injective _ (S.data q).radius_pos.ne' (congrArg Prod.snd hcoords))
  · rintro ⟨rfl, rfl⟩
    exact nativeBeltArc_zero S q u v

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.nativeBeltArc_injOn {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    Set.InjOn (nativeBeltArc S q u v) (Set.Icc (-1 : ℝ) 1) := by
  intro s hs t ht hst
  have hcoords :=
    (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
      (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr hs))
      (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ht)) hst
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hfst : ((S.data q).radius * s) • u.val = ((S.data q).radius * t) • u.val :=
    congrArg Prod.fst hcoords
  exact mul_left_cancel₀ (S.data q).radius_pos.ne' (smul_left_injective ℝ hu hfst)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeBeltArc_contMDiffOn {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (nativeBeltArc S q u v) (Set.Ioo (-1 : ℝ) 1) := by
  apply
    (S.data q).chart.splitChart.contMDiffOn_invFun.comp
      (Degree.BeltPassage.contDiff_upper (S.data q).radius u.val v.val).contMDiff.contMDiffOn
  intro s hs
  exact nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

private theorem MorseCancel.nativeLowerMeridian_coordinates_mem_target {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    Degree.BeltPassage.lower (S.data q).radius s u.val v.val ∈
      (S.data q).chart.splitChart.target := by
  have hh :=
    Degree.BeltPassage.upper_mem_block (S.data q).radius_pos
      (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)
      (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  exact (S.data q).block ⟨hh.2, hh.1⟩

private theorem MorseCancel.nativeLowerMeridian_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    f
        ((S.data q).chart.splitChart.symm
          (Degree.BeltPassage.lower (S.data q).radius s u.val v.val)) =
      S.toSurgeryWindows.lower q := by
  rw [(S.data q).chart.splitChart_inverse_equation
      (nativeLowerMeridian_coordinates_mem_target S q u v s)]
  have hh :=
    Degree.BeltPassage.upper_height (S.data q).radius (s : ℝ)
      (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  change
    -‖(Degree.BeltPassage.lower (S.data q).radius s u.val v.val).2‖ ^ 2 +
        ‖(Degree.BeltPassage.lower (S.data q).radius s u.val v.val).1‖ ^ 2 =
      (S.data q).radius ^ 2 at hh
  dsimp only [Smale.ManifoldMorse.SurgeryWindows.lower]
  linarith

private def
    MorseCancel.nativeLowerMeridianFamily {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    C(unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      (S.data q).LowerLevel)
    where
  toFun
    z :=
    ⟨(S.data q).chart.splitChart.symm
        (Degree.BeltPassage.lower (S.data q).radius z.1 z.2.val v.val),
      nativeLowerMeridian_height S q z.2 v z.1⟩
  continuous_toFun := by
    have hsize :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hdir :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hcoords :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          Degree.BeltPassage.lower (S.data q).radius (z.1 : ℝ) z.2.val v.val) := by
      unfold Degree.BeltPassage.lower
      exact
        ((continuous_const.mul
                  (Real.continuous_sqrt.comp (continuous_const.add (hsize.pow 2)))).smul
              hdir).prodMk
          ((continuous_const.mul hsize).smul continuous_const)
    exact
      ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hcoords
            (fun z => nativeLowerMeridian_coordinates_mem_target S q z.2 v z.1)).subtype_mk
        _

private def MorseCancel.nativeLowerMeridian {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).LowerLevel) :=
  (nativeLowerMeridianFamily S q v).comp ((ContinuousMap.const _ s).prodMk (ContinuousMap.id _))

private def MorseCancel.nativeUpperMeridian {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).UpperLevel)
    where
  toFun
    u :=
    ⟨nativeBeltArc S q u v s,
      nativeBeltArc_height S q u v (by rw [abs_of_nonneg s.property.1]; exact s.property.2)⟩
  continuous_toFun := by
    have hcoords :
      Continuous
        (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          Degree.BeltPassage.upper (S.data q).radius (s : ℝ) u.val v.val) := by
      unfold Degree.BeltPassage.upper
      have hneg :
        Continuous
          (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
            ((S.data q).radius * (s : ℝ)) • u.val) :=
        (continuous_subtype_val :
              Continuous
                (fun u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
                  u.val)).const_smul
          ((S.data q).radius * (s : ℝ))
      have hpos :
        Continuous
          (fun _ : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
            ((S.data q).radius * Real.sqrt (1 + (s : ℝ) ^ 2)) • v.val) :=
        continuous_const
      exact hneg.prodMk hpos
    exact
      ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hcoords
            (fun u =>
              nativeBeltArc_coordinates_mem_target S q u v
                (by rw [abs_of_nonneg s.property.1]; exact s.property.2))).subtype_mk
        _

private theorem MorseCancel.nativeLowerMeridian_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeLowerMeridian S q v 0 = (S.data q).surgery.attachingSphere := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change
    (S.data q).chart.splitChart.symm (Degree.BeltPassage.lower (S.data q).radius 0 u.val v.val) =
      _
  rw [Degree.BeltPassage.lower_zero, (S.data q).attaching_eq,
    (S.data q).chart.attachingCoreMap_coe]

private theorem MorseCancel.nativeUpperMeridian_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    S.flow (Degree.BeltPassage.time s) ((nativeUpperMeridian S q v s) u).val =
      ((nativeLowerMeridian S q v s) u).val :=
  S.flow_belt_passage q hs s.property.2 u v

private theorem
    MorseCancel.nativeLowerMeridian_homotopic_attaching {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    (nativeLowerMeridian S q v s).Homotopic (S.data q).surgery.attachingSphere := by
  let shrink : C(unitInterval, unitInterval) :=
    ⟨fun t => unitInterval.symm t * s, unitInterval.continuous_symm.mul continuous_const⟩
  have h0 : shrink 0 = s := by simp [shrink]
  have h1 : shrink 1 = 0 := by simp [shrink]
  let H : (nativeLowerMeridian S q v s).Homotopy (S.data q).surgery.attachingSphere :=
    { toFun := fun z => nativeLowerMeridianFamily S q v (shrink z.1, z.2)
      continuous_toFun :=
        (nativeLowerMeridianFamily S q v).continuous.comp
          ((shrink.continuous.comp continuous_fst).prodMk continuous_snd)
      map_zero_left := by
        intro u
        rw [h0]
        rfl
      map_one_left := by
        intro u
        rw [h1]
        exact
          congrArg
            (fun g :
                C(Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                  (S.data q).LowerLevel) =>
              g u)
            (nativeLowerMeridian_zero S q v) }
  exact ⟨H⟩

private theorem MorseCancel.nativeUpperMeridian_avoids_belt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    nativeUpperMeridian S q v s u ∉ Set.range (S.data q).surgery.beltSphere := by
  rintro ⟨w, hw⟩
  have he :=
    (nativeBeltArc_belt_eq_iff S q u v w
          (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)).mp
      (congrArg Subtype.val hw.symm)
  exact hs.ne' he.1

private theorem Smale.NativeSubmersion.surjective_fderiv_sourceChart_iff {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    (c : PartialDiffeomorph I 𝓘(ℝ, E) X E ∞) {f : X → F} {z : E} (hz : z ∈ c.target)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f (c.symm z)) :
    Function.Surjective (fderiv ℝ (f ∘ c.symm) z) ↔
      Function.Surjective (mfderiv I 𝓘(ℝ, F) f (c.symm z)) := by
  let A : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f (c.symm z)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  have hd : fderiv ℝ (f ∘ c.symm) z = A.comp B := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp z hf (c.symm.mdifferentiableAt (by simp) hz)
  have hB : Function.Surjective B := (Smale.PartialChart.bijective_mfderiv c.symm hz).surjective
  rw [hd]
  change Function.Surjective (A.comp B) ↔ Function.Surjective A
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨B v, hv⟩
  · intro h
    exact h.comp hB

private theorem Smale.NativeSubmersion.isOpen_surjective_nativeDerivative {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [I.Boundaryless] [IsManifold I ∞ X] {f : P → X → F} {W : Set (P × X)}
    (hW : IsOpen W) (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ (Function.uncurry f) W)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsOpen {q : P × X | q ∈ W ∧ Function.Surjective (mfderiv I 𝓘(ℝ, F) (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqsurj⟩
  let c := NoExotic.modelChartPartialDiffeomorph (I := I) q.2
  have hqc : q.2 ∈ c.source := mem_extChartAt_source q.2
  let Q : Set (P × E) := Set.univ ×ˢ c.target
  let C : P × E → P × X := fun r => (r.1, c.symm r.2)
  have hQ : IsOpen Q := isOpen_univ.prod c.open_target
  have hC : ContMDiffOn 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod I) ∞ C Q :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (c.contMDiffOn_invFun.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hr => hr.2))
  let U : Set (P × E) := Q ∩ C ⁻¹' W
  have hU : IsOpen U := hC.continuousOn.isOpen_inter_preimage hQ hW
  have hcoord : ContDiffOn ℝ ∞ (fun r : P × E => f r.1 (c.symm r.2)) U :=
    (hf.comp (hC.mono Set.inter_subset_left) (fun _ hr => hr.2)).contDiffOn
  have hspatial :=
    Smale.MorsePerturbation.contDiffOn_spatialDerivative (f := fun a z => f a (c.symm z)) hU
      hcoord
  have hopen : IsOpen {A : E →L[ℝ] F | Function.Surjective A} := by
    have heq : {A : E →L[ℝ] F | Function.Surjective A} = {A : E →L[ℝ] F | Function.Injective A} :=
      by
      ext A
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).symm
    rw [heq]
    exact ContinuousLinearMap.isOpen_injective
  let V : Set (P × E) :=
    U ∩
      (fun r => fderiv ℝ (fun z => f r.1 (c.symm z)) r.2) ⁻¹'
        {A : E →L[ℝ] F | Function.Surjective A}
  have hV : IsOpen V := hspatial.continuousOn.isOpen_inter_preimage hU hopen
  have hiff (r : P × E) (hr : r ∈ U) :
    Function.Surjective (fderiv ℝ (fun z => f r.1 (c.symm z)) r.2) ↔
      Function.Surjective (mfderiv I 𝓘(ℝ, F) (f r.1) (c.symm r.2)) := by
    have hfr : ContMDiffAt I 𝓘(ℝ, F) ∞ (f r.1) (c.symm r.2) :=
      (hf.contMDiffAt (hW.mem_nhds hr.2)).comp (c.symm r.2)
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact surjective_fderiv_sourceChart_iff c hr.1.2 (hfr.mdifferentiableAt (by simp))
  have hleft : c.symm (c q.2) = q.2 := c.left_inv' hqc
  have hqU : (q.1, c q.2) ∈ U := by
    refine ⟨⟨Set.mem_univ _, c.map_source' hqc⟩, ?_⟩
    change (q.1, c.symm (c q.2)) ∈ W
    rw [hleft]
    exact hq
  have hqV : (q.1, c q.2) ∈ V := by
    refine ⟨hqU, (hiff _ hqU).mpr ?_⟩
    exact hleft.symm ▸ hqsurj
  have hforward : ContinuousAt (fun r : P × X => (r.1, c r.2)) q :=
    continuousAt_fst.prodMk
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hqc)).continuousAt.comp
        continuousAt_snd)
  have hn := hforward.preimage_mem_nhds (hV.mem_nhds hqV)
  have hnc : ∀ᶠ r : P × X in 𝓝 q, r.2 ∈ c.source :=
    continuous_snd.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hqc)
  apply Filter.mem_of_superset (Filter.inter_mem hn hnc)
  intro r hr
  have hleft' : c.symm (c r.2) = r.2 := c.left_inv' hr.2
  have hmem : (r.1, c.symm (c r.2)) ∈ W := hr.1.1.2
  have hsurj := (hiff (r.1, c r.2) hr.1.1).mp hr.1.2
  refine ⟨?_, hleft' ▸ hsurj⟩
  rwa [hleft'] at hmem

private theorem
    Smale.RegularValues.exists_null_exceptional_values_on {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → E}
    {s : Set E} (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    ∃ T : Set E, μ T = 0 ∧ ∀ x ∈ s, f x ∉ T → Function.Bijective (fderiv ℝ f x) := by
  let B : Set E := {x | x ∈ s ∧ (fderiv ℝ f x).det = 0}
  have hzero : μ (f '' B) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf x hx.1).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)
  refine ⟨f '' B, hzero, ?_⟩
  intro x hx hfx
  apply (bijective_iff_det_ne_zero _).mpr
  intro hdet
  exact hfx ⟨x, ⟨hx, hdet⟩, rfl⟩

private theorem Smale.RegularValues.exists_null_exceptional_values_in_chart {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] [MeasurableSpace F] [BorelSpace F]
    (μ : MeasureTheory.Measure F) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (c : PartialDiffeomorph I 𝓘(ℝ, E) X E ∞) {f : X → F} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ T : Set F,
      μ T = 0 ∧ ∀ x ∈ c.source ∩ s, f x ∉ T → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hdim
  let W : Set F := L '' (c.target ∩ c.symm ⁻¹' s)
  let G : F → F := fun z => f (c.symm (L.symm z))
  have hcoord (z : F) (hz : z ∈ W) : L.symm z ∈ c.target ∧ c.symm (L.symm z) ∈ s := by
    obtain ⟨w, hw, rfl⟩ := hz
    rw [L.symm_apply_apply]
    exact hw
  have hsmooth (z : F) (hz : z ∈ W) : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ G z := by
    have hh := hcoord z hz
    exact
      (hf.contMDiffAt (hs.mem_nhds hh.2)).comp z
        ((c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hh.1)).comp z
          L.symm.contDiff.contMDiff.contMDiffAt)
  obtain ⟨T, hT, hgood⟩ :=
    exists_null_exceptional_values_on μ
      (fun z hz => (hsmooth z hz).mdifferentiableAt (by simp) |>.differentiableAt)
  refine ⟨T, hT, ?_⟩
  intro x hx hfx
  let z := L (c x)
  have hz : z ∈ W := by
    refine ⟨c x, ⟨c.map_source' hx.1, ?_⟩, rfl⟩
    change c.symm (c x) ∈ s
    have heq : c.symm (c x) = x := c.left_inv' hx.1
    rw [heq]
    exact hx.2
  have hpoint : c.symm (L.symm z) = x := by
    change c.symm (L.symm (L (c x))) = x
    rw [L.symm_apply_apply]
    exact c.left_inv' hx.1
  have hvalue : G z = f x := congrArg f hpoint
  have hbij := hgood z hz (by rwa [hvalue])
  have hfx' : MDifferentiableAt I 𝓘(ℝ, F) f (c.symm (L.symm z)) :=
    (hf.contMDiffAt (hs.mem_nhds (hcoord z hz).2)).mdifferentiableAt (by simp)
  have hinner : MDifferentiableAt 𝓘(ℝ, F) I (c.symm ∘ L.symm) z :=
    (c.symm.mdifferentiableAt (by simp) (hcoord z hz).1).comp z
      L.symm.toContinuousLinearMap.differentiableAt.mdifferentiableAt
  rw [← mfderiv_eq_fderiv] at hbij
  change Function.Bijective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (f ∘ (c.symm ∘ L.symm)) z) at hbij
  rw [mfderiv_comp z hfx' hinner] at hbij
  have hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, F) f (c.symm (L.symm z))) := by
    intro w
    obtain ⟨v, hv⟩ := hbij.surjective w
    exact ⟨mfderiv 𝓘(ℝ, F) I (c.symm ∘ L.symm) z v, hv⟩
  exact hpoint ▸ hsurj

private theorem Smale.RegularValues.exists_null_exceptional_values_manifold {E F H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [MeasurableSpace F] [BorelSpace F] (μ : MeasureTheory.Measure F)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] [LindelofSpace X] {f : X → F} {s : Set X}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ T : Set F, μ T = 0 ∧ ∀ x ∈ s, f x ∉ T → Function.Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  classical
  let c (x : X) := NoExotic.modelChartPartialDiffeomorph (I := I) x
  let U : X → Set X := fun x => (c x).source
  have hU : ∀ x, IsOpen (U x) := fun x => (c x).open_source
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let _ := htcount.to_subtype
  choose T hT hgood using fun i : t => exists_null_exceptional_values_in_chart μ (c i) hs hf hdim
  refine ⟨⋃ i : t, T i, MeasureTheory.measure_iUnion_null hT, ?_⟩
  intro x hx hfx
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  apply hgood ⟨i, hit⟩ x ⟨hxi, hx⟩
  intro hi
  exact hfx (Set.mem_iUnion.mpr ⟨⟨i, hit⟩, hi⟩)

private theorem Smale.TransverseCoordinates.mfderiv_sheetDifference {D Z F H K X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ Z K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace K Y] {f : X → F} {g : Y → F} {x : X}
    {y : Y} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt J 𝓘(ℝ, F) g y) :
    (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y) : D × Z →L[ℝ] F) =
      (-(mfderiv I 𝓘(ℝ, F) f x : D →L[ℝ] F)).coprod (mfderiv J 𝓘(ℝ, F) g y : Z →L[ℝ] F) := by
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change
    (mfderiv (I.prod J) 𝓘(ℝ, F) (g ∘ Prod.snd - f ∘ Prod.fst) (x, y) : D × Z →L[ℝ] F) =
      (-A).coprod B
  have hf' : MDifferentiableAt (I.prod J) 𝓘(ℝ, F) (f ∘ Prod.fst) (x, y) :=
    hf.comp (x, y) mdifferentiableAt_fst
  have hg' : MDifferentiableAt (I.prod J) 𝓘(ℝ, F) (g ∘ Prod.snd) (x, y) :=
    hg.comp (x, y) mdifferentiableAt_snd
  rw [mfderiv_sub hg' hf', mfderiv_comp (x, y) hg mdifferentiableAt_snd,
    mfderiv_comp (x, y) hf mdifferentiableAt_fst, mfderiv_fst, mfderiv_snd]
  apply ContinuousLinearMap.ext
  intro v
  change B v.2 - A v.1 = -(A v.1) + B v.2
  abel

private theorem Smale.TransverseCoordinates.surjective_sheetDifference_iff {D Z F H K X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ Z K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace K Y] {f : X → F} {g : Y → F} {x : X}
    {y : Y} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt J 𝓘(ℝ, F) g y) :
    Function.Surjective (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y)) ↔
      Function.Surjective
        ((mfderiv I 𝓘(ℝ, F) f x : D →L[ℝ] F).coprod (mfderiv J 𝓘(ℝ, F) g y : Z →L[ℝ] F)) := by
  rw [mfderiv_sheetDifference hf hg]
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change Function.Surjective ((-A).coprod B) ↔ Function.Surjective (A.coprod B)
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h w
    refine ⟨(-v.1, v.2), ?_⟩
    change A (-v.1) + B v.2 = w
    change -(A v.1) + B v.2 = w at hv
    simpa only [map_neg] using hv
  · intro h w
    obtain ⟨v, hv⟩ := h w
    refine ⟨(-v.1, v.2), ?_⟩
    change -(A (-v.1)) + B v.2 = w
    change A v.1 + B v.2 = w at hv
    simpa only [map_neg, neg_neg] using hv

private theorem Smale.TransverseCoordinates.exists_null_exceptional_native_translations
    {D Z F H K X Y : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ Z K} [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace K Y] [IsManifold J ∞ Y] [LindelofSpace (X × Y)] [MeasurableSpace F]
    [BorelSpace F] (μ : MeasureTheory.Measure F) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : X → F} {g : Y → F} {U : Set X} {V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U) (hg : ContMDiffOn J 𝓘(ℝ, F) ∞ g V)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) :
    ∃ T : Set F,
      μ T = 0 ∧
        ∀ a ∉ T,
          ∀ x ∈ U,
            ∀ y ∈ V,
              g y = f x + a →
                Function.Surjective ((mfderiv I 𝓘(ℝ, F) f x).coprod (mfderiv J 𝓘(ℝ, F) g y)) := by
  let B : X × Y → F := fun z => g z.2 - f z.1
  have hB : ContMDiffOn (I.prod J) 𝓘(ℝ, F) ∞ B (U ×ˢ V) := by
    intro z hz
    have hfx : ContMDiffAt (I.prod J) 𝓘(ℝ, F) ∞ (fun w : X × Y => f w.1) z :=
      (hf.contMDiffAt (hU.mem_nhds hz.1)).comp z contMDiffAt_fst
    have hgy : ContMDiffAt (I.prod J) 𝓘(ℝ, F) ∞ (fun w : X × Y => g w.2) z :=
      (hg.contMDiffAt (hV.mem_nhds hz.2)).comp z contMDiffAt_snd
    exact (hgy.sub hfx).contMDiffWithinAt
  obtain ⟨T, hT, hgood⟩ :=
    Smale.RegularValues.exists_null_exceptional_values_manifold μ (hU.prod hV) hB
      (by simpa only [Module.finrank_prod] using hdim)
  refine ⟨T, hT, ?_⟩
  intro a ha x hx y hy hxy
  have hvalue : B (x, y) = a := by
    change g y - f x = a
    rw [hxy, add_sub_cancel_left]
  have hs := hgood (x, y) ⟨hx, hy⟩ (by rwa [hvalue])
  change
    Function.Surjective (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y)) at hs
  rw [mfderiv_sheetDifference ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hg.contMDiffAt (hV.mem_nhds hy)).mdifferentiableAt (by simp))] at hs
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B' : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change Function.Surjective ((-A).coprod B') at hs
  change Function.Surjective (A.coprod B')
  intro w
  obtain ⟨v, hv⟩ := hs w
  refine ⟨(-v.1, v.2), ?_⟩
  change A (-v.1) + B' v.2 = w
  change -(A v.1) + B' v.2 = w at hv
  simpa only [map_neg] using hv

private theorem Smale.TransverseCoordinates.dense_native_translations {D Z F H K X Y : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {J : ModelWithCorners ℝ Z K} [I.Boundaryless] [J.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace K Y]
    [IsManifold J ∞ Y] [LindelofSpace (X × Y)] {f : X → F} {g : Y → F} {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U)
    (hg : ContMDiffOn J 𝓘(ℝ, F) ∞ g V)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) :
    Dense
      {a : F |
        ∀ x ∈ U,
          ∀ y ∈ V,
            g y = f x + a →
              Function.Surjective ((mfderiv I 𝓘(ℝ, F) f x).coprod (mfderiv J 𝓘(ℝ, F) g y))} := by
  let _ : MeasurableSpace F := borel F
  let _ : BorelSpace F := ⟨rfl⟩
  let μ : MeasureTheory.Measure F := MeasureTheory.Measure.addHaar
  obtain ⟨T, hT, hgood⟩ := exists_null_exceptional_native_translations μ hU hV hf hg hdim
  have hdense : Dense Tᶜ := by
    apply μ.dense_of_ae
    rw [MeasureTheory.ae_iff]
    simpa only [Set.mem_compl_iff, Classical.not_not, Set.ofPred_mem_eq] using hT
  exact hdense.mono hgood

private theorem Smale.ChartMapPerturbation.mfderiv_eq_of_translation_germ {D F H X : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X] [ChartedSpace H X]
    {u v : X → F} {a : F} {x : X} (hu : MDifferentiableAt I 𝓘(ℝ, F) u x)
    (hevent : v =ᶠ[𝓝 x] fun z => u z + a) :
    (mfderiv I 𝓘(ℝ, F) v x : D →L[ℝ] F) = mfderiv I 𝓘(ℝ, F) u x := by
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) u x
  let C : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (fun _ : X => a) x
  have hC : C = 0 := mfderiv_const
  have hh :=
    mfderiv_add hu
      (show MDifferentiableAt I 𝓘(ℝ, F) (fun _ : X => a) x from mdifferentiableAt_const)
  change (mfderiv I 𝓘(ℝ, F) (fun z => u z + a) x : D →L[ℝ] F) = A + C at hh
  rw [hC] at hh
  exact hevent.mfderiv_eq.trans (hh.trans (add_zero A))

private theorem Smale.ChartMapPerturbation.transverse_of_chart {D Z G F H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X}
    {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ c.source)
    (ht :
      Function.Surjective
        ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
          (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F))) :
    Function.Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have heq : (C.comp A).coprod (C.comp B) = C.comp (A.coprod B) := by
    apply ContinuousLinearMap.ext
    intro v
    change C (A v.1) + C (B v.2) = C (A v.1 + B v.2)
    exact (C.map_add _ _).symm
  rw [hA, hB] at ht
  change Function.Surjective ((C.comp A).coprod (C.comp B)) at ht
  rw [heq] at ht
  have hC : Function.Injective C := (Smale.PartialChart.bijective_mfderiv c hx).injective
  change Function.Surjective (A.coprod B)
  intro w
  obtain ⟨v, hv⟩ := ht (C w)
  exact ⟨v, hC hv⟩

private theorem Smale.ChartMapPerturbation.transverse_in_chart {D Z G F H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X}
    {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ c.source)
    (ht :
      Function.Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G))) :
    Function.Surjective
      ((mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F).coprod
        (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F)) := by
  let A : D →L[ℝ] G := mfderiv I J f x
  let B : Z →L[ℝ] G := mfderiv I' J g y
  let C : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) c (f x)
  have hy : g y ∈ c.source := hxy ▸ hx
  have hA : (mfderiv I 𝓘(ℝ, F) (c ∘ f) x : D →L[ℝ] F) = C.comp A :=
    mfderiv_comp x (c.mdifferentiableAt (by simp) hx) hf
  have hB : (mfderiv I' 𝓘(ℝ, F) (c ∘ g) y : Z →L[ℝ] F) = C.comp B := by
    rw [mfderiv_comp y (c.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  rw [hA, hB]
  change Function.Surjective ((C.comp A).coprod (C.comp B))
  have hC : Function.Surjective C := (Smale.PartialChart.bijective_mfderiv c hx).surjective
  change Function.Surjective (A.coprod B) at ht
  intro w
  obtain ⟨z, hz⟩ := hC w
  obtain ⟨v, hv⟩ := ht z
  refine ⟨v, ?_⟩
  change C (A v.1) + C (B v.2) = w
  rw [← C.map_add]
  exact (congrArg C hv).trans hz

private def Smale.NativeTransversality.At {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    (I : ModelWithCorners ℝ D H) (I' : ModelWithCorners ℝ Z H') (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [TopologicalSpace N] [ChartedSpace K N] (f : X → N) (g : Y → N) (x : X) (y : Y) : Prop :=
  g y = f x →
    Function.Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G))

private theorem Smale.NativeTransversality.at_iff_chart_difference {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X}
    {y : Y} (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ c.source) :
    At I I' J f g x y ↔
      Function.Surjective
        (mfderiv (I.prod I') 𝓘(ℝ, F) (fun z : X × Y => c (g z.2) - c (f z.1)) (x, y)) := by
  have hy : g y ∈ c.source := hxy ▸ hx
  have hcf := (c.mdifferentiableAt (by simp) hx).comp x hf
  have hcg := (c.mdifferentiableAt (by simp) hy).comp y hg
  have hdiff := Smale.TransverseCoordinates.surjective_sheetDifference_iff hcf hcg
  constructor
  · intro ht
    apply hdiff.mpr
    exact Smale.ChartMapPerturbation.transverse_in_chart c hf hg hxy hx (ht hxy)
  · intro h _
    exact Smale.ChartMapPerturbation.transverse_of_chart c hf hg hxy hx (hdiff.mp h)

private theorem Smale.NativeTransversality.isOpen_at_family {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ G]
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [IsManifold I ∞ X] [IsManifold I' ∞ Y]
    [IsManifold J ∞ N] [T2Space N] {f : P → X → N} {g : Y → N} {U : Set P} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (Function.uncurry f) (U ×ˢ Set.univ))
    (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) :
    IsOpen {r : P × (X × Y) | r.1 ∈ U ∧ At I I' J (f r.1) g r.2.1 r.2.2} := by
  let W₀ : Set (P × (X × Y)) := U ×ˢ Set.univ
  have hW₀ : IsOpen W₀ := hU.prod isOpen_univ
  let F : P × (X × Y) → N := fun r => f r.1 r.2.1
  let G' : P × (X × Y) → N := fun r => g r.2.2
  have hF : ContMDiffOn (𝓘(ℝ, P).prod (I.prod I')) J ∞ F W₀ :=
    hf.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).contMDiffOn
      (fun _ hr => ⟨hr.1, Set.mem_univ _⟩)
  have hG : ContMDiff (𝓘(ℝ, P).prod (I.prod I')) J ∞ G' :=
    hg.comp (contMDiff_snd.comp contMDiff_snd)
  have hslice (a : P) (x : X) (ha : a ∈ U) : ContMDiffAt I J ∞ (f a) x :=
    (hf.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ha, Set.mem_univ x⟩)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqt⟩
  have hq₀ : q ∈ W₀ := ⟨hq, Set.mem_univ _⟩
  by_cases hcross : g q.2.2 = f q.1 q.2.1
  · let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f q.1 q.2.1)
    have hqc : f q.1 q.2.1 ∈ c.source := mem_extChartAt_source _
    have hqgc : g q.2.2 ∈ c.source := hcross ▸ hqc
    let W : Set (P × (X × Y)) := (W₀ ∩ F ⁻¹' c.source) ∩ G' ⁻¹' c.source
    have hW : IsOpen W :=
      (hF.continuousOn.isOpen_inter_preimage hW₀ c.open_source).inter
        (c.open_source.preimage hG.continuous)
    let B : P → X × Y → G := fun a z => c (g z.2) - c (f a z.1)
    have hB : ContMDiffOn (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞ (Function.uncurry B) W := by
      intro r hr
      have hfirst :
        ContMDiffAt (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞ (fun s : P × (X × Y) => c (f s.1 s.2.1))
          r :=
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.1.2)).comp r
          (hF.contMDiffAt (hW₀.mem_nhds hr.1.1))
      have hsecond :
        ContMDiffAt (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞ (fun s : P × (X × Y) => c (g s.2.2)) r :=
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.2)).comp r hG.contMDiffAt
      exact (hsecond.sub hfirst).contMDiffWithinAt
    have hopen :=
      Smale.NativeSubmersion.isOpen_surjective_nativeDerivative hW hB
        (by simpa only [Module.finrank_prod] using hdim)
    have hqB : Function.Surjective (mfderiv (I.prod I') 𝓘(ℝ, G) (B q.1) q.2) :=
      (at_iff_chart_difference c ((hslice q.1 q.2.1 hq).mdifferentiableAt (by simp))
            (hg.mdifferentiableAt (by simp)) hcross hqc).mp
        hqt
    have hn :=
      hopen.mem_nhds
        (show q ∈ {r | r ∈ W ∧ Function.Surjective (mfderiv (I.prod I') 𝓘(ℝ, G) (B r.1) r.2)} from
          ⟨⟨⟨hq₀, hqc⟩, hqgc⟩, hqB⟩)
    apply Filter.mem_of_superset hn
    intro r hr
    refine ⟨hr.1.1.1.1, ?_⟩
    intro hxy
    have ht :=
      (at_iff_chart_difference c ((hslice r.1 r.2.1 hr.1.1.1.1).mdifferentiableAt (by simp))
            (hg.mdifferentiableAt (by simp)) hxy hr.1.1.2).mpr
        hr.2
    exact ht hxy
  · have hpair : ContinuousAt (fun r : P × (X × Y) => (G' r, F r)) q :=
      hG.continuous.continuousAt.prodMk (hF.contMDiffAt (hW₀.mem_nhds hq₀)).continuousAt
    have hne : IsOpen {z : N × N | z.1 ≠ z.2} := isOpen_ne_fun continuous_fst continuous_snd
    have hn := hpair.preimage_mem_nhds (hne.mem_nhds hcross)
    have hparam : ∀ᶠ r : P × (X × Y) in 𝓝 q, r.1 ∈ U :=
      continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hq)
    apply Filter.mem_of_superset (Filter.inter_mem hparam hn)
    intro r hr
    refine ⟨hr.1, ?_⟩
    intro hxy
    exact False.elim (hr.2 hxy)

private theorem Smale.NativeTransversality.eventually_on_compact {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ G]
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [IsManifold I ∞ X] [IsManifold I' ∞ Y]
    [IsManifold J ∞ N] [T2Space N] {f : P → X → N} {g : Y → N} {U : Set P} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (Function.uncurry f) (U ×ˢ Set.univ))
    (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {C : Set (X × Y)}
    (hC : IsCompact C) {a : P} (ha : a ∈ U) (htrans : ∀ z ∈ C, At I I' J (f a) g z.1 z.2) :
    ∀ᶠ b in 𝓝 a, ∀ z ∈ C, At I I' J (f b) g z.1 z.2 := by
  have hopen :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact hC (isOpen_at_family hU hf hg hdim)
  have hn := hopen.mem_nhds (fun z hz => ⟨ha, htrans z hz⟩)
  filter_upwards [hn] with b hb z hz
  exact (hb z hz).2

private theorem Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff
    {A B Z E HA HB HZ HE X Y N M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HA] [TopologicalSpace HB]
    [TopologicalSpace HZ] [TopologicalSpace HE] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} {J : ModelWithCorners ℝ Z HZ} {J' : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    [TopologicalSpace N] [ChartedSpace HZ N] [TopologicalSpace M] [ChartedSpace HE M]
    (P : PartialDiffeomorph J J' N M ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y) (hxy : g y = f x)
    (hx : f x ∈ P.source) :
    Smale.NativeTransversality.At I I' J f g x y ↔
      Smale.NativeTransversality.At I I' J' (P ∘ f) (P ∘ g) x y := by
  let L : A →L[ℝ] Z := mfderiv I J f x
  let R : B →L[ℝ] Z := mfderiv I' J g y
  let C : Z →L[ℝ] E := mfderiv J J' P (f x)
  have hy : g y ∈ P.source := hxy ▸ hx
  have hL : (mfderiv I J' (P ∘ f) x : A →L[ℝ] E) = C.comp L :=
    mfderiv_comp x (P.mdifferentiableAt (by simp) hx) hf
  have hR : (mfderiv I' J' (P ∘ g) y : B →L[ℝ] E) = C.comp R := by
    rw [mfderiv_comp y (P.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have hC : Function.Bijective C := Smale.PartialChart.bijective_mfderiv P hx
  constructor
  · intro ht _
    have hsum : Function.Surjective (L.coprod R) := ht hxy
    rw [hL, hR]
    intro w
    obtain ⟨z, hz⟩ := hC.surjective w
    obtain ⟨v, hv⟩ := hsum z
    refine ⟨v, ?_⟩
    change C (L v.1) + C (R v.2) = w
    rw [← C.map_add]
    exact (congrArg C hv).trans hz
  · intro ht _
    have hsum := ht (show (P ∘ g) y = (P ∘ f) x from congrArg P hxy)
    rw [hL, hR] at hsum
    intro w
    obtain ⟨v, hv⟩ := hsum (C w)
    refine ⟨v, hC.injective ?_⟩
    change C (L v.1 + R v.2) = C w
    rw [C.map_add]
    exact hv

private theorem Smale.MorseHandle.ambientMap_lower_sphere {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (u : Metric.sphere (0 : N) 1) (v : P) :
    -‖(ambientMap ρ ((u : N), v)).1‖ ^ 2 + ‖(ambientMap ρ ((u : N), v)).2‖ ^ 2 = -(ρ ^ 2) := by
  have hA : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  simp only [ambientMap, norm_smul, Real.norm_eq_abs, abs_of_pos hA, abs_of_pos hρ,
    mem_sphere_zero_iff_norm.mp u.property, mul_one, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖v‖ ^ 2 by positivity)]
  ring

private theorem Smale.MorseHandle.ambientMap_sphere_mem_product {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (u : Metric.sphere (0 : N) 1) (v : P) (hv : ‖v‖ ≤ (3 / 2 : ℝ)) :
    ambientMap ρ ((u : N), v) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hA : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hs : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg v]⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + ‖v‖ ^ 2)) • (u : N)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA, mem_sphere_zero_iff_norm.mp u.property,
      mul_one]
    calc
      _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hs hρ.le
      _ = _ := mul_comm _ _
  · rw [mem_closedBall_zero_iff]
    change ‖ρ • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hm := mul_le_mul_of_nonneg_left hv hρ.le
    linarith

private theorem
    Smale.MorseHandle.norm_ambientInverse_fst_of_lower {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P)
    (hz : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = -(ρ ^ 2)) : ‖(ambientInverse ρ z).1‖ = 1 := by
  let A : ℝ := ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)
  have hA : 0 < A := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hA₂ : A ^ 2 = ρ ^ 2 + ‖z.2‖ ^ 2 := inverse_scale_sq hρ z.2
  have hn : ‖z.1‖ = A := by nlinarith [norm_nonneg z.1]
  change ‖A⁻¹ • z.1‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), hn, inv_mul_cancel₀ hA.ne']

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.SignedMorseChart.beltRawCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ)
    (z : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :
    c.NegativeCoordinates × c.PositiveCoordinates :=
  (Smale.MorseHandle.ambientMap ρ ((z.1 : c.PositiveCoordinates), z.2)).swap

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.continuous_beltRawCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltRawCoordinates ρ) :=
  continuous_swap.comp
    ((Smale.MorseHandle.ambientHomeomorph ρ hρ).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.beltSource {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    TopologicalSpace.Opens
      (Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates × c.NegativeCoordinates) :=
  ⟨c.beltRawCoordinates ρ ⁻¹' c.splitChart.target,
    c.splitChart.open_target.preimage (c.continuous_beltRawCoordinates ρ hρ)⟩

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.beltTarget {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) :
    TopologicalSpace.Opens { y : M // f y = f p + ρ ^ 2 } :=
  ⟨Subtype.val ⁻¹' c.splitChart.source, c.splitChart.open_source.preimage continuous_subtype_val⟩

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) : c.beltTarget ρ :=
  ⟨⟨c.splitChart.symm (c.beltRawCoordinates ρ z.val),
      by
      rw [c.splitChart_inverse_equation z.property]
      have hh := Smale.MorseHandle.ambientMap_lower_sphere hρ z.val.1 z.val.2
      change
        -‖(c.beltRawCoordinates ρ z.val).2‖ ^ 2 + ‖(c.beltRawCoordinates ρ z.val).1‖ ^ 2 =
          -(ρ ^ 2) at hh
      linarith⟩,
    c.splitChart.map_target' z.property⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.continuous_beltNeighborhoodMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodMap ρ hρ) := by
  have hc :
    Continuous (fun z : c.beltSource ρ hρ => c.splitChart.symm (c.beltRawCoordinates ρ z.val)) :=
    c.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous
      ((c.continuous_beltRawCoordinates ρ hρ).comp continuous_subtype_val) (fun z => z.property)
  exact (hc.subtype_mk _).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.beltInverseCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (y : M) :
    c.PositiveCoordinates × c.NegativeCoordinates :=
  Smale.MorseHandle.ambientInverse ρ (c.splitChart y).swap

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.continuousOn_beltInverseCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    ContinuousOn (c.beltInverseCoordinates ρ) c.splitChart.source :=
  (Smale.MorseHandle.ambientHomeomorph ρ hρ).symm.continuous.comp_continuousOn
    (continuous_swap.comp_continuousOn c.splitChart.contMDiffOn_toFun.continuousOn)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.beltInverseCoordinates_neighborhoodMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) :
    c.beltInverseCoordinates ρ ((c.beltNeighborhoodMap ρ hρ z).val : M) =
      ((z.val.1 : c.PositiveCoordinates), z.val.2) := by
  have hr :
    c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val)) =
      c.beltRawCoordinates ρ z.val :=
    c.splitChart.right_inv' z.property
  change
    Smale.MorseHandle.ambientInverse ρ
        (c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val))).swap =
      _
  rw [hr]
  exact Smale.MorseHandle.ambientInverse_ambientMap hρ _

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.norm_beltInverseCoordinates_fst {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (y : { y : M // f y = f p + ρ ^ 2 }) (hy : (y : M) ∈ c.splitChart.source) :
    ‖(c.beltInverseCoordinates ρ y).1‖ = 1 := by
  apply Smale.MorseHandle.norm_ambientInverse_fst_of_lower hρ
  have hh := c.splitChart_equation hy
  rw [y.property] at hh
  change -‖(c.splitChart (y : M)).2‖ ^ 2 + ‖(c.splitChart (y : M)).1‖ ^ 2 = -(ρ ^ 2)
  linarith

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodInverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (y : c.beltTarget ρ) : c.beltSource ρ hρ := by
  let v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates :=
    ⟨(c.beltInverseCoordinates ρ (y.val : M)).1,
      mem_sphere_zero_iff_norm.mpr (c.norm_beltInverseCoordinates_fst ρ hρ y.val y.property)⟩
  refine ⟨(v, (c.beltInverseCoordinates ρ (y.val : M)).2), ?_⟩
  change
    (Smale.MorseHandle.ambientMap ρ
          (Smale.MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap ∈
      c.splitChart.target
  rw [Smale.MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
  exact c.splitChart.map_source' y.property

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.continuous_beltNeighborhoodInverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.beltNeighborhoodInverse ρ hρ) := by
  have hc : Continuous (fun y : c.beltTarget ρ => c.beltInverseCoordinates ρ (y.val : M)) :=
    (c.continuousOn_beltInverseCoordinates ρ hρ).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property)
  exact ((hc.fst.subtype_mk _).prodMk hc.snd).subtype_mk _

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ) :
    c.beltSource ρ hρ ≃ₜ c.beltTarget ρ
    where
  toFun := c.beltNeighborhoodMap ρ hρ
  invFun := c.beltNeighborhoodInverse ρ hρ
  left_inv
    z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst (c.beltInverseCoordinates_neighborhoodMap ρ hρ z))
    · exact
        congrArg (fun w : c.PositiveCoordinates × c.NegativeCoordinates => w.2)
          (c.beltInverseCoordinates_neighborhoodMap ρ hρ z)
  right_inv
    y := by
    apply Subtype.ext
    apply Subtype.ext
    change
      c.splitChart.symm
          (Smale.MorseHandle.ambientMap ρ
              (Smale.MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)).swap)).swap =
        (y.val : M)
    rw [Smale.MorseHandle.ambientMap_ambientInverse hρ, Prod.swap_swap]
    exact c.splitChart.left_inv' y.property
  continuous_toFun := c.continuous_beltNeighborhoodMap ρ hρ
  continuous_invFun := c.continuous_beltNeighborhoodInverse ρ hρ

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.enlarged_closed_belt_subset_source {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    (Set.univ : Set (Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates)) ×ˢ
        Metric.closedBall (0 : c.NegativeCoordinates) (3 / 2 : ℝ) ⊆
      c.beltSource ρ hρ := by
  rintro ⟨v, u⟩ ⟨_, hu⟩
  have hh :=
    Smale.MorseHandle.ambientMap_sphere_mem_product hρ v u (mem_closedBall_zero_iff.mp hu)
  exact hblock ⟨hh.2, hh.1⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.beltNeighborhoodHomeomorph_normal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.beltSource ρ hρ) :
    (c.splitChart ((c.beltNeighborhoodHomeomorph ρ hρ z).val : M)).1 = ρ • z.val.2 := by
  have hr :
    c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val)) =
      c.beltRawCoordinates ρ z.val :=
    c.splitChart.right_inv' z.property
  change (c.splitChart (c.splitChart.symm (c.beltRawCoordinates ρ z.val))).1 = _
  rw [hr]
  rfl

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.beltNormalDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) : Set d.UpperLevel :=
  (Subtype.val : d.UpperLevel → M) ⁻¹' d.chart.splitChart.source

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.beltNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    d.UpperLevel → d.chart.NegativeCoordinates := fun x => (d.chart.splitChart (x : M)).1

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.isOpen_beltNormalDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) : IsOpen d.beltNormalDomain :=
  d.chart.splitChart.open_source.preimage continuous_subtype_val

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.belt_model_mem_target {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (0, d.radius • (v : d.chart.PositiveCoordinates)) ∈ d.chart.splitChart.target := by
  apply d.block
  constructor
  · simpa only [Metric.mem_closedBall, dist_self] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) d.radius_pos.le)
  · have hv : ‖(v : d.chart.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos d.radius_pos, hv, mul_one]
    linarith [d.radius_pos]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.belt_mem_normalDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.beltSphere v ∈ d.beltNormalDomain := by
  change (d.surgery.beltSphere v : M) ∈ d.chart.splitChart.source
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.map_target' (d.belt_model_mem_target v)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.belt_split_coordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.splitChart (d.surgery.beltSphere v : M) =
      (0, d.radius • (v : d.chart.PositiveCoordinates)) := by
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  exact d.chart.splitChart.right_inv' (d.belt_model_mem_target v)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.beltNormal_belt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.surgery.beltSphere v) = 0 := by
  change (d.chart.splitChart (d.surgery.beltSphere v : M)).1 = 0
  rw [d.belt_split_coordinates]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.beltNormal_eq_zero_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) {x : d.UpperLevel}
    (hx : x ∈ d.beltNormalDomain) : d.beltNormal x = 0 ↔ x ∈ Set.range d.surgery.beltSphere := by
  constructor
  · intro hzero
    let z := d.chart.splitChart (x : M)
    have hz₁ : z.1 = 0 := hzero
    have heq := d.chart.splitChart_equation hx
    change f (x : M) = f p - ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 at heq
    rw [hz₁, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, x.property] at heq
    have hnorm : ‖z.2‖ = d.radius := by nlinarith [norm_nonneg z.2, d.radius_pos]
    let v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates :=
      ⟨d.radius⁻¹ • z.2, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr d.radius_pos), hnorm, inv_mul_cancel₀ d.radius_pos.ne']⟩
    refine ⟨v, Subtype.ext ?_⟩
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
    change d.chart.splitChart.symm (0, d.radius • (d.radius⁻¹ • z.2)) = (x : M)
    rw [smul_smul, mul_inv_cancel₀ d.radius_pos.ne', one_smul]
    have hz : (0, z.2) = z := Prod.ext hz₁.symm rfl
    rw [hz]
    exact d.chart.splitChart.left_inv' hx
  · rintro ⟨v, rfl⟩
    exact d.beltNormal_belt v

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.contMDiffOn_beltNormal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffOn 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ d.beltNormal
      d.beltNormalDomain := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  have hcoords :
    ContMDiffOn 𝓘(ℝ, Smale.RegularLevel.Model E)
      𝓘(ℝ, d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) ∞
      (d.chart.splitChart ∘ (Subtype.val : d.UpperLevel → M)) d.beltNormalDomain :=
    d.chart.splitChart.contMDiffOn_toFun.comp
      (Smale.RegularLevel.contMDiff_inclusion hf d.upper_regular).contMDiffOn (fun _ hx => hx)
  exact contDiff_fst.contMDiff.comp_contMDiffOn hcoords

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.beltNormal_derivative_comp_belt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    (mfderiv 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
            (d.surgery.beltSphere v)).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v) =
      0 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  have hnormal :=
    (d.contMDiffOn_beltNormal hf).contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  have heq : d.beltNormal ∘ d.surgery.beltSphere = fun _ => 0 := funext d.beltNormal_belt
  have hzero :
    mfderiv (𝓡 n) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ d.surgery.beltSphere) v = 0 :=
    by rw [heq, mfderiv_const]
  have hchain :=
    mfderiv_comp v (hnormal.mdifferentiableAt (by simp))
      ((d.belt_smooth hf n).mdifferentiableAt (by simp))
  exact hchain.symm.trans hzero

private def
    Smale.NativeParametrization.translation {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : D) : Diffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D D ∞
    where
  toEquiv :=
    { toFun := fun x => x + a
      invFun := fun x => x - a
      left_inv := fun _ => add_sub_cancel_right _ _
      right_inv := fun _ => sub_add_cancel _ _ }
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private def
    Smale.NativeParametrization.centered {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] (x : N) :
    PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D N ∞ :=
  let c := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  (translation (c x)).toPartialDiffeomorph.trans c.symm

private theorem
    Smale.NativeParametrization.zero_mem_centered_source {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : (0 : D) ∈ (centered (D := D) x).source := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  refine ⟨Set.mem_univ _, ?_⟩
  change 0 + c x ∈ c.target
  rw [zero_add]
  exact c.map_source' (mem_extChartAt_source x)

private theorem Smale.NativeParametrization.centered_zero {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : centered (D := D) x (0 : D) = x := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  change c.symm (0 + c x) = x
  rw [zero_add]
  exact c.left_inv' (mem_extChartAt_source x)

private theorem Smale.NativeParametrization.mem_centered_target {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
    (x : N) : x ∈ (centered (D := D) x).target := by
  have hx := (centered (D := D) x).map_source' (zero_mem_centered_source (D := D) x)
  rwa [centered_zero] at hx

private theorem Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.mapsTo_superset {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S) {U : Set X} (hKU : K ⊆ U)
    (t : ℝ) : Set.MapsTo (fun x => A.family (t, x)) U U := by
  obtain ⟨d, hd⟩ := A.slices t
  have hfix : ∀ x ∉ U, d x = x := by
    intro x hx
    exact (hd x).trans (A.fixedOutside t x (fun h => hx (hKU h)))
  intro x hx
  change A.family (t, x) ∈ U
  rw [← hd]
  exact Smale.SupportedDiffeomorph.mapsTo_of_fixed_outside d.toEquiv hfix hx

private def Smale.SupportedDiffeomorph.SupportedRelativeIsotopy.extension {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    {e : Diffeomorph I I X X ∞} {K S : Set X}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K S)
    (Φ : PartialDiffeomorph I J X Y ∞) (hK : IsCompact K) (hKsource : K ⊆ Φ.source) {T : Set Y}
    (hfixed : ∀ x ∈ Φ.source, Φ x ∈ T → x ∈ S) :
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy
      (Smale.SupportedDiffeomorph.extension Φ e hK hKsource A.endpoint_fixed_outside) (Φ '' K) T
    where
  family := fun p => Smale.SupportedDiffeomorph.extendMap Φ (fun x => A.family (p.1, x)) p.2
  smooth :=
    Smale.SupportedDiffeomorph.contMDiff_extendFamily Φ A.smooth hK hKsource A.fixedOutside
      (A.mapsTo_superset hKsource)
  zero := by
    intro y
    have heq : (fun x => A.family (0, x)) = id := funext A.zero
    rw [heq]
    exact Smale.SupportedDiffeomorph.extendMap_id Φ y
  one := by
    intro y
    exact congrArg (fun f : X → X => Smale.SupportedDiffeomorph.extendMap Φ f y) (funext A.one)
  slices := by
    intro t
    obtain ⟨d, hd⟩ := A.slices t
    have hfix : ∀ x ∉ K, d x = x := fun x hx => (hd x).trans (A.fixedOutside t x hx)
    exact
      ⟨Smale.SupportedDiffeomorph.extension Φ d hK hKsource hfix, fun y =>
        congrArg (fun f : X → X => Smale.SupportedDiffeomorph.extendMap Φ f y) (funext hd)⟩
  fixedOutside := fun t y hy =>
    Smale.SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (A.fixedOutside t) hy
  fixedOn := by
    intro t y hy
    by_cases hyt : y ∈ Φ.target
    · rw [Smale.SupportedDiffeomorph.extendMap_of_mem Φ _ hyt]
      have hsource : Φ.symm y ∈ Φ.source := Φ.map_target' hyt
      have hi : Φ (Φ.symm y) = y := Φ.right_inv' hyt
      have hs : Φ.symm y ∈ S := hfixed (Φ.symm y) hsource (hi.symm ▸ hy)
      rw [A.fixedOn t (Φ.symm y) hs]
      exact hi
    · exact Smale.SupportedDiffeomorph.extendMap_of_notMem Φ _ hyt

private def Smale.SupportedDiffeomorph.normalBumpFamily {E F H M P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (p : ℝ × (M × P)) : M × P :=
  (bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1), p.2.2)

private theorem Smale.SupportedDiffeomorph.normalBumpFamily_normal {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (t : ℝ) (z : M × P) :
    (normalBumpFamily Φ β b (t, z)).2 = z.2 :=
  rfl

private theorem Smale.SupportedDiffeomorph.normalBumpFamily_zero {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) (z : M × P) :
    normalBumpFamily Φ β b (0, z) = z := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 0 • b z.2), z.1) = z.1
    rw [Real.smoothTransition.zero, zero_smul, neg_zero, bumpFamily_zero]
  · rfl

private theorem Smale.SupportedDiffeomorph.normalBumpFamily_fixed_fiber {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {u : P} (hu : b u = 0)
    (t : ℝ) (x : M) : normalBumpFamily Φ β b (t, (x, u)) = (x, u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition t • b u), x) = x
    rw [hu, smul_zero, neg_zero, bumpFamily_zero]
  · rfl

private theorem Smale.SupportedDiffeomorph.normalBumpFamily_fixed_outside {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup P] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E)
    (t : ℝ) (z : M × P) (hz : z ∉ (Φ '' tsupport β) ×ˢ tsupport b) :
    normalBumpFamily Φ β b (t, z) = z := by
  by_cases hu : z.2 ∈ tsupport b
  · have hx : z.1 ∉ Φ '' tsupport β := fun hx => hz ⟨hx, hu⟩
    exact Prod.ext (bumpFamily_fixed_outside Φ β _ hx) rfl
  · have hb : b z.2 = 0 := by
      by_contra hb
      exact hu (subset_tsupport b hb)
    exact normalBumpFamily_fixed_fiber Φ β b hb t z.1

private theorem Smale.SupportedDiffeomorph.normalBumpFamily_chart {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) (β : E → ℝ) (b : P → E) {x : E} (hx : x ∈ Φ.source)
    (u : P) : normalBumpFamily Φ β b (1, (Φ x, u)) = (Φ (x - β x • b u), u) := by
  apply Prod.ext
  · change bumpFamily Φ β (-(Real.smoothTransition 1 • b u), Φ x) = _
    rw [Real.smoothTransition.one, one_smul, bumpFamily_chart Φ β _ hx, smul_neg, ←
      sub_eq_add_neg]
  · rfl

private theorem Smale.SupportedDiffeomorph.exists_radius_normalBumpFamily {E F H M P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ P] [J.Boundaryless]
    [IsManifold J ∞ M] [T2Space M] {β : E → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ b : P → E,
          ContDiff ℝ ∞ b →
            HasCompactSupport b →
              (∀ u, ‖b u‖ < ε) →
                ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
                    (normalBumpFamily Φ β b) ∧
                  (∀ t,
                      ∃ D : Diffeomorph (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) (M × P) (M × P) ∞,
                        ∀ z, D z = normalBumpFamily Φ β b (t, z)) ∧
                    IsCompact ((Φ '' tsupport β) ×ˢ tsupport b) := by
  obtain ⟨ε, hε, hdiff, hsmooth, -⟩ := exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro b hb hbcompact hbound
  have hsmall (t : ℝ) (u : P) : ‖-(Real.smoothTransition t • b u)‖ < ε := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact
      (mul_le_of_le_one_left (norm_nonneg (b u)) (Real.smoothTransition.le_one t)).trans_lt
        (hbound u)
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hvec :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => Real.smoothTransition p.1 • b p.2.2) :=
    (hθ.comp contMDiff_fst).smul (hb.contMDiff.comp (contMDiff_snd.comp contMDiff_snd))
  have hneg :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, E) ∞
      (fun p : ℝ × (M × P) => -(Real.smoothTransition p.1 • b p.2.2)) :=
    (show ContDiff ℝ ∞ (fun x : E => -x) from contDiff_neg).contMDiff.comp hvec
  have hparam :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (𝓘(ℝ, E).prod J) ∞
      (fun p : ℝ × (M × P) => (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) :=
    hneg.prodMk (contMDiff_fst.comp contMDiff_snd)
  have hfirst :
    ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) J ∞
      (fun p : ℝ × (M × P) => bumpFamily Φ β (-(Real.smoothTransition p.1 • b p.2.2), p.2.1)) := by
    intro p
    exact (hsmooth _ (hsmall p.1 p.2.2)).comp p hparam.contMDiffAt
  refine ⟨hfirst.prodMk (contMDiff_snd.comp contMDiff_snd), ?_, ?_⟩
  · intro t
    have ht :
      ContMDiff (J.prod 𝓘(ℝ, P)) J ∞
        (fun z : M × P => bumpFamily Φ β (-(Real.smoothTransition t • b z.2), z.1)) :=
      hfirst.comp (contMDiff_const.prodMk contMDiff_id)
    have hslices :
      ∀ u : P,
        ∃ D : Diffeomorph J J M M ∞,
          ∀ x, D x = bumpFamily Φ β (-(Real.smoothTransition t • b u), x) :=
      fun u => hdiff _ (hsmall t u)
    exact ⟨Smale.FiberwiseDiffeomorph.diffeomorph ht hslices, fun _ => rfl⟩
  · exact
      (hcompact.isCompact.image_of_continuousOn
            (Φ.contMDiffOn_toFun.continuousOn.mono hsupport)).prod
        hbcompact.isCompact

private theorem
    Smale.exists_small_supported_germ {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] {L : P → E} {U : Set P}
    (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hL : ContDiffOn ℝ ∞ L U) (hLzero : L 0 = 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ b : P → E,
      ContDiff ℝ ∞ b ∧
        HasCompactSupport b ∧ tsupport b ⊆ U ∧ (∀ u, ‖b u‖ < ε) ∧ b =ᶠ[𝓝 (0 : P)] L ∧ b 0 = 0 := by
  let V : Set P := U ∩ L ⁻¹' Metric.ball (0 : E) ε
  have hV : IsOpen V := hL.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hzeroV : (0 : P) ∈ V := ⟨hzero, by simpa [hLzero] using hε⟩
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    exists_compact_smooth_cutoff isCompact_singleton hV (Set.singleton_subset_iff.mpr hzeroV)
  let b : P → E := fun u => β u • L u
  have hfix (u : P) (hu : u ∉ tsupport β) : β u = 0 := by
    by_contra hne
    exact hu (subset_tsupport β hne)
  have hsmooth : ContDiff ℝ ∞ b := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : u ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hu))
    · have hnot : u ∉ tsupport β := fun h => hu (hβsupport h).1
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) u := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hnot] with v hv
      change β v • L v = 0
      rw [hfix v hv, zero_smul]
  have hsupport : tsupport b ⊆ tsupport β := by
    apply closure_mono
    intro u hu hβu
    apply hu
    change β u • L u = 0
    rw [hβu, zero_smul]
  have hcompact : HasCompactSupport b :=
    HasCompactSupport.intro hβcompact.isCompact
      (fun u hu => by change β u • L u = 0; rw [hfix u hu, zero_smul])
  have hsmall (u : P) : ‖b u‖ < ε := by
    by_cases hu : u ∈ tsupport β
    · have hLu : ‖L u‖ < ε := mem_ball_zero_iff.mp (hβsupport hu).2
      change ‖β u • L u‖ < ε
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβrange u).1]
      exact (mul_le_of_le_one_left (norm_nonneg (L u)) (hβrange u).2).trans_lt hLu
    · change ‖β u • L u‖ < ε
      rw [hfix u hu, zero_smul, norm_zero]
      exact hε
  have hgerm : b =ᶠ[𝓝 (0 : P)] L := by
    filter_upwards [hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : P)))] with u hu
    change β u • L u = L u
    rw [hu, one_smul]
  exact
    ⟨b, hsmooth, hcompact, hsupport.trans (hβsupport.trans Set.inter_subset_left), hsmall, hgerm,
      hgerm.eq_of_nhds.trans hLzero⟩

private theorem Smale.SupportedDiffeomorph.exists_supported_shear_isotopy {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U)
    (hzero : (0 : E × F) ∈ U) :
    ∃ (A : ℝ × (E × F) → E × F) (K : Set (E × F)),
      IsCompact K ∧
        K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A ∧
            (∀ p, A (0, p) = p) ∧
              (∀ t,
                  ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞,
                    ∀ p, D p = A (t, p)) ∧
                (∀ t p, p ∉ K → A (t, p) = p) ∧
                  (∀ t p, (A (t, p)).2 = p.2) ∧
                    (∀ t x, A (t, (x, (0 : F))) = (x, 0)) ∧
                      (fun p => A (1, p)) =ᶠ[𝓝 (0 : E × F)] (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, -⟩ :=
    Smale.exists_compact_smooth_cutoff (K := {(0 : E)}) isCompact_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hρ))
  let Φ := (Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph
  obtain ⟨ε, hε, hfamily⟩ :=
    exists_radius_normalBumpFamily (P := F) Φ hβ hβcompact
      (show tsupport β ⊆ Φ.source from Set.subset_univ _)
  obtain ⟨b, hb, hbcompact, hbsupport, hbsmall, hbeq, hbzero⟩ :=
    Smale.exists_small_supported_germ Metric.isOpen_ball (Metric.mem_ball_self hρ)
      (show ContDiffOn ℝ ∞ (fun y : F => -(L y)) (Metric.ball 0 ρ) from L.contDiff.neg.contDiffOn)
      (show -(L (0 : F)) = 0 by simp) hε
  obtain ⟨hAprod, hdiffprod, hK⟩ := hfamily b hb hbcompact hbsmall
  let A := normalBumpFamily Φ β b
  let K : Set (E × F) := (Φ '' tsupport β) ×ˢ tsupport b
  let V := Smale.PartialChart.vectorProduct E F
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ A :=
    V.symm.contMDiff.comp (hAprod.comp (contMDiff_fst.prodMk (V.contMDiff.comp contMDiff_snd)))
  have hdiff (t : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞, ∀ p, D p = A (t, p) := by
    obtain ⟨D, hD⟩ := hdiffprod t
    exact ⟨(V.trans D).trans V.symm, hD⟩
  have hKU : K ⊆ U := by
    rintro ⟨x, y⟩ ⟨⟨w, hw, rfl⟩, hy⟩
    apply hρU
    change (w, y) ∈ Metric.ball (0 : E × F) ρ
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨mem_ball_zero_iff.mp (hβsupport hw), mem_ball_zero_iff.mp (hbsupport hy)⟩
  have hplateau : ∀ᶠ x in 𝓝 (0 : E), β x = 1 :=
    hβone.filter_mono (nhds_le_nhdsSet (Set.mem_singleton (0 : E)))
  have hfirst : ∀ᶠ p in 𝓝 (0 : E × F), β p.1 = 1 := (continuous_fst.tendsto (0 : E × F)) hplateau
  have hsecond : ∀ᶠ p in 𝓝 (0 : E × F), b p.2 = -(L p.2) :=
    (continuous_snd.tendsto (0 : E × F)) hbeq
  refine
    ⟨A, K, hK, hKU, hA, normalBumpFamily_zero Φ β b, hdiff, normalBumpFamily_fixed_outside Φ β b,
      normalBumpFamily_normal Φ β b, fun t x => normalBumpFamily_fixed_fiber Φ β b hbzero t x, ?_⟩
  filter_upwards [hfirst, hsecond] with p hp₁ hp₂
  have hh := normalBumpFamily_chart Φ β b (show p.1 ∈ Φ.source from Set.mem_univ _) p.2
  change A (1, p) = (p.1 - β p.1 • b p.2, p.2) at hh
  rwa [hp₁, one_smul, hp₂, sub_neg_eq_add] at hh

end Mathoverflow1973

end
