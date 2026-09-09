/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisymmetricFields
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Cartesian Navier--Stokes residual in regular axisymmetric coordinates

Every derivative below is an ordinary Fréchet derivative. The coordinate is
`s=(x₀²+x₁²)/2`, so none of the formulas divide by the cylindrical radius.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AxisymmetricResidual

open ProblemStatement AxisymmetricFields
open scoped BigOperators ContDiff

/-- Pack, given by `a • coordinateVector 0 + b • coordinateVector 1 + c • coordinateVector 2`. -/
def pack (a b c : ℝ) : Space :=
  a • coordinateVector 0 + b • coordinateVector 1 + c • coordinateVector 2

@[simp] theorem pack_zero (a b c : ℝ) : pack a b c 0 = a := by
  simp only [Fin.isValue, pack, coordinateVector, PiLp.add_apply, PiLp.smul_apply,
      PiLp.single_eq_same,
    smul_eq_mul, mul_one, ne_eq, zero_ne_one, not_false_eq_true, PiLp.single_eq_of_ne, mul_zero,
        add_zero, Fin.reduceEq]
@[simp] theorem pack_one (a b c : ℝ) : pack a b c 1 = b := by
  simp only [Fin.isValue, pack, coordinateVector, PiLp.add_apply, PiLp.smul_apply, ne_eq,
      one_ne_zero,
    not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero, PiLp.single_eq_same, mul_one,
        zero_add,
    Fin.reduceEq, add_zero]
@[simp] theorem pack_two (a b c : ℝ) : pack a b c 2 = c := by
  simp only [Fin.isValue, pack, coordinateVector, PiLp.add_apply, PiLp.smul_apply, ne_eq,
      Fin.reduceEq,
    not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero, add_zero, PiLp.single_eq_same,
        mul_one, zero_add]

/-- Pack derivative, given by `a.smulRight (coordinateVector 0) + b.smulRight (coordinateVector
1) + c.smulRight (coordinateVector 2)`. -/
def packDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : E →L[ℝ] ℝ) : E →L[ℝ] Space :=
  a.smulRight (coordinateVector 0) + b.smulRight (coordinateVector 1) +
    c.smulRight (coordinateVector 2)

@[simp] theorem packDerivative_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : E →L[ℝ] ℝ) (v : E) : packDerivative a b c v = pack (a v) (b v) (c v) := rfl

theorem hasFDerivAt_pack {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : E → ℝ} {da db dc : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a da x) (hb : HasFDerivAt b db x) (hc : HasFDerivAt c dc x) :
    HasFDerivAt (fun y => pack (a y) (b y) (c y)) (packDerivative da db dc) x :=
  ((ha.smul_const _).add (hb.smul_const _)).add (hc.smul_const _)

theorem fderiv_pack_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : E → ℝ} {x : E} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) (hc : DifferentiableAt ℝ c x) (v : E) :
    fderiv ℝ (fun y => pack (a y) (b y) (c y)) x v =
      pack (fderiv ℝ a x v) (fderiv ℝ b x v) (fderiv ℝ c x v) := by
  rw [(hasFDerivAt_pack ha.hasFDerivAt hb.hasFDerivAt hc.hasFDerivAt).fderiv]
  rfl

/-- Direction, given by `fderiv ℝ g x (coordinateVector i)`. -/
def direction (g : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ g x (coordinateVector i)

/-- Scalar laplacian, given by `∑ i : Fin 3, direction (fun y => direction g i y) i x`. -/
def scalarLaplacian (g : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, direction (fun y => direction g i y) i x

/-- Vector laplacian, given by `∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ g y (coordinateVector
i)) x (coordinateVector i)`. -/
def vectorLaplacian (g : Space → Space) (x : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ g y (coordinateVector i)) x (coordinateVector i)

theorem contDiff_direction {g : Space → ℝ} {m n : WithTop ℕ∞}
    (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiff ℝ m (fun x => direction g i x) :=
  (hg.fderiv_right hmn).clm_apply contDiff_const

theorem direction_add {a b : Space → ℝ} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) (i : Fin 3) (x : Space) :
    direction (fun y => a y + b y) i x = direction a i x + direction b i x := by
  unfold direction
  rw [fderiv_fun_add (ha x) (hb x)]
  rfl

theorem direction_sub {a b : Space → ℝ} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) (i : Fin 3) (x : Space) :
    direction (fun y => a y - b y) i x = direction a i x - direction b i x := by
  unfold direction
  rw [fderiv_fun_sub (ha x) (hb x)]
  rfl

theorem direction_neg (a : Space → ℝ) (i : Fin 3) (x : Space) :
    direction (fun y => -a y) i x = -direction a i x := by
  simp only [direction, fderiv_fun_neg, neg_apply]

theorem scalarLaplacian_add {a b : Space → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (x : Space) :
    scalarLaplacian (fun y => a y + b y) x = scalarLaplacian a x + scalarLaplacian b x := by
  unfold scalarLaplacian
  simp_rw [direction_add (ha.differentiable (by norm_num)) (hb.differentiable (by norm_num))]
  simp_rw [direction_add
    ((contDiff_direction ha (m := 1) (by norm_num) _).differentiable (by norm_num))
    ((contDiff_direction hb (m := 1) (by norm_num) _).differentiable (by norm_num))]
  exact Finset.sum_add_distrib

theorem scalarLaplacian_sub {a b : Space → ℝ} (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b) (x : Space) :
    scalarLaplacian (fun y => a y - b y) x = scalarLaplacian a x - scalarLaplacian b x := by
  unfold scalarLaplacian
  simp_rw [direction_sub (ha.differentiable (by norm_num)) (hb.differentiable (by norm_num))]
  simp_rw [direction_sub
    ((contDiff_direction ha (m := 1) (by norm_num) _).differentiable (by norm_num))
    ((contDiff_direction hb (m := 1) (by norm_num) _).differentiable (by norm_num))]
  simp only [Finset.sum_sub_distrib]

theorem scalarLaplacian_neg (a : Space → ℝ) (x : Space) :
    scalarLaplacian (fun y => -a y) x = -scalarLaplacian a x := by
  simp only [scalarLaplacian, direction_neg, Finset.sum_neg_distrib]

theorem direction_coord_mul {g : Space → ℝ} (hg : Differentiable ℝ g)
    (i j : Fin 3) (x : Space) :
    direction (fun y => y i * g y) j x =
      (coordinateVector j) i * g x + x i * direction g j x := by
  unfold direction
  change (fderiv ℝ (fun y => projection i y * g y) x) (coordinateVector j) = _
  rw [fderiv_fun_mul (projection i).differentiableAt (hg x)]
  simp only [projection_apply, ContinuousLinearMap.fderiv, add_apply, smul_apply, smul_eq_mul]
  ring

theorem second_direction_coord_mul {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (i j : Fin 3) (x : Space) :
    direction (fun y => direction (fun z => z i * g z) j y) j x =
      2 * (coordinateVector j) i * direction g j x +
        x i * direction (fun y => direction g j y) j x := by
  have hd := hg.differentiable (by norm_num)
  have hdg := (contDiff_direction hg (m := 1) (by norm_num) j).differentiable (by norm_num)
  simp_rw [direction_coord_mul hd i j]
  change (fderiv ℝ (fun y => (coordinateVector j) i * g y +
    projection i y * direction g j y) x) (coordinateVector j) = _
  rw [fderiv_fun_add ((hd x).const_mul ((coordinateVector j) i))
    ((projection i).differentiableAt.fun_mul (hdg x))]
  rw [fderiv_const_mul (hd x), fderiv_fun_mul (projection i).differentiableAt (hdg x)]
  simp only [projection_apply, direction, ContinuousLinearMap.fderiv, add_apply, smul_apply,
      smul_eq_mul]
  ring

theorem scalarLaplacian_coord_mul {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (i : Fin 3) (x : Space) :
    scalarLaplacian (fun y => y i * g y) x =
      x i * scalarLaplacian g x + 2 * direction g i x := by
  unfold scalarLaplacian
  simp_rw [second_direction_coord_mul hg]
  fin_cases i <;> simp only [coordinateVector, Fin.zero_eta, Fin.isValue, PiLp.single_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fin.sum_univ_three, ↓reduceIte, zero_ne_one,
          zero_add, Fin.reduceEq, Fin.mk_one, one_ne_zero, Fin.reduceFinMk] <;> ring

theorem vectorLaplacian_pack {a b c : Space → ℝ}
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hc : ContDiff ℝ 2 c) (x : Space) :
    vectorLaplacian (fun y => pack (a y) (b y) (c y)) x =
      pack (scalarLaplacian a x) (scalarLaplacian b x) (scalarLaplacian c x) := by
  unfold vectorLaplacian
  simp_rw [fderiv_pack_apply (ha.differentiable (by norm_num) _)
    (hb.differentiable (by norm_num) _) (hc.differentiable (by norm_num) _)]
  change (∑ i : Fin 3, fderiv ℝ (fun y => pack (direction a i y) (direction b i y)
    (direction c i y)) x (coordinateVector i)) = _
  simp_rw [fderiv_pack_apply
    ((contDiff_direction ha (m := 1) (by norm_num) _).differentiable (by norm_num) x)
    ((contDiff_direction hb (m := 1) (by norm_num) _).differentiable (by norm_num) x)
    ((contDiff_direction hc (m := 1) (by norm_num) _).differentiable (by norm_num) x)]
  simp only [pack, direction, Finset.sum_add_distrib, ← Finset.sum_smul, scalarLaplacian]

/-- Lift, given by `G (profilePoint t x)`. -/
def lift (G : Profile) (t : ℝ) (x : Space) : ℝ := G (profilePoint t x)

/-- Joint differentiability is needed only along the spatial slice being evaluated. -/
def SliceDifferentiable (G : Profile) (t : ℝ) : Prop :=
  ∀ x : Space, DifferentiableAt ℝ G (profilePoint t x)

/-- No smooth extension across the singular time is required by this hypothesis. -/
def SliceC2 (G : Profile) (t : ℝ) : Prop :=
  ∀ x : Space, ContDiffAt ℝ 2 G (profilePoint t x)

theorem SliceC2.differentiable {G : Profile} {t : ℝ} (hG : SliceC2 G t) :
    SliceDifferentiable G t := fun x => (hG x).differentiableAt (by norm_num)

theorem sliceC2_of_contDiffOn {G : Profile} {times : Set ℝ} {t : ℝ}
    (hG : ContDiffOn ℝ 2 G (times ×ˢ (Set.univ : Set (ℝ × ℝ))))
    (ht : times ∈ nhds t) : SliceC2 G t := by
  intro x
  exact hG.contDiffAt (prod_mem_nhds ht Filter.univ_mem)

theorem contDiff_lift_slice {G : Profile} {t : ℝ} (hG : SliceC2 G t) :
    ContDiff ℝ 2 (lift G t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (hG x).comp x (contDiff_profilePoint_slice t).contDiffAt

/-- Partial T, given by `fderiv ℝ G p (1, (0, 0))`. -/
def partialT (G : Profile) (p : ProfilePoint) : ℝ := fderiv ℝ G p (1, (0, 0))
/-- Laplace scalar, given by `2 * p.2.1 * partialS (partialS G) p + 2 * partialS G p + partialZ
(partialZ G) p`. -/
def laplaceScalar (G : Profile) (p : ProfilePoint) : ℝ :=
  2 * p.2.1 * partialS (partialS G) p + 2 * partialS G p + partialZ (partialZ G) p
/-- Laplace weighted, given by `2 * p.2.1 * partialS (partialS G) p + 4 * partialS G p +
partialZ (partialZ G) p`. -/
def laplaceWeighted (G : Profile) (p : ProfilePoint) : ℝ :=
  2 * p.2.1 * partialS (partialS G) p + 4 * partialS G p + partialZ (partialZ G) p

theorem contDiff_lift {G : Profile} {n : WithTop ℕ∞} (hG : ContDiff ℝ n G) (t : ℝ) :
    ContDiff ℝ n (lift G t) := hG.comp (contDiff_profilePoint_slice t)

theorem contDiff_partialS {G : Profile} {m n : WithTop ℕ∞}
    (hG : ContDiff ℝ n G) (hmn : m + 1 ≤ n) : ContDiff ℝ m (partialS G) :=
  (hG.fderiv_right hmn).clm_apply contDiff_const

theorem contDiff_partialZ {G : Profile} {m n : WithTop ℕ∞}
    (hG : ContDiff ℝ n G) (hmn : m + 1 ≤ n) : ContDiff ℝ m (partialZ G) :=
  (hG.fderiv_right hmn).clm_apply contDiff_const

theorem fderiv_lift_apply {G : Profile} {t : ℝ} (hG : SliceDifferentiable G t)
    (x v : Space) : fderiv ℝ (lift G t) x v =
      (x 0 * v 0 + x 1 * v 1) * partialS G (profilePoint t x) +
        v 2 * partialZ G (profilePoint t x) := by
  change (fderiv ℝ (fun y => G (profilePoint t y)) x) v = _
  rw [(hasFDerivAt_profile_composition G t x (hG _)).fderiv]
  exact profileDerivative_apply G t x v

theorem direction_lift_zero {G : Profile} {t : ℝ} (hG : SliceDifferentiable G t) (x : Space) :
    direction (lift G t) 0 x = x 0 * lift (partialS G) t x := by
  unfold direction
  rw [fderiv_lift_apply hG]
  simp only [Fin.isValue, coordinateVector, PiLp.single_eq_same, mul_one, ne_eq, one_ne_zero,
      not_false_eq_true,
    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, zero_mul, lift]

theorem direction_lift_one {G : Profile} {t : ℝ} (hG : SliceDifferentiable G t) (x : Space) :
    direction (lift G t) 1 x = x 1 * lift (partialS G) t x := by
  unfold direction
  rw [fderiv_lift_apply hG]
  simp only [Fin.isValue, coordinateVector, ne_eq, zero_ne_one, not_false_eq_true,
      PiLp.single_eq_of_ne,
    mul_zero, PiLp.single_eq_same, mul_one, zero_add, Fin.reduceEq, zero_mul, add_zero, lift]

theorem direction_lift_two {G : Profile} {t : ℝ} (hG : SliceDifferentiable G t) (x : Space) :
    direction (lift G t) 2 x = lift (partialZ G) t x := by
  unfold direction
  rw [fderiv_lift_apply hG]
  simp only [Fin.isValue, coordinateVector, ne_eq, Fin.reduceEq, not_false_eq_true,
      PiLp.single_eq_of_ne,
    mul_zero, add_zero, zero_mul, PiLp.single_eq_same, one_mul, zero_add, lift]

theorem scalarLaplacian_lift {G : Profile} {t : ℝ} (hG : SliceC2 G t) (x : Space) :
    scalarLaplacian (lift G t) x = laplaceScalar G (profilePoint t x) := by
  have hd := hG.differentiable
  have hs : SliceDifferentiable (partialS G) t := fun x =>
    (((hG x).fderiv_right (m := 1) (by
        norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hz : SliceDifferentiable (partialZ G) t := fun x =>
    (((hG x).fderiv_right (m := 1) (by
        norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hls : Differentiable ℝ (lift (partialS G) t) :=
    fun x => (hs x).comp x ((contDiff_profilePoint_slice t (n := 1)).differentiable (by norm_num) x)
  unfold scalarLaplacian
  rw [Fin.sum_univ_three]
  simp_rw [direction_lift_zero hd, direction_lift_one hd, direction_lift_two hd]
  rw [direction_coord_mul hls, direction_coord_mul hls]
  rw [direction_lift_zero hs, direction_lift_one hs, direction_lift_two hz]
  simp only [Fin.isValue, coordinateVector, PiLp.single_eq_same, lift, profilePoint, radialEnergy,
      one_mul,
    laplaceScalar, add_left_inj]
  ring

theorem scalarLaplacian_weighted_zero {G : Profile} {t : ℝ} (hG : SliceC2 G t) (x : Space) :
    scalarLaplacian (fun y => y 0 * lift G t y) x =
      x 0 * laplaceWeighted G (profilePoint t x) := by
  rw [scalarLaplacian_coord_mul (contDiff_lift_slice hG), scalarLaplacian_lift hG,
    direction_lift_zero hG.differentiable]
  unfold lift laplaceScalar laplaceWeighted
  ring

theorem scalarLaplacian_weighted_one {G : Profile} {t : ℝ} (hG : SliceC2 G t) (x : Space) :
    scalarLaplacian (fun y => y 1 * lift G t y) x =
      x 1 * laplaceWeighted G (profilePoint t x) := by
  rw [scalarLaplacian_coord_mul (contDiff_lift_slice hG), scalarLaplacian_lift hG,
    direction_lift_one hG.differentiable]
  unfold lift laplaceScalar laplaceWeighted
  ring

/-- Component X, given by `-(x 0 * lift B t x + x 1 * lift F t x)`. -/
def componentX (B F : Profile) (t : ℝ) (x : Space) : ℝ :=
  -(x 0 * lift B t x + x 1 * lift F t x)
/-- Component Y, given by `x 0 * lift F t x - x 1 * lift B t x`. -/
def componentY (B F : Profile) (t : ℝ) (x : Space) : ℝ :=
  x 0 * lift F t x - x 1 * lift B t x

/-- Convention: radial velocity `-r B`, angular velocity `r F`, axial velocity `U`. -/
def velocity (B F U : Profile) : VelocityField :=
  fun w => pack (componentX B F w.1 w.2) (componentY B F w.1 w.2) (lift U w.1 w.2)
/-- Pressure, defined pointwise by `lift P w.1 w.2`. -/
def pressure (P : Profile) : PressureField := fun w => lift P w.1 w.2

/-- Velocity jacobian, constructed using `packDerivative`. -/
def velocityJacobian (B F U : Profile) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  packDerivative
    (-(x 0 • profileDerivative B t x + lift B t x • projection 0 +
      (x 1 • profileDerivative F t x + lift F t x • projection 1)))
    ((x 0 • profileDerivative F t x + lift F t x • projection 0) -
      (x 1 • profileDerivative B t x + lift B t x • projection 1))
    (profileDerivative U t x)

theorem hasFDerivAt_velocity {B F U : Profile} {t : ℝ}
    (hB : SliceDifferentiable B t) (hF : SliceDifferentiable F t)
    (hU : SliceDifferentiable U t) (x : Space) :
    HasFDerivAt (fun y => velocity B F U (t, y)) (velocityJacobian B F U t x) x := by
  have hb := hasFDerivAt_profile_composition B t x (hB x)
  have hf := hasFDerivAt_profile_composition F t x (hF x)
  have hu := hasFDerivAt_profile_composition U t x (hU x)
  exact hasFDerivAt_pack
    ((((projection 0).hasFDerivAt.mul hb).add ((projection 1).hasFDerivAt.mul hf)).neg)
    (((projection 0).hasFDerivAt.mul hf).sub ((projection 1).hasFDerivAt.mul hb)) hu

/-- Advection radial, given by `(B p) ^ 2 - (F p) ^ 2 + 2 * p.2.1 * B p * partialS B p - U p *
partialZ B p`. -/
def advectionRadial (B F U : Profile) (p : ProfilePoint) : ℝ :=
  (B p) ^ 2 - (F p) ^ 2 + 2 * p.2.1 * B p * partialS B p - U p * partialZ B p
/-- Advection angular, given by `2 * B p * F p + 2 * p.2.1 * B p * partialS F p - U p * partialZ
F p`. -/
def advectionAngular (B F U : Profile) (p : ProfilePoint) : ℝ :=
  2 * B p * F p + 2 * p.2.1 * B p * partialS F p - U p * partialZ F p
/-- Advection axial, given by `-2 * p.2.1 * B p * partialS U p + U p * partialZ U p`. -/
def advectionAxial (B U : Profile) (p : ProfilePoint) : ℝ :=
  -2 * p.2.1 * B p * partialS U p + U p * partialZ U p

theorem advection_velocity {B F U : Profile} {t : ℝ}
    (hB : SliceDifferentiable B t) (hF : SliceDifferentiable F t)
    (hU : SliceDifferentiable U t) (x : Space) :
    advection (velocity B F U) t x =
      pack (x 0 * advectionRadial B F U (profilePoint t x) +
        x 1 * advectionAngular B F U (profilePoint t x))
      (x 1 * advectionRadial B F U (profilePoint t x) -
        x 0 * advectionAngular B F U (profilePoint t x))
      (advectionAxial B U (profilePoint t x)) := by
  change (fderiv ℝ (fun y => velocity B F U (t, y)) x) (velocity B F U (t, x)) = _
  rw [(hasFDerivAt_velocity hB hF hU x).fderiv]
  simp only [velocityJacobian, packDerivative_apply]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, lift, profilePoint, radialEnergy, neg_add_rev,
      velocity, componentX,
                    coordinateVector, componentY, add_apply, neg_apply, smul_apply,
                        projection_apply, PiLp.add_apply, PiLp.smul_apply,
                    ne_eq, one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul,
                        mul_zero, PiLp.single_eq_same, mul_one,
                    zero_add, Fin.reduceEq, add_zero, profileDerivative_apply, zero_ne_one,
                        sub_apply, Fin.zero_eta, advectionRadial,
                    advectionAngular, advectionAxial, neg_mul] <;> ring

theorem divergence_velocity {B F U : Profile} {t : ℝ}
    (hB : SliceDifferentiable B t) (hF : SliceDifferentiable F t)
    (hU : SliceDifferentiable U t) (x : Space) :
    spatialDivergence (velocity B F U) t x =
      partialZ U (profilePoint t x) - 2 * B (profilePoint t x) -
        2 * radialEnergy x * partialS B (profilePoint t x) := by
  unfold spatialDivergence spatialDerivative
  rw [(hasFDerivAt_velocity hB hF hU x).fderiv, Fin.sum_univ_three]
  simp only [velocityJacobian, Fin.isValue, lift, profilePoint, radialEnergy, neg_add_rev,
      coordinateVector,
    packDerivative_apply, add_apply, neg_apply, smul_apply, projection_apply, ne_eq, one_ne_zero,
        not_false_eq_true,
    PiLp.single_eq_of_ne, smul_eq_mul, mul_zero, neg_zero, profileDerivative_apply,
        PiLp.single_eq_same, mul_one,
    add_zero, Fin.reduceEq, zero_mul, zero_add, sub_apply, pack_zero, zero_ne_one, pack_one,
        one_mul, pack_two]
  ring

theorem spatialLaplacian_velocity {B F U : Profile} {t : ℝ}
    (hB : SliceC2 B t) (hF : SliceC2 F t) (hU : SliceC2 U t) (x : Space) :
    spatialLaplacian (velocity B F U) t x =
      pack (-x 0 * laplaceWeighted B (profilePoint t x) -
        x 1 * laplaceWeighted F (profilePoint t x))
      (-x 1 * laplaceWeighted B (profilePoint t x) +
        x 0 * laplaceWeighted F (profilePoint t x))
      (laplaceScalar U (profilePoint t x)) := by
  have hb := contDiff_lift_slice hB
  have hf := contDiff_lift_slice hF
  have hu := contDiff_lift_slice hU
  have h0b : ContDiff ℝ 2 (fun y : Space => y 0 * lift B t y) := (projection 0).contDiff.mul hb
  have h1b : ContDiff ℝ 2 (fun y : Space => y 1 * lift B t y) := (projection 1).contDiff.mul hb
  have h0f : ContDiff ℝ 2 (fun y : Space => y 0 * lift F t y) := (projection 0).contDiff.mul hf
  have h1f : ContDiff ℝ 2 (fun y : Space => y 1 * lift F t y) := (projection 1).contDiff.mul hf
  have hx : ContDiff ℝ 2 (componentX B F t) := (h0b.add h1f).neg
  have hy : ContDiff ℝ 2 (componentY B F t) := h0f.sub h1b
  change vectorLaplacian (fun y => pack (componentX B F t y) (componentY B F t y)
    (lift U t y)) x = _
  rw [vectorLaplacian_pack hx hy hu]
  unfold componentX componentY
  rw [scalarLaplacian_neg, scalarLaplacian_add h0b h1f, scalarLaplacian_sub h0f h1b]
  rw [scalarLaplacian_weighted_zero hB, scalarLaplacian_weighted_one hF,
    scalarLaplacian_weighted_zero hF, scalarLaplacian_weighted_one hB, scalarLaplacian_lift hU]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, neg_add_rev, coordinateVector, Fin.zero_eta,
      PiLp.add_apply, PiLp.smul_apply,
                    PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one,
                        not_false_eq_true, PiLp.single_eq_of_ne, mul_zero,
                    add_zero, Fin.reduceEq, neg_mul] <;> ring

theorem pressureGradient_pressure {P : Profile} {t : ℝ}
    (hP : SliceDifferentiable P t) (x : Space) :
    pressureGradient (pressure P) t x =
      pack (x 0 * partialS P (profilePoint t x)) (x 1 * partialS P (profilePoint t x))
        (partialZ P (profilePoint t x)) := by
  change (∑ i : Fin 3, fderiv ℝ (lift P t) x (coordinateVector i) • coordinateVector i) = _
  simp_rw [fderiv_lift_apply hP]
  rw [Fin.sum_univ_three]
  simp only [Fin.isValue, coordinateVector, PiLp.single_eq_same, mul_one, ne_eq, one_ne_zero,
      not_false_eq_true,
    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, zero_mul, zero_ne_one, zero_add,
        one_mul, pack]

/-- Time profile jacobian, given by `(ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ × ℝ)`. -/
def timeProfileJacobian : ℝ →L[ℝ] ProfilePoint :=
  (ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ × ℝ)
/-- Time profile derivative, given by `(fderiv ℝ G p).comp timeProfileJacobian`. -/
def timeProfileDerivative (G : Profile) (p : ProfilePoint) : ℝ →L[ℝ] ℝ :=
  (fderiv ℝ G p).comp timeProfileJacobian

@[simp] theorem timeProfileDerivative_one (G : Profile) (p : ProfilePoint) :
    timeProfileDerivative G p 1 = partialT G p := rfl

theorem hasFDerivAt_time_lift {G : Profile} {t : ℝ} (hG : SliceDifferentiable G t) (x : Space) :
    HasFDerivAt (fun s => lift G s x) (timeProfileDerivative G (profilePoint t x)) t := by
  have hp : HasFDerivAt (fun s => profilePoint s x) timeProfileJacobian t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const (radialEnergy x, x 2) t)
  exact (hG x).hasFDerivAt.comp t hp

theorem temporalDerivative_velocity {B F U : Profile} {t : ℝ}
    (hB : SliceDifferentiable B t) (hF : SliceDifferentiable F t)
    (hU : SliceDifferentiable U t) (x : Space) :
    temporalDerivative (velocity B F U) t x =
      pack (-x 0 * partialT B (profilePoint t x) - x 1 * partialT F (profilePoint t x))
        (-x 1 * partialT B (profilePoint t x) + x 0 * partialT F (profilePoint t x))
        (partialT U (profilePoint t x)) := by
  have hb := hasFDerivAt_time_lift hB x
  have hf := hasFDerivAt_time_lift hF x
  have hu := hasFDerivAt_time_lift hU x
  have hv := hasFDerivAt_pack (((hb.const_mul (x 0)).fun_add (hf.const_mul (x 1))).fun_neg)
    ((hf.const_mul (x 0)).fun_sub (hb.const_mul (x 1))) hu
  change (fderiv ℝ (fun s => pack (-(x 0 * lift B s x + x 1 * lift F s x))
    (x 0 * lift F s x - x 1 * lift B s x) (lift U s x)) t) 1 = _
  rw [hv.fderiv]
  simp only [Fin.isValue, neg_add_rev, packDerivative_apply, add_apply, neg_apply, smul_apply,
    timeProfileDerivative_one, smul_eq_mul, sub_apply, neg_mul]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, coordinateVector, Fin.zero_eta, PiLp.add_apply,
      PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one,
          not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, Fin.mk_one,
              one_ne_zero, zero_add, Fin.reduceFinMk] <;> ring

/-- Residual radial, given by `-partialT B p + advectionRadial B F U p + laplaceWeighted B p +
partialS P p`. -/
def residualRadial (B F U P : Profile) (p : ProfilePoint) : ℝ :=
  -partialT B p + advectionRadial B F U p + laplaceWeighted B p + partialS P p
/-- Residual angular, given by `-partialT F p + advectionAngular B F U p + laplaceWeighted F p`. -/
def residualAngular (B F U : Profile) (p : ProfilePoint) : ℝ :=
  -partialT F p + advectionAngular B F U p + laplaceWeighted F p
/-- Residual axial, given by `partialT U p + advectionAxial B U p - laplaceScalar U p + partialZ
P p`. -/
def residualAxial (B U P : Profile) (p : ProfilePoint) : ℝ :=
  partialT U p + advectionAxial B U p - laplaceScalar U p + partialZ P p

/-- Exact physical Navier--Stokes residual, at viscosity one, including radial,
angular, and axial viscosity. Its hypotheses need no continuation past time `t`. -/
theorem navierStokesResidual_velocity {B F U P : Profile} {t : ℝ}
    (hB : SliceC2 B t) (hF : SliceC2 F t) (hU : SliceC2 U t)
    (hP : SliceDifferentiable P t) (x : Space) :
    navierStokesResidual (velocity B F U) (pressure P) t x =
      pack (x 0 * residualRadial B F U P (profilePoint t x) +
        x 1 * residualAngular B F U (profilePoint t x))
      (x 1 * residualRadial B F U P (profilePoint t x) -
        x 0 * residualAngular B F U (profilePoint t x))
      (residualAxial B U P (profilePoint t x)) := by
  unfold navierStokesResidual
  rw [temporalDerivative_velocity hB.differentiable hF.differentiable hU.differentiable,
    advection_velocity hB.differentiable hF.differentiable hU.differentiable,
    spatialLaplacian_velocity hB hF hU, pressureGradient_pressure hP]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, neg_mul, coordinateVector, Fin.zero_eta,
      PiLp.add_apply, PiLp.sub_apply,
                    PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one,
                        not_false_eq_true,
                    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, residualRadial,
                        residualAngular, residualAxial] <;> ring

theorem navierStokesResidual_on_axis {B F U P : Profile} {t : ℝ}
    (hB : SliceC2 B t) (hF : SliceC2 F t) (hU : SliceC2 U t)
    (hP : SliceDifferentiable P t) (x : Space) (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    navierStokesResidual (velocity B F U) (pressure P) t x =
      residualAxial B U P (t, (0, x 2)) • coordinateVector 2 := by
  rw [navierStokesResidual_velocity hB hF hU hP]
  simp only [pack, Fin.isValue, hx0, profilePoint, radialEnergy, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true,
    zero_pow, hx1, add_zero, zero_div, zero_mul, zero_smul, sub_self, zero_add]

/-- The three explicit coefficient equations imply the actual Cartesian PDE. -/
theorem navierStokesResidual_eq_zero {B F U P : Profile} {t : ℝ}
    (hB : SliceC2 B t) (hF : SliceC2 F t) (hU : SliceC2 U t)
    (hP : SliceDifferentiable P t) (x : Space)
    (hr : residualRadial B F U P (profilePoint t x) = 0)
    (ha : residualAngular B F U (profilePoint t x) = 0)
    (hz : residualAxial B U P (profilePoint t x) = 0) :
    navierStokesResidual (velocity B F U) (pressure P) t x = 0 := by
  rw [navierStokesResidual_velocity hB hF hU hP]
  simp only [pack, Fin.isValue, hr, mul_zero, ha, add_zero, zero_smul, sub_self, hz]

/-- From potential B, given by `partialZ H p / 2`. -/
def fromPotentialB (H : Profile) (p : ProfilePoint) : ℝ := partialZ H p / 2
/-- From potential F, given by `-partialS K p`. -/
def fromPotentialF (K : Profile) (p : ProfilePoint) : ℝ := -partialS K p
/-- From potential U, given by `H p + p.2.1 * partialS H p`. -/
def fromPotentialU (H : Profile) (p : ProfilePoint) : ℝ := H p + p.2.1 * partialS H p

/-- Connect the residual convention to the already constructed curl field. -/
theorem velocity_from_potential_at (H K : Profile) (t : ℝ) (x : Space)
    (hH : DifferentiableAt ℝ H (profilePoint t x))
    (hK : DifferentiableAt ℝ K (profilePoint t x)) :
    AxisymmetricFields.velocity H K (t, x) =
      velocity (fromPotentialB H) (fromPotentialF K) (fromPotentialU H) (t, x) := by
  ext i
  fin_cases i
  · change AxisymmetricFields.velocity H K (t, x) 0 = _
    rw [AxisymmetricFields.velocity_zero H K t x hH hK]
    simp only [Fin.isValue, neg_mul, velocity, componentX, lift, fromPotentialB, fromPotentialF,
        mul_neg,
      neg_add_rev, neg_neg, Fin.zero_eta, pack_zero]
    ring
  · change AxisymmetricFields.velocity H K (t, x) 1 = _
    rw [AxisymmetricFields.velocity_one H K t x hH hK]
    simp only [Fin.isValue, neg_mul, velocity, componentY, lift, fromPotentialF, mul_neg,
        fromPotentialB,
      Fin.mk_one, pack_one]
    ring
  · change AxisymmetricFields.velocity H K (t, x) 2 = _
    rw [AxisymmetricFields.velocity_two H K t x hH hK]
    simp only [Fin.isValue, profilePoint, velocity, lift, fromPotentialU, Fin.reduceFinMk, pack_two]

theorem velocity_from_potential {H K : Profile}
    (hH : Differentiable ℝ H) (hK : Differentiable ℝ K) :
    AxisymmetricFields.velocity H K =
      velocity (fromPotentialB H) (fromPotentialF K) (fromPotentialU H) := by
  funext w
  exact velocity_from_potential_at H K w.1 w.2 (hH _) (hK _)

theorem divergence_velocity_eq_zero {B F U : Profile} {t : ℝ}
    (hB : SliceDifferentiable B t) (hF : SliceDifferentiable F t)
    (hU : SliceDifferentiable U t) (x : Space)
    (h : partialZ U (profilePoint t x) =
      2 * B (profilePoint t x) + 2 * radialEnergy x * partialS B (profilePoint t x)) :
    spatialDivergence (velocity B F U) t x = 0 := by
  rw [divergence_velocity hB hF hU, h]
  ring

end NavierStokes.AxisymmetricResidual
