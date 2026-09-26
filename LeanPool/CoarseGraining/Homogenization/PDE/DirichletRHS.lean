/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientFieldHilbert
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareZeroTrace
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-! # Dirichlet RHS -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators

/-!
# Zero-trace Dirichlet problems with right-hand side

This file records the weak solution surface used by the deterministic
coarse-grained Poincare-with-RHS argument. At this stage it packages the
first-variation identity and the immediate consequences needed in Step 1 of the
notes: invariance under subtracting constants from the forcing, zero average
gradient of the zero-trace corrector, and the basic elliptic energy bound.
-/

/-- Weak zero-trace formulation of `- div (a grad u) = div g` on `U`. -/
def IsZeroTraceDirichletRhsWeakSolution {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H10Function U) (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U,
    ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
      ∂MeasureTheory.volume =
    ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume

theorem integral_vecDot_const_zeroTraceGrad_eq_zero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H10Function U) (c : Vec d) :
    ∫ x in U, vecDot c (u.toH1Function.grad x) ∂MeasureTheory.volume = 0 := by
  have hzero :
      (fun i => ∫ x in U, u.toH1Function.grad x i ∂MeasureTheory.volume) = 0 :=
    IsPotentialZeroTraceOn.integral_eq_zero u.isPotentialZeroTraceOn
  calc
    ∫ x in U, vecDot c (u.toH1Function.grad x) ∂MeasureTheory.volume
        = ∫ x in U, ∑ i, c i * u.toH1Function.grad x i ∂MeasureTheory.volume := by
            simp [vecDot]
    _ = ∑ i, ∫ x in U, c i * u.toH1Function.grad x i ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro i hi
          have hbase :
              MeasureTheory.Integrable
                (fun x => u.toH1Function.grad x i) (MeasureTheory.volume.restrict U) :=
            (u.toH1Function.grad_memL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
          simpa using hbase.const_mul (c i)
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hzeroi : ∫ x in U, u.toH1Function.grad x i ∂MeasureTheory.volume = 0 := by
            simpa using congrFun hzero i
          rw [MeasureTheory.integral_const_mul, hzeroi]
          simp

theorem integral_vecDot_sub_const_zeroTraceGrad_eq
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (u : H10Function U) (c : Vec d) :
    ∫ x in U, vecDot (g x - c) (u.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hg_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (g x) (u.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hg u.toH1Function.grad_memVectorL2
  have hc_mem : MemVectorL2 U (fun _ : Vec d => c) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) c
  have hc_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot c (u.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hc_mem u.toH1Function.grad_memVectorL2
  have hfun :
      (fun x => vecDot (g x - c) (u.toH1Function.grad x)) =
        fun x => vecDot (g x) (u.toH1Function.grad x) - vecDot c (u.toH1Function.grad x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  rw [hfun, MeasureTheory.integral_sub hg_int hc_int,
    integral_vecDot_const_zeroTraceGrad_eq_zero]
  simp

theorem integral_vecDot_add_const_zeroTraceGrad_eq
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (u : H10Function U) (c : Vec d) :
    ∫ x in U, vecDot (g x + c) (u.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  simpa [sub_eq_add_neg] using
    integral_vecDot_sub_const_zeroTraceGrad_eq (U := U) hg u (-c)

theorem integrableOn_vecNormSq_h1Grad
    {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    MeasureTheory.IntegrableOn (fun x => vecNormSq (u.grad x)) U := by
  simpa [vecNormSq] using
    (integrableOn_vecDot_of_memVectorL2
      u.grad_memVectorL2 u.grad_memVectorL2)

theorem integrableOn_vecNormSq_zeroTraceGrad
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) :
    MeasureTheory.IntegrableOn (fun x => vecNormSq (u.toH1Function.grad x)) U := by
  simpa using integrableOn_vecNormSq_h1Grad u.toH1Function

theorem integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (u : H10Function U) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))) U := by
  have hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2
  exact integrableOn_vecDot_of_memVectorL2 u.toH1Function.grad_memVectorL2 hflux

namespace IsZeroTraceDirichletRhsWeakSolution

variable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
variable {u : H10Function U} {g : Vec d → Vec d}

theorem averageGradient_eq_zero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (_h : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    u.toH1Function.averageGradient = 0 := by
  simpa using H10Function.averageGradient_eq_zero u

theorem sub_const_iff
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hmem : MemVectorL2 U g) (c : Vec d) :
    IsZeroTraceDirichletRhsWeakSolution a U u (fun x => g x - c) ↔
      IsZeroTraceDirichletRhsWeakSolution a U u g := by
  constructor
  · intro h φ
    calc
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
          =
            ∫ x in U, vecDot (g x - c) (φ.toH1Function.grad x) ∂MeasureTheory.volume := h φ
      _ =
            ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume :=
          integral_vecDot_sub_const_zeroTraceGrad_eq (U := U) hmem φ c
  · intro h φ
    calc
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
          =
            ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := h φ
      _ =
            ∫ x in U, vecDot (g x - c) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
              symm
              exact integral_vecDot_sub_const_zeroTraceGrad_eq (U := U) hmem φ c

theorem add_const_iff
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hmem : MemVectorL2 U g) (c : Vec d) :
    IsZeroTraceDirichletRhsWeakSolution a U u (fun x => g x + c) ↔
      IsZeroTraceDirichletRhsWeakSolution a U u g := by
  simpa [sub_eq_add_neg] using sub_const_iff (a := a) (U := U) (u := u) (g := g) hmem (-c)

theorem energy_identity
    (h : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    ∫ x in U, vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))
      ∂MeasureTheory.volume =
      ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  simpa [vecDot_comm] using h u

theorem energy_identity_sub_const
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (h : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hmem : MemVectorL2 U g) (c : Vec d) :
    ∫ x in U, vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))
      ∂MeasureTheory.volume =
      ∫ x in U, vecDot (g x - c) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  calc
    ∫ x in U, vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))
      ∂MeasureTheory.volume
        =
          ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume :=
      energy_identity h
    _ =
          ∫ x in U, vecDot (g x - c) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
            symm
            exact integral_vecDot_sub_const_zeroTraceGrad_eq (U := U) hmem u c

theorem energy_le_rhs_pairing_of_isEllipticFieldOn
    {lam Lam : ℝ} (h : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    lam * ∫ x in U, vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume ≤
      ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hsq_int :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (u.toH1Function.grad x)) U :=
    integrableOn_vecNormSq_zeroTraceGrad u
  have hlhs_int :
      MeasureTheory.IntegrableOn (fun x => lam * vecNormSq (u.toH1Function.grad x)) U :=
    hsq_int.const_mul lam
  have henergy_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))) U :=
    integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn hEll u
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hpoint :
      ∀ᵐ x ∂ volumeMeasureOn U,
        lam * vecNormSq (u.toH1Function.grad x) ≤
          vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x)) := by
    filter_upwards [hmem] with x hx
    exact (hEll.2 x hx).2.2.1 (u.toH1Function.grad x)
  calc
    lam * ∫ x in U, vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume
        = ∫ x in U, lam * vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
    _ ≤
        ∫ x in U, vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))
          ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono_ae hlhs_int henergy_int hpoint
    _ = ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume :=
      energy_identity h

theorem energy_le_sub_const_rhs_pairing_of_isEllipticFieldOn
    {lam Lam : ℝ} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (h : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hmem : MemVectorL2 U g) (c : Vec d) :
    lam * ∫ x in U, vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume ≤
      ∫ x in U, vecDot (g x - c) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  calc
    lam * ∫ x in U, vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume
        ≤ ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume :=
      energy_le_rhs_pairing_of_isEllipticFieldOn h hEll
    _ =
        ∫ x in U, vecDot (g x - c) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
          symm
          exact integral_vecDot_sub_const_zeroTraceGrad_eq (U := U) hmem u c

theorem of_grad_eq
    {v : H10Function U}
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hgrad : v.toH1Function.grad = u.toH1Function.grad) :
    IsZeroTraceDirichletRhsWeakSolution a U v g := by
  intro φ
  simpa [hgrad] using hu φ

theorem sub_zero
    {v : H10Function U}
    {lam Lam : ℝ}
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution a U v g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsZeroTraceDirichletRhsWeakSolution a U (u - v) (0 : Vec d → Vec d) := by
  intro φ
  have huFlux : MemVectorL2 U (fun x => matVecMul (a x) (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2
  have hvFlux : MemVectorL2 U (fun x => matVecMul (a x) (v.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.toH1Function.grad_memVectorL2
  have huInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 huFlux φ.toH1Function.grad_memVectorL2
  have hvInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hvFlux φ.toH1Function.grad_memVectorL2
  have hfun :
      (fun x =>
        vecDot (matVecMul (a x) ((u - v).toH1Function.grad x)) (φ.toH1Function.grad x)) =
        (fun x =>
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x) -
            vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x)) := by
    funext x
    have hgradSubX :
        ((u - v).toH1Function.grad x) = u.toH1Function.grad x - v.toH1Function.grad x := by
      change ((u.toH1Function - v.toH1Function).grad x) =
        u.toH1Function.grad x - v.toH1Function.grad x
      exact congrArg (fun f => f x) (H1Function.sub_grad u.toH1Function v.toH1Function)
    rw [hgradSubX]
    simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left, vecDot_neg_left]
  calc
    ∫ x in U,
        vecDot (matVecMul (a x) ((u - v).toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
        =
          ∫ x in U,
            (vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x) -
              vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x))
            ∂MeasureTheory.volume := by
              rw [hfun]
    _ =
        ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume -
          ∫ x in U, vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
              rw [MeasureTheory.integral_sub huInt hvInt]
    _ =
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume -
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
              rw [hu φ, hv φ]
    _ = ∫ x in U, vecDot (0 : Vec d) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
          symm
          simp [vecDot]

theorem gradToVectorL2_eq_of_isEllipticFieldOn
    {v : H10Function U} {lam Lam : ℝ} (hne : Set.Nonempty U)
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution a U v g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.toH1Function.gradToVectorL2 = v.toH1Function.gradToVectorL2 := by
  let w : H10Function U := u - v
  have hw : IsZeroTraceDirichletRhsWeakSolution a U w (0 : Vec d → Vec d) :=
    sub_zero hu hv hEll
  rcases hne with ⟨x, hx⟩
  have hlam : 0 < lam := (hEll.2 x hx).1
  have henergy :
      lam * ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume ≤ 0 := by
    calc
      lam * ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume
          ≤ ∫ y in U, vecDot (0 : Vec d) (w.toH1Function.grad y) ∂MeasureTheory.volume :=
        energy_le_rhs_pairing_of_isEllipticFieldOn
          (u := w) (g := (0 : Vec d → Vec d)) hw hEll
      _ = 0 := by
            simp [vecDot]
  have hsqInt :
      MeasureTheory.IntegrableOn (fun y => vecNormSq (w.toH1Function.grad y)) U :=
    integrableOn_vecNormSq_zeroTraceGrad w
  have hsqNonneg :
      0 ≤ ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume :=
    MeasureTheory.integral_nonneg fun _ => vecNormSq_nonneg _
  have hsqLeZero :
      ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume ≤ 0 := by
    nlinarith
  have hsqZero :
      ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume = 0 :=
    le_antisymm hsqLeZero hsqNonneg
  have hsqAe :
      (fun y => vecNormSq (w.toH1Function.grad y)) =ᵐ[volumeMeasureOn U] 0 := by
    exact
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
        hsqInt.integrable).1 hsqZero
  have hgradAe :
      (fun y => w.toH1Function.grad y) =ᵐ[volumeMeasureOn U] 0 := by
    filter_upwards [hsqAe] with y hy
    exact vecNormSq_eq_zero hy
  have hgradZero : w.toH1Function.gradToVectorL2 = 0 := by
    apply MeasureTheory.Lp.ext
    let hzeroAe :=
      MeasureTheory.Lp.coeFn_zero (E := Vec d) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)
    filter_upwards
        [H1Function.coeFn_gradToVectorL2 w.toH1Function, hzeroAe, hgradAe]
      with y hwGrad hzero hy
    rw [hwGrad, hzero, hy]
  have hsub :
      u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 = 0 := by
    have hneg :
        (-v.toH1Function).gradToVectorL2 = -v.toH1Function.gradToVectorL2 := by
      simpa using H1Function.gradToVectorL2_smul (-1 : ℝ) v.toH1Function
    have hgradSubH1 :
        (u.toH1Function - v.toH1Function).gradToVectorL2 =
          u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 := by
      calc
        (u.toH1Function - v.toH1Function).gradToVectorL2
            = u.toH1Function.gradToVectorL2 + (-v.toH1Function).gradToVectorL2 := by
                simpa [sub_eq_add_neg] using
                  H1Function.gradToVectorL2_add u.toH1Function (-v.toH1Function)
        _ = u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 := by
              rw [hneg, sub_eq_add_neg]
    have hgradSub :
        (u - v).toH1Function.gradToVectorL2 =
          u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 := by
      simpa using! hgradSubH1
    calc
      u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2
          = (u - v).toH1Function.gradToVectorL2 := by
              symm
              exact hgradSub
      _ = 0 := hgradZero
  exact sub_eq_zero.mp hsub

theorem gradToVectorL2_eq_of_isOpenBoundedConvexDomain
    {v : H10Function U} {lam Lam : ℝ}
    (_hU : IsOpenBoundedConvexDomain U) (hne : Set.Nonempty U)
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution a U v g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.toH1Function.gradToVectorL2 = v.toH1Function.gradToVectorL2 :=
  gradToVectorL2_eq_of_isEllipticFieldOn hne hu hv hEll

theorem toScalarL2_eq_of_isOpenBoundedConvexDomain
    {v : H10Function U} {lam Lam : ℝ}
    (hU : IsOpenBoundedConvexDomain U) [NeZero d] (hne : Set.Nonempty U)
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution a U v g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.toH1Function.toScalarL2 = v.toH1Function.toScalarL2 := by
  let w : H10Function U := u - v
  have hgradEq :
      u.toH1Function.gradToVectorL2 = v.toH1Function.gradToVectorL2 :=
    gradToVectorL2_eq_of_isEllipticFieldOn hne hu hv hEll
  have hgradZero : w.toH1Function.gradToVectorL2 = 0 := by
    have hneg :
        (-v.toH1Function).gradToVectorL2 = -v.toH1Function.gradToVectorL2 := by
      simpa using H1Function.gradToVectorL2_smul (-1 : ℝ) v.toH1Function
    have hgradSubH1 :
        (u.toH1Function - v.toH1Function).gradToVectorL2 =
          u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 := by
      calc
        (u.toH1Function - v.toH1Function).gradToVectorL2
            = u.toH1Function.gradToVectorL2 + (-v.toH1Function).gradToVectorL2 := by
                simpa [sub_eq_add_neg] using
                  H1Function.gradToVectorL2_add u.toH1Function (-v.toH1Function)
        _ = u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 := by
              rw [hneg, sub_eq_add_neg]
    have hgradSub :
        (u - v).toH1Function.gradToVectorL2 =
          u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 := by
      simpa using! hgradSubH1
    calc
      w.toH1Function.gradToVectorL2
          = u.toH1Function.gradToVectorL2 - v.toH1Function.gradToVectorL2 := by
              simpa [w] using hgradSub
      _ = 0 := sub_eq_zero.mpr hgradEq
  have hP :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : H10Function U,
          ‖z.toH1Function.toScalarL2‖ ≤ C * z.toH1Function.gradientCoordL2NormSum :=
    H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hU
  have hvalZero :
      w.toH1Function.toScalarL2 = 0 :=
    H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      hP w hgradZero
  have hsub :
      u.toH1Function.toScalarL2 - v.toH1Function.toScalarL2 = 0 := by
    have hneg :
        (-v.toH1Function).toScalarL2 = -v.toH1Function.toScalarL2 := by
      simpa using H1Function.toScalarL2_smul (-1 : ℝ) v.toH1Function
    have hvalueSubH1 :
        (u.toH1Function - v.toH1Function).toScalarL2 =
          u.toH1Function.toScalarL2 - v.toH1Function.toScalarL2 := by
      calc
        (u.toH1Function - v.toH1Function).toScalarL2
            = u.toH1Function.toScalarL2 + (-v.toH1Function).toScalarL2 := by
                simpa [sub_eq_add_neg] using
                  H1Function.toScalarL2_add u.toH1Function (-v.toH1Function)
        _ = u.toH1Function.toScalarL2 - v.toH1Function.toScalarL2 := by
              rw [hneg, sub_eq_add_neg]
    have hvalueSub :
        (u - v).toH1Function.toScalarL2 =
          u.toH1Function.toScalarL2 - v.toH1Function.toScalarL2 := by
      simpa using! hvalueSubH1
    calc
      u.toH1Function.toScalarL2 - v.toH1Function.toScalarL2
          = (u - v).toH1Function.toScalarL2 := by
              symm
              exact hvalueSub
      _ = 0 := hvalZero
  exact sub_eq_zero.mp hsub

end IsZeroTraceDirichletRhsWeakSolution

namespace PotentialZeroTraceHilbert

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The Hilbert realization of the closed `L²` subspace modeling `\Lpoto(U)`. -/
noncomputable def closedSubmodule (M : PotentialSolenoidalL2Data U) :
    ClosedSubmodule ℝ (HilbertVectorL2 U) :=
  M.potentialZeroTrace.comap
    ((continuousLinearEquivVectorL2 (U := U)).symm.toContinuousLinearMap)

noncomputable abbrev submodule (M : PotentialSolenoidalL2Data U) :
    Submodule ℝ (HilbertVectorL2 U) :=
  (closedSubmodule (M := M)).toSubmodule

noncomputable abbrev Space (M : PotentialSolenoidalL2Data U) :=
  ↥(submodule (M := M))

noncomputable instance instSeminormedAddCommGroup (M : PotentialSolenoidalL2Data U) :
    SeminormedAddCommGroup (Space M) := by
  exact inferInstanceAs (SeminormedAddCommGroup (submodule (M := M)))

noncomputable instance instNormedAddCommGroup (M : PotentialSolenoidalL2Data U) :
    NormedAddCommGroup (Space M) := by
  exact inferInstanceAs (NormedAddCommGroup (submodule (M := M)))

noncomputable instance instNormedSpace (M : PotentialSolenoidalL2Data U) :
    NormedSpace ℝ (Space M) := by
  exact inferInstanceAs (NormedSpace ℝ (submodule (M := M)))

noncomputable instance instInnerProductSpace (M : PotentialSolenoidalL2Data U) :
    InnerProductSpace ℝ (Space M) := by
  exact inferInstanceAs (InnerProductSpace ℝ (submodule (M := M)))

noncomputable instance instCompleteSpace (M : PotentialSolenoidalL2Data U) :
    CompleteSpace (Space M) := by
  simpa [Space, submodule, closedSubmodule] using!
    (closedSubmodule (M := M)).isClosed.completeSpace_coe

/-- The ambient Hilbert-vector `L²` field represented by a point of
`\Lpoto(U)`. -/
abbrev field {M : PotentialSolenoidalL2Data U} (z : Space M) : HilbertVectorL2 U :=
  z.1

/-- The ambient vector `L²` field represented by a point of `\Lpoto(U)`. -/
noncomputable def vectorFieldCLM (M : PotentialSolenoidalL2Data U) :
    Space M →L[ℝ] VectorL2 U :=
  ((continuousLinearEquivVectorL2 (U := U)).symm.toContinuousLinearMap).comp
    (submodule (M := M)).subtypeL

noncomputable abbrev vectorField {M : PotentialSolenoidalL2Data U} (z : Space M) : VectorL2 U :=
  vectorFieldCLM M z

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem vectorFieldCLM_apply (M : PotentialSolenoidalL2Data U) (z : Space M) :
    vectorFieldCLM M z = vectorField z :=
  rfl

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem mem_potentialZeroTrace {M : PotentialSolenoidalL2Data U} (z : Space M) :
    vectorField z ∈ M.potentialZeroTrace := by
  exact (ClosedSubmodule.mem_comap).1 z.2

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem field_eq_toHilbertVectorL2OfVecField {M : PotentialSolenoidalL2Data U} (z : Space M) :
    field z =
      toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)) := by
  calc
    field z = vectorL2ToHilbertVectorL2 (U := U) (vectorField z) := by
      symm
      exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) (field z)
    _ =
        vectorL2ToHilbertVectorL2 (U := U)
          (toVectorL2 (MeasureTheory.Lp.memLp (vectorField z))) := by
            congr 1
            exact
              (MeasureTheory.Lp.toLp_coeFn
                (vectorField z)
                (MeasureTheory.Lp.memLp (vectorField z))).symm
    _ = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)) := by
          rfl

/-- The Hilbert-space element corresponding to the gradient of an `H¹₀`
function. -/
noncomputable def ofH10Function (M : PotentialSolenoidalL2Data U) (u : H10Function U) :
    Space M := by
  refine ⟨u.toH1Function.gradToHilbertVectorL2, ?_⟩
  change
    ((continuousLinearEquivVectorL2 (U := U)).symm u.toH1Function.gradToHilbertVectorL2) ∈
      M.potentialZeroTrace
  simpa [H1Function.gradToHilbertVectorL2, H1Function.gradToVectorL2] using!
    M.mem_potentialZeroTrace u.toH1Function.grad_memVectorL2 u.isPotentialZeroTraceOn

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem vectorField_ofH10Function (M : PotentialSolenoidalL2Data U) (u : H10Function U) :
    vectorField (ofH10Function M u) = u.toH1Function.gradToVectorL2 := by
  change
    ((continuousLinearEquivVectorL2 (U := U)).symm u.toH1Function.gradToHilbertVectorL2) =
      u.toH1Function.gradToVectorL2
  simpa [H1Function.gradToHilbertVectorL2, H1Function.gradToVectorL2] using
    hilbertVectorL2ToVectorL2_toHilbertVectorL2
      (U := U) (f := u.toH1Function.grad) u.toH1Function.grad_memVectorL2

/-- The coefficient-weighted field associated to a point of `\Lpoto(U)`. -/
noncomputable def coeffFieldCLM (M : PotentialSolenoidalL2Data U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) :
    Space M →L[ℝ] HilbertVectorL2 U :=
  (hilbertCoeffOperator hEll).comp ((submodule (M := M)).subtypeL)

/-- The coefficient-weighted bilinear form on the Hilbert realization of
`\Lpoto(U)`. -/
noncomputable def coeffBilin (M : PotentialSolenoidalL2Data U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) :
    Space M →L[ℝ] Space M →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (coeffFieldCLM (M := M) hEll) ((submodule (M := M)).subtypeL)

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem coeffBilin_apply {M : PotentialSolenoidalL2Data U}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (z w : Space M) :
    coeffBilin (M := M) hEll z w =
      inner ℝ (hilbertCoeffOperator hEll (field z)) (field w) := by
  simp [coeffBilin, coeffFieldCLM, ContinuousLinearMap.bilinearComp_apply, field]

/-- The forcing functional induced by `g` on the Hilbert realization of
`\Lpoto(U)`. -/
noncomputable def forcingFunctionalCLM (M : PotentialSolenoidalL2Data U)
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    Space M →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (HilbertVectorL2 U)
      (toHilbertVectorL2OfVecField hg)).comp
    ((submodule (M := M)).subtypeL)

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem forcingFunctionalCLM_apply {M : PotentialSolenoidalL2Data U}
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (z : Space M) :
    forcingFunctionalCLM (M := M) hg z =
      inner ℝ (toHilbertVectorL2OfVecField hg) (field z) := by
  simp [forcingFunctionalCLM, field]

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem coeffBilin_apply_eq_integral {M : PotentialSolenoidalL2Data U}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (z w : Space M) :
    coeffBilin (M := M) hEll z w =
      ∫ x in U,
        vecDot (matVecMul (a x) (vectorField z x)) (vectorField w x)
          ∂MeasureTheory.volume := by
  have hzField :
      field z = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)) :=
    field_eq_toHilbertVectorL2OfVecField z
  have hwField :
      field w = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField w)) :=
    field_eq_toHilbertVectorL2OfVecField w
  have hA :
      hilbertCoeffOperator hEll (field z) =
        toHilbertVectorL2OfVecField
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
            (MeasureTheory.Lp.memLp (vectorField z))) := by
    rw [hzField]
    simpa using
      hilbertCoeffOperator_toHilbertVectorL2OfVecField
        (U := U) (a := a) (lam := lam) (Lam := Lam) hEll
        (MeasureTheory.Lp.memLp (vectorField z))
  calc
    coeffBilin (M := M) hEll z w
        = inner ℝ (hilbertCoeffOperator hEll (field z)) (field w) := by
            simp [coeffBilin_apply]
    _ =
        inner ℝ
          (toHilbertVectorL2OfVecField
            (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
              (MeasureTheory.Lp.memLp (vectorField z))))
          (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField w))) := by
            rw [hA, hwField]
    _ =
        ∫ x in U,
          vecDot (matVecMul (a x) (vectorField z x)) (vectorField w x)
            ∂MeasureTheory.volume := by
              exact inner_toHilbertVectorL2OfVecField_eq_integral
                (U := U)
                (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
                  (MeasureTheory.Lp.memLp (vectorField z)))
                (MeasureTheory.Lp.memLp (vectorField w))

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem forcingFunctionalCLM_apply_eq_integral {M : PotentialSolenoidalL2Data U}
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (z : Space M) :
    forcingFunctionalCLM (M := M) hg z =
      ∫ x in U, vecDot (g x) (vectorField z x) ∂MeasureTheory.volume := by
  calc
    forcingFunctionalCLM (M := M) hg z
        = inner ℝ (toHilbertVectorL2OfVecField hg) (field z) := by
            simp [forcingFunctionalCLM_apply]
    _ =
        inner ℝ
          (toHilbertVectorL2OfVecField hg)
          (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z))) := by
            rw [field_eq_toHilbertVectorL2OfVecField z]
    _ = ∫ x in U, vecDot (g x) (vectorField z x) ∂MeasureTheory.volume := by
          exact inner_toHilbertVectorL2OfVecField_eq_integral
            (U := U) hg (MeasureTheory.Lp.memLp (vectorField z))

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem coeffBilin_self_ge_lam_mul_norm_sq {M : PotentialSolenoidalL2Data U}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (z : Space M) :
    lam * ‖z‖ ^ 2 ≤ coeffBilin (M := M) hEll z z := by
  have hsqInt :
      MeasureTheory.IntegrableOn
        (fun x => vecNormSq (vectorField z x)) U := by
    simpa [vecNormSq] using
      (integrableOn_vecDot_of_memVectorL2
        (MeasureTheory.Lp.memLp (vectorField z))
        (MeasureTheory.Lp.memLp (vectorField z)))
  have henergyInt :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (matVecMul (a x) (vectorField z x)) (vectorField z x)) U := by
    exact
      integrableOn_vecDot_of_memVectorL2
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
          (MeasureTheory.Lp.memLp (vectorField z)))
        (MeasureTheory.Lp.memLp (vectorField z))
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hpoint :
      ∀ᵐ x ∂ volumeMeasureOn U,
        lam * vecNormSq (vectorField z x) ≤
          vecDot (matVecMul (a x) (vectorField z x)) (vectorField z x) := by
    filter_upwards [hmem] with x hx
    simpa [vecDot_comm] using (hEll.2 x hx).2.2.1 (vectorField z x)
  have hnormSq :
      ‖z‖ ^ 2 =
        ∫ x in U, vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
    calc
      ‖z‖ ^ 2 = inner ℝ (field z) (field z) := by
            simp [field]
      _ =
          inner ℝ
            (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z)))
            (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp (vectorField z))) := by
              rw [field_eq_toHilbertVectorL2OfVecField z]
      _ =
          ∫ x in U, vecDot (vectorField z x) (vectorField z x) ∂MeasureTheory.volume := by
            exact inner_toHilbertVectorL2OfVecField_eq_integral
              (U := U)
              (MeasureTheory.Lp.memLp (vectorField z))
              (MeasureTheory.Lp.memLp (vectorField z))
      _ = ∫ x in U, vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
            simp [vecNormSq]
  calc
    lam * ‖z‖ ^ 2
        = lam * ∫ x in U, vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
            rw [hnormSq]
    _ = ∫ x in U, lam * vecNormSq (vectorField z x) ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤
        ∫ x in U,
          vecDot (matVecMul (a x) (vectorField z x)) (vectorField z x)
            ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint
    _ = coeffBilin (M := M) hEll z z := by
          symm
          exact coeffBilin_apply_eq_integral (M := M) hEll z z

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem isCoercive_coeffBilin {M : PotentialSolenoidalL2Data U}
    {a : CoeffField d} {lam Lam : ℝ} (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsCoercive (coeffBilin (M := M) hEll) := by
  rcases hne with ⟨x, hx⟩
  have hlam : 0 < lam := (hEll.2 x hx).1
  refine ⟨lam, hlam, ?_⟩
  intro z
  simpa [pow_two, mul_assoc] using coeffBilin_self_ge_lam_mul_norm_sq (M := M) hEll z

noncomputable def forcingRieszMap (M : PotentialSolenoidalL2Data U) :
    (Space M →L[ℝ] ℝ) → Space M :=
  fun ℓ => (InnerProductSpace.toDual ℝ (Space M)).symm ℓ

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem inner_forcingRieszMap_apply (M : PotentialSolenoidalL2Data U)
    (ℓ : Space M →L[ℝ] ℝ) (z : Space M) :
    inner ℝ (forcingRieszMap M ℓ) z = ℓ z := by
  change inner ℝ (((InnerProductSpace.toDual ℝ (Space M)).symm) ℓ) z = ℓ z
  exact
    InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ)
      (E := Space M)
      (x := z)
      (y := (ℓ : StrongDual ℝ (Space M)))

noncomputable def forcingRieszRep (M : PotentialSolenoidalL2Data U)
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    Space M :=
  forcingRieszMap M (forcingFunctionalCLM (M := M) hg)

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
@[simp] theorem inner_forcingRieszRep_apply (M : PotentialSolenoidalL2Data U)
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (z : Space M) :
    inner ℝ (forcingRieszRep M hg) z =
      forcingFunctionalCLM (M := M) hg z := by
  exact inner_forcingRieszMap_apply M (forcingFunctionalCLM (M := M) hg) z

/-- The unique Hilbert-space element of `\Lpoto(U)` solving the coefficient
problem with forcing `g`. -/
noncomputable def coeffProblemSolution (M : PotentialSolenoidalL2Data U)
    {a : CoeffField d} {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g) (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    Space M := by
  let hB : IsCoercive (coeffBilin (M := M) hEll) :=
    isCoercive_coeffBilin (M := M) hne hEll
  let e : Space M ≃L[ℝ] Space M := hB.continuousLinearEquivOfBilin
  exact e.symm (forcingRieszRep M hg)

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem coeffBilin_coeffProblemSolution_apply (M : PotentialSolenoidalL2Data U)
    {a : CoeffField d} {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g) (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a)
    (z : Space M) :
    coeffBilin (M := M) hEll
        (coeffProblemSolution (M := M) hg hne hEll) z =
      forcingFunctionalCLM (M := M) hg z := by
  let hB : IsCoercive (coeffBilin (M := M) hEll) :=
    isCoercive_coeffBilin (M := M) hne hEll
  let e : Space M ≃L[ℝ] Space M := hB.continuousLinearEquivOfBilin
  calc
    coeffBilin (M := M) hEll (coeffProblemSolution (M := M) hg hne hEll) z
        = inner ℝ (e (coeffProblemSolution (M := M) hg hne hEll)) z := by
            symm
            simpa [e, hB] using
              hB.continuousLinearEquivOfBilin_apply
                (coeffProblemSolution (M := M) hg hne hEll) z
    _ = inner ℝ (forcingRieszRep M hg) z := by
          rw [coeffProblemSolution, e.apply_symm_apply]
    _ = forcingFunctionalCLM (M := M) hg z := by
          exact inner_forcingRieszRep_apply M hg z

end PotentialZeroTraceHilbert

private noncomputable def vectorPairingCLM {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    VectorL2 U →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (HilbertVectorL2 U) (toHilbertVectorL2OfVecField hg)).comp
    ((continuousLinearEquivVectorL2 (U := U)).toContinuousLinearMap)

theorem exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g)
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    ∃ v : H10Function U, IsZeroTraceDirichletRhsWeakSolution a U v g := by
  let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  let z : PotentialZeroTraceHilbert.Space M :=
    PotentialZeroTraceHilbert.coeffProblemSolution (M := M) hg hne hEll
  let F : VectorL2 U := PotentialZeroTraceHilbert.vectorField z
  have hFsub : F ∈ M.potentialZeroTrace :=
    PotentialZeroTraceHilbert.mem_potentialZeroTrace z
  have hpot0 : IsPotentialZeroTraceOn U F := by
    simpa [M] using
      PotentialSolenoidalL2Data.isPotentialZeroTraceOn_of_mem_potentialZeroTrace_ofSubmoduleClosures
        (U := U) hRealize F hFsub
  have hfirst :
      ∀ φ : H10Function U,
        ∫ x in U, vecDot (matVecMul (a x) (F x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    intro φ
    let w : PotentialZeroTraceHilbert.Space M :=
      PotentialZeroTraceHilbert.ofH10Function (M := M) φ
    have hleft :
        ∫ x in U,
          vecDot (matVecMul (a x) (F x))
            (PotentialZeroTraceHilbert.vectorField w x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot (matVecMul (a x) (F x)) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [H1Function.coeFn_gradToVectorL2 φ.toH1Function] with x hx
      simpa [w] using congrArg (fun v : Vec d => vecDot (matVecMul (a x) (F x)) v) hx
    have hright :
        ∫ x in U, vecDot (g x) (PotentialZeroTraceHilbert.vectorField w x)
            ∂MeasureTheory.volume =
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [H1Function.coeFn_gradToVectorL2 φ.toH1Function] with x hx
      simpa [w] using congrArg (fun v : Vec d => vecDot (g x) v) hx
    calc
      ∫ x in U, vecDot (matVecMul (a x) (F x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
          =
            PotentialZeroTraceHilbert.coeffBilin (M := M) hEll z w := by
              rw [← hleft]
              symm
              simpa [F] using
                PotentialZeroTraceHilbert.coeffBilin_apply_eq_integral
                  (M := M) hEll z w
      _ =
            PotentialZeroTraceHilbert.forcingFunctionalCLM (M := M) hg w :=
        PotentialZeroTraceHilbert.coeffBilin_coeffProblemSolution_apply (M := M) hg hne hEll w
      _ =
            ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
              rw [← hright]
              exact PotentialZeroTraceHilbert.forcingFunctionalCLM_apply_eq_integral
                (M := M) hg w
  rcases hpot0 with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  intro φ
  simpa [hv] using hfirst φ

/-- A chosen zero-trace Dirichlet weak solution under the abstract
zero-trace-potential closure realization hypothesis. -/
noncomputable def zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g)
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    H10Function U :=
  Classical.choose
    (exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := U) (g := g) (lam := lam) (Lam := Lam)
      hg hRealize hne hEll)

theorem
    isZeroTraceDirichletRhsWeakSolution_zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g)
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    IsZeroTraceDirichletRhsWeakSolution a U
      (zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
        (a := a) (U := U) (g := g) (lam := lam) (Lam := Lam)
        hg hRealize hne hEll)
      g := by
  simpa [zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization]
    using
      (Classical.choose_spec
        (exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
          (a := a) (U := U) (g := g) (lam := lam) (Lam := Lam)
          hg hRealize hne hEll))

theorem gradToVectorL2_eq_zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : H10Function U} {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g)
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U)
    (hne : Set.Nonempty U)
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.toH1Function.gradToVectorL2 =
      (zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
        (a := a) (U := U) (g := g) (lam := lam) (Lam := Lam)
        hg hRealize hne hEll).toH1Function.gradToVectorL2 := by
  let v : H10Function U :=
    zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := U) (g := g) (lam := lam) (Lam := Lam)
      hg hRealize hne hEll
  have hv : IsZeroTraceDirichletRhsWeakSolution a U v g :=
    isZeroTraceDirichletRhsWeakSolution_zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := U) (g := g) (lam := lam) (Lam := Lam)
      hg hRealize hne hEll
  simpa [v] using
    IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (U := U) (a := a) (u := u) (v := v) (g := g) hne hu hv hEll

theorem exists_isZeroTraceDirichletRhsWeakSolution_of_gradient_firstVariation_eq_integral_of_isPotentialZeroTraceOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hfirst :
      ∀ φ : H10Function U,
        ∫ x in U, vecDot (matVecMul (a x) (f x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume)
    (hpot : IsPotentialZeroTraceOn U f) :
    ∃ v : H10Function U, IsZeroTraceDirichletRhsWeakSolution a U v g := by
  rcases hpot with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  intro φ
  simpa [hv] using hfirst φ

theorem exists_isZeroTraceDirichletRhsWeakSolution_of_firstVariation_eq_integral_of_isPotentialZeroTraceOn
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {g : Vec d → Vec d}
    (hfirst :
      ∀ φ : H10Function U,
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume)
    (hpot : IsPotentialZeroTraceOn U u.grad) :
    ∃ v : H10Function U, IsZeroTraceDirichletRhsWeakSolution a U v g := by
  exact
    exists_isZeroTraceDirichletRhsWeakSolution_of_gradient_firstVariation_eq_integral_of_isPotentialZeroTraceOn
      (a := a) (U := U) (f := u.grad) (g := g) hfirst hpot

end Homogenization
