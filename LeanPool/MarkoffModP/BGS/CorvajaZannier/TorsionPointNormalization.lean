/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FinitePlaceCompletion
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSeparability
public import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Integral

/-!
# Affine centers and normalization of torsion points

Construct coordinate-ring evaluations and their maximal ideals, and compare affine torsion
points with normalization places.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open IsDedekindDomain Multiplicative WithZero

variable {K : Type*} [Field K]

/-- An affine rational point of the plane curve `f = 0`. -/
abbrev AffinePlaneCurvePoint (f : MvPolynomial (Fin 2) K) :=
  {z : K × K // MvPolynomial.eval ![z.1, z.2] f = 0}

/-- Evaluation at an affine rational point, descended to the coordinate ring. -/
def planeCurvePointEval (f : MvPolynomial (Fin 2) K)
    (z : AffinePlaneCurvePoint f) : PlaneCurveCoordinateRing f →+* K :=
  Ideal.Quotient.lift (Ideal.span {f})
    (MvPolynomial.eval₂Hom (RingHom.id K) ![z.1.1, z.1.2]) (by
      intro g hg
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hg
      rw [map_mul]
      have hfzero :
          (MvPolynomial.eval₂Hom (RingHom.id K) ![z.1.1, z.1.2]) f = 0 := by
        change (MvPolynomial.eval ![z.1.1, z.1.2]) f = 0
        exact z.2
      rw [hfzero, zero_mul])

@[simp]
theorem planeCurvePointEval_coordinate (f : MvPolynomial (Fin 2) K)
    (z : AffinePlaneCurvePoint f) (i : Fin 2) :
    planeCurvePointEval f z (planeCurveCoordinate f i) = ![z.1.1, z.1.2] i := by
  simp [planeCurvePointEval, planeCurveCoordinate, planeCurveQuotientMap]

@[simp]
theorem planeCurvePointEval_algebraMap (f : MvPolynomial (Fin 2) K)
    (z : AffinePlaneCurvePoint f) (c : K) :
    planeCurvePointEval f z (algebraMap K (PlaneCurveCoordinateRing f) c) = c := by
  change planeCurvePointEval f z
    (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.C c)) = c
  simp [planeCurvePointEval]

theorem planeCurvePointEval_surjective (f : MvPolynomial (Fin 2) K)
    (z : AffinePlaneCurvePoint f) : Function.Surjective (planeCurvePointEval f z) := by
  intro c
  exact ⟨algebraMap K (PlaneCurveCoordinateRing f) c,
    planeCurvePointEval_algebraMap f z c⟩

/-- The maximal ideal of the affine coordinate ring attached to a rational point. -/
def affinePlaneCurvePointMaximalIdeal (f : MvPolynomial (Fin 2) K)
    (z : AffinePlaneCurvePoint f) : MaximalSpectrum (PlaneCurveCoordinateRing f) where
  asIdeal := RingHom.ker (planeCurvePointEval f z)
  isMaximal := RingHom.ker_isMaximal_of_surjective _
    (planeCurvePointEval_surjective f z)

/-- Distinct rational affine points define distinct maximal ideals. -/
theorem affinePlaneCurvePointMaximalIdeal_injective (f : MvPolynomial (Fin 2) K) :
    Function.Injective (affinePlaneCurvePointMaximalIdeal f) := by
  intro z w hzw
  have hker : RingHom.ker (planeCurvePointEval f z) =
      RingHom.ker (planeCurvePointEval f w) :=
    congrArg MaximalSpectrum.asIdeal hzw
  apply Subtype.ext
  apply Prod.ext
  · have hzmem : planeCurveCoordinate f 0 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.1 ∈
        RingHom.ker (planeCurvePointEval f z) := by
      change planeCurvePointEval f z
        (planeCurveCoordinate f 0 -
          algebraMap K (PlaneCurveCoordinateRing f) z.1.1) = 0
      simp
    have hwmem : planeCurveCoordinate f 0 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.1 ∈
        RingHom.ker (planeCurvePointEval f w) := by
      rw [← hker]
      exact hzmem
    change planeCurvePointEval f w
      (planeCurveCoordinate f 0 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.1) = 0 at hwmem
    have heval : w.1.1 - z.1.1 = 0 := by simpa using hwmem
    exact (sub_eq_zero.mp heval).symm
  · have hzmem : planeCurveCoordinate f 1 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.2 ∈
        RingHom.ker (planeCurvePointEval f z) := by
      change planeCurvePointEval f z
        (planeCurveCoordinate f 1 -
          algebraMap K (PlaneCurveCoordinateRing f) z.1.2) = 0
      simp
    have hwmem : planeCurveCoordinate f 1 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.2 ∈
        RingHom.ker (planeCurvePointEval f w) := by
      rw [← hker]
      exact hzmem
    change planeCurvePointEval f w
      (planeCurveCoordinate f 1 -
        algebraMap K (PlaneCurveCoordinateRing f) z.1.2) = 0 at hwmem
    have heval : w.1.2 - z.1.2 = 0 := by simpa using hwmem
    exact (sub_eq_zero.mp heval).symm

variable [Fintype K] [DecidableEq K]

/-- A torsion point in the finite-field intersection, as a finite subtype. -/
abbrev TorusCurveTorsionPoint (f : MvPolynomial (Fin 2) K)
    (firstOrder secondOrder : ℕ) :=
  {z : Kˣ × Kˣ // z ∈ BGS.External.torusCurveTorsionIntersection
    K f firstOrder secondOrder}

/-- Forget the unit witnesses and regard a torsion point as an affine point of
the plane curve. -/
def torsionPointToAffinePlaneCurvePoint
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    AffinePlaneCurvePoint f :=
  ⟨((z.1.1 : K), (z.1.2 : K)),
    (BGS.External.mem_torusCurveTorsionIntersection_iff.mp z.2).1⟩

theorem torsionPointToAffinePlaneCurvePoint_injective
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ) :
    Function.Injective
      (torsionPointToAffinePlaneCurvePoint f firstOrder secondOrder) := by
  intro z w hzw
  apply Subtype.ext
  apply Prod.ext <;> apply Units.ext
  · exact congrArg Prod.fst (congrArg Subtype.val hzw)
  · exact congrArg Prod.snd (congrArg Subtype.val hzw)

/-- A finite-field torsion point determines a maximal ideal of the affine
coordinate ring. -/
def torsionPointMaximalIdeal
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    MaximalSpectrum (PlaneCurveCoordinateRing f) :=
  affinePlaneCurvePointMaximalIdeal f
    (torsionPointToAffinePlaneCurvePoint f firstOrder secondOrder z)

theorem torsionPointMaximalIdeal_injective
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ) :
    Function.Injective (torsionPointMaximalIdeal f firstOrder secondOrder) :=
  (affinePlaneCurvePointMaximalIdeal_injective f).comp
    (torsionPointToAffinePlaneCurvePoint_injective f firstOrder secondOrder)

/-- The first torsion function belongs to the maximal ideal of its point. -/
theorem first_torsionFunction_mem_torsionPointMaximalIdeal
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    planeCurveCoordinate f 0 ^ firstOrder - 1 ∈
      (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal := by
  change planeCurvePointEval f
    (torsionPointToAffinePlaneCurvePoint f firstOrder secondOrder z)
      (planeCurveCoordinate f 0 ^ firstOrder - 1) = 0
  rw [map_sub, map_pow, map_one, planeCurvePointEval_coordinate]
  have hpow :=
    (BGS.External.mem_torusCurveTorsionIntersection_iff.mp z.2).2.1
  exact sub_eq_zero.mpr (congrArg Units.val hpow)

/-- The second torsion function belongs to the maximal ideal of its point. -/
theorem second_torsionFunction_mem_torsionPointMaximalIdeal
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    planeCurveCoordinate f 1 ^ secondOrder - 1 ∈
      (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal := by
  change planeCurvePointEval f
    (torsionPointToAffinePlaneCurvePoint f firstOrder secondOrder z)
      (planeCurveCoordinate f 1 ^ secondOrder - 1) = 0
  rw [map_sub, map_pow, map_one, planeCurvePointEval_coordinate]
  have hpow :=
    (BGS.External.mem_torusCurveTorsionIntersection_iff.mp z.2).2.2
  exact sub_eq_zero.mpr (congrArg Units.val hpow)

variable {f : MvPolynomial (Fin 2) K}
variable [IsDomain (PlaneCurveCoordinateRing f)]

/-- The affine normalization of the plane-curve coordinate ring inside its
fraction field. -/
abbrev PlaneCurveNormalization (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] :=
  integralClosure (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)

/-- Choose one normalization branch above an affine maximal ideal.  Lying over
guarantees that such a branch exists; no smoothness is assumed. -/
def planeCurveNormalizationBranch
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)]
    (m : MaximalSpectrum (PlaneCurveCoordinateRing f)) :
    MaximalSpectrum (PlaneCurveNormalization f) := by
  let hex := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := PlaneCurveNormalization f) m.asIdeal
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

omit [Fintype K] [DecidableEq K] in
theorem planeCurveNormalizationBranch_liesOver
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)]
    (m : MaximalSpectrum (PlaneCurveCoordinateRing f)) :
    (planeCurveNormalizationBranch f m).asIdeal.LiesOver m.asIdeal := by
  let hex := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := PlaneCurveNormalization f) m.asIdeal
  exact (Classical.choose_spec hex).2

omit [Fintype K] [DecidableEq K] in
/-- Chosen normalization branches above distinct affine maximal ideals remain
distinct, because their contractions are distinct. -/
theorem planeCurveNormalizationBranch_injective
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)] :
    Function.Injective (planeCurveNormalizationBranch f) := by
  intro m n hmn
  apply MaximalSpectrum.ext
  let hm : (planeCurveNormalizationBranch f m).asIdeal.LiesOver m.asIdeal :=
    planeCurveNormalizationBranch_liesOver f m
  let hn : (planeCurveNormalizationBranch f n).asIdeal.LiesOver n.asIdeal :=
    planeCurveNormalizationBranch_liesOver f n
  calc
    m.asIdeal = (planeCurveNormalizationBranch f m).asIdeal.under
        (PlaneCurveCoordinateRing f) :=
      Ideal.over_def
        (P := (planeCurveNormalizationBranch f m).asIdeal) (p := m.asIdeal)
    _ = (planeCurveNormalizationBranch f n).asIdeal.under
        (PlaneCurveCoordinateRing f) := by rw [hmn]
    _ = n.asIdeal :=
      (Ideal.over_def
        (P := (planeCurveNormalizationBranch f n).asIdeal) (p := n.asIdeal)).symm

/-- The chosen branch of the normalization above a torsion point. -/
def torsionPointNormalizationBranch
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)]
    (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    MaximalSpectrum (PlaneCurveNormalization f) :=
  planeCurveNormalizationBranch f
    (torsionPointMaximalIdeal f firstOrder secondOrder z)

theorem torsionPointNormalizationBranch_injective
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)]
    (firstOrder secondOrder : ℕ) :
    Function.Injective
      (torsionPointNormalizationBranch f firstOrder secondOrder) :=
  (planeCurveNormalizationBranch_injective f).comp
    (torsionPointMaximalIdeal_injective f firstOrder secondOrder)

/-- The first torsion function vanishes on the chosen normalization branch. -/
theorem first_torsionFunction_mem_normalizationBranch
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)]
    (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveNormalization f)
        (planeCurveCoordinate f 0 ^ firstOrder - 1) ∈
      (torsionPointNormalizationBranch f firstOrder secondOrder z).asIdeal := by
  let :
      (torsionPointNormalizationBranch f firstOrder secondOrder z).asIdeal.LiesOver
        (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal :=
    planeCurveNormalizationBranch_liesOver f
      (torsionPointMaximalIdeal f firstOrder secondOrder z)
  exact (Ideal.mem_of_liesOver
    (P := (torsionPointNormalizationBranch f firstOrder secondOrder z).asIdeal)
    (p := (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal) _).mp
      (first_torsionFunction_mem_torsionPointMaximalIdeal
        f firstOrder secondOrder z)

/-- The second torsion function vanishes on the chosen normalization branch. -/
theorem second_torsionFunction_mem_normalizationBranch
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)]
    (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveNormalization f)
        (planeCurveCoordinate f 1 ^ secondOrder - 1) ∈
      (torsionPointNormalizationBranch f firstOrder secondOrder z).asIdeal := by
  let :
      (torsionPointNormalizationBranch f firstOrder secondOrder z).asIdeal.LiesOver
        (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal :=
    planeCurveNormalizationBranch_liesOver f
      (torsionPointMaximalIdeal f firstOrder secondOrder z)
  exact (Ideal.mem_of_liesOver
    (P := (torsionPointNormalizationBranch f firstOrder secondOrder z).asIdeal)
    (p := (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal) _).mp
      (second_torsionFunction_mem_torsionPointMaximalIdeal
        f firstOrder secondOrder z)

/-- An integral-closure model of the plane-curve function field has that
function field as its fraction field. -/
noncomputable instance planeCurveIntegralClosureIsFractionRing
    {B : Type*} [CommRing B] [IsDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)] :
    IsFractionRing B (PlaneCurveFunctionField f) := by
  let : Algebra.IsAlgebraic (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := PlaneCurveCoordinateRing f)
      (K := PlaneCurveFunctionField f)
      (C := PlaneCurveFunctionField f)).mpr inferInstance
  exact IsIntegralClosure.isFractionRing_of_algebraic
    (PlaneCurveCoordinateRing f) B
      (fun x hx => IsFractionRing.injective
        (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f) (by simpa using hx))

/-- Membership in a height-one prime gives at least one unit of additive
finite-place order. -/
theorem one_le_finitePlaceOrder_of_mem
    {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (v : HeightOneSpectrum R) (a : R) (ha : a ∈ v.asIdeal) (ha0 : a ≠ 0) :
    (1 : ℤ) ≤ finitePlaceOrder v (algebraMap R L a) := by
  have hmap : algebraMap R L a ≠ 0 :=
    fun h ↦ ha0 ((IsFractionRing.injective R L) (by simpa using h))
  have hvaluation := valuation_eq_exp_neg_finitePlaceOrder
    v (algebraMap R L a) hmap
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at hvaluation
  have hlt : exp (-finitePlaceOrder v (algebraMap R L a)) < 1 := by
    rw [← hvaluation]
    exact (v.intValuation_lt_one_iff_mem a).2 ha
  rw [← exp_zero, exp_lt_exp] at hlt
  omega

/-- Generic local bridge for any Dedekind integral-closure model `B` of the
curve's function field.  A maximal ideal of `B` lying over the torsion point
is a finite place, and both torsion functions have order at least one there.

The branch is an explicit parameter, so a later global normalization or
projective model can supply its own chosen lift. -/
theorem liftedNormalizationBranch_torsion_orders_positive
    (f : MvPolynomial (Fin 2) K)
    [IsDomain (PlaneCurveCoordinateRing f)]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder)
    (branch : MaximalSpectrum B)
    (hbranch : branch.asIdeal.LiesOver
      (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal) :
    ∃ v : HeightOneSpectrum B,
      v.asIdeal = branch.asIdeal ∧
        (1 : ℤ) ≤ finitePlaceOrder v
          (planeCurveFunction f 0 ^ firstOrder - 1) ∧
        (1 : ℤ) ≤ finitePlaceOrder v
          (planeCurveFunction f 1 ^ secondOrder - 1) ∧
        (1 : ℤ) ≤ min
          (finitePlaceOrder v (planeCurveFunction f 0 ^ firstOrder - 1))
          (finitePlaceOrder v (planeCurveFunction f 1 ^ secondOrder - 1)) := by
  let A := PlaneCurveCoordinateRing f
  let L := PlaneCurveFunctionField f
  let firstRegular : B :=
    algebraMap A B (planeCurveCoordinate f 0 ^ firstOrder - 1)
  let secondRegular : B :=
    algebraMap A B (planeCurveCoordinate f 1 ^ secondOrder - 1)
  have hfirstMap : algebraMap B L firstRegular =
      planeCurveFunction f 0 ^ firstOrder - 1 := by
    simp only [firstRegular, map_sub, map_pow, map_one]
    rw [← IsScalarTower.algebraMap_apply A B L]
    rfl
  have hsecondMap : algebraMap B L secondRegular =
      planeCurveFunction f 1 ^ secondOrder - 1 := by
    simp only [secondRegular, map_sub, map_pow, map_one]
    rw [← IsScalarTower.algebraMap_apply A B L]
    rfl
  have hfirstRegular : firstRegular ≠ 0 := by
    intro hzero
    apply hfirstNonzero
    rw [← hfirstMap, hzero, map_zero]
  have hsecondRegular : secondRegular ≠ 0 := by
    intro hzero
    apply hsecondNonzero
    rw [← hsecondMap, hzero, map_zero]
  let : branch.asIdeal.LiesOver
      (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal := hbranch
  have hfirstMem : firstRegular ∈ branch.asIdeal := by
    exact (Ideal.mem_of_liesOver
      (P := branch.asIdeal)
      (p := (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal) _).mp
        (first_torsionFunction_mem_torsionPointMaximalIdeal
          f firstOrder secondOrder z)
  have hsecondMem : secondRegular ∈ branch.asIdeal := by
    exact (Ideal.mem_of_liesOver
      (P := branch.asIdeal)
      (p := (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal) _).mp
        (second_torsionFunction_mem_torsionPointMaximalIdeal
          f firstOrder secondOrder z)
  have hbranchNeBot : branch.asIdeal ≠ ⊥ := by
    intro hbot
    have : firstRegular = 0 := by
      simpa [hbot] using hfirstMem
    exact hfirstRegular this
  let v : HeightOneSpectrum B :=
    ⟨branch.asIdeal, branch.isMaximal.isPrime, hbranchNeBot⟩
  have hfirstOrder : (1 : ℤ) ≤
      finitePlaceOrder v (planeCurveFunction f 0 ^ firstOrder - 1) := by
    rw [← hfirstMap]
    exact one_le_finitePlaceOrder_of_mem v firstRegular hfirstMem hfirstRegular
  have hsecondOrder : (1 : ℤ) ≤
      finitePlaceOrder v (planeCurveFunction f 1 ^ secondOrder - 1) := by
    rw [← hsecondMap]
    exact one_le_finitePlaceOrder_of_mem v secondRegular hsecondMem hsecondRegular
  exact ⟨v, rfl, hfirstOrder, hsecondOrder, le_min hfirstOrder hsecondOrder⟩

end

end BGS.CorvajaZannier
