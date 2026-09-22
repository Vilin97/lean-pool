/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
/-!
# The logarithmic lattice of `S`-units

This file develops the logarithmic lattice of `S`-units. The
finite set `S` consists of the finite places; all infinite places are
understood to belong to the set of places used in the theorem.

The first construction uses the usual reduced archimedean logarithmic
space (one infinite coordinate is omitted) together with the integral
principal-divisor coordinates at `S`.  Its image is proved directly to
be a complete `ℤ`-lattice.  The normalized, all-place logarithmic map
and its coordinate-sum-zero hyperplane are constructed below from this
lattice.
-/

noncomputable section

open IsDedekindDomain Module
open scoped NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

open scoped Classical in
/-- The reduced logarithmic space for `S`-units.  It consists of the
Dirichlet logarithmic space and one real divisor coordinate for every
finite place in `S`. -/
abbrev ReducedLogSpace :=
  NumberField.Units.dirichletUnitTheorem.logSpace K × (S → ℝ)

open scoped Classical in
/-- The reduced logarithmic embedding.  At an infinite place it is the
usual multiplicity-weighted logarithm.  At a finite place it is the
integer exponent of the principal fractional ideal, regarded as a real
number. -/
noncomputable def reducedLog :
    Additive (SUnitGroup (K := K) S) →+
      ReducedLogSpace (K := K) S where
  toFun x :=
    (fun w =>
      w.1.mult *
        Real.log
          (w.1
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K)),
      fun v =>
        (divisorCoordinate (K := K) S
          (Additive.toMul x) v : ℝ))
  map_zero' := by
    apply Prod.ext
    · ext w
      simp
    · ext v
      change
        (divisorCoordinate (K := K) S 1 v : ℝ) = 0
      exact_mod_cast divisorCoordinate_one (K := K) S v
  map_add' x y := by
    apply Prod.ext
    · ext w
      simp [Real.log_mul, mul_add]
    · ext v
      change
        (divisorCoordinate (K := K) S
          (Additive.toMul x * Additive.toMul y) v : ℝ) =
          (divisorCoordinate (K := K) S
            (Additive.toMul x) v : ℝ) +
          (divisorCoordinate (K := K) S
            (Additive.toMul y) v : ℝ)
      exact_mod_cast
        divisorCoordinate_mul (K := K) S
          (Additive.toMul x) (Additive.toMul y) v

open scoped Classical in
/-- The normalized finite absolute value is the norm of the prime
raised to minus the corresponding principal-divisor exponent. -/
theorem adicAbv_eq_zpow_neg_divisorCoordinate
    (x : SUnitGroup (K := K) S) (v : S) :
    NumberField.HeightOneSpectrum.adicAbv K
        (v : HeightOneSpectrum (𝓞 K)) (((x : Kˣ) : K)) =
      (Ideal.absNorm
        (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) ^
          (-divisorCoordinate (K := K) S x v) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    valuation_eq_exp_neg_count (K := K)]
  rw [WithZeroMulInt.toNNReal_neg_apply]
  · norm_cast
  · simp

open scoped Classical in
/-- The logarithm of a normalized finite absolute value is the divisor
coordinate times `-log Nv`. -/
theorem log_adicAbv_eq_neg_divisorCoordinate_mul_log_absNorm
    (x : SUnitGroup (K := K) S) (v : S) :
    Real.log
        (NumberField.HeightOneSpectrum.adicAbv K
          (v : HeightOneSpectrum (𝓞 K)) (((x : Kˣ) : K))) =
      -(divisorCoordinate (K := K) S x v : ℝ) *
        Real.log
          (Ideal.absNorm
            (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) := by
  rw [adicAbv_eq_zpow_neg_divisorCoordinate (K := K) S,
    Real.log_zpow]
  push_cast
  ring

open scoped Classical in
/-- The `ℤ`-linear form of the reduced logarithmic embedding. -/
noncomputable def reducedLogLinearMap :
    Additive (SUnitGroup (K := K) S) →ₗ[ℤ]
      ReducedLogSpace (K := K) S :=
  (reducedLog (K := K) S).toIntLinearMap

open scoped Classical in
@[simp]
theorem reducedLog_fst_fromNumberFieldUnits
    (u : (𝓞 K)ˣ) :
    (reducedLog (K := K) S
      (Additive.ofMul
        (fromNumberFieldUnits (K := K) S u))).1 =
      NumberField.Units.logEmbedding K (Additive.ofMul u) := by
  ext w
  rfl

open scoped Classical in
@[simp]
theorem reducedLog_snd_fromNumberFieldUnits
    (u : (𝓞 K)ˣ) :
    (reducedLog (K := K) S
      (Additive.ofMul
        (fromNumberFieldUnits (K := K) S u))).2 = 0 := by
  ext v
  change
    (divisorCoordinate (K := K) S
      (fromNumberFieldUnits (K := K) S u) v : ℝ) = 0
  norm_cast
  have hrange :
      fromNumberFieldUnitsLinearMap (K := K) S
          (Additive.ofMul u) ∈
        LinearMap.range
          (fromNumberFieldUnitsLinearMap (K := K) S) :=
    LinearMap.mem_range_self _ _
  rw [range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
    (K := K) S] at hrange
  have hzero :=
    congrFun
      (LinearMap.mem_ker.mp hrange) v
  simpa [divisorLinearMap, divisor,
    fromNumberFieldUnitsLinearMap] using hzero

open scoped Classical in
/-- The reduced logarithm vanishes precisely on the roots of unity. -/
theorem reducedLog_eq_zero_iff
    (x : Additive (SUnitGroup (K := K) S)) :
    reducedLog (K := K) S x = 0 ↔
      x ∈ AddCommGroup.torsion
        (Additive (SUnitGroup (K := K) S)) := by
  constructor
  · intro hx
    have hxdiv :
        x ∈ LinearMap.ker
          (divisorLinearMap (K := K) S) := by
      apply LinearMap.mem_ker.mpr
      ext v
      have hv := congrFun (congrArg Prod.snd hx) v
      simpa [reducedLog, divisorLinearMap, divisor] using
        (show
          (divisorCoordinate (K := K) S
            (Additive.toMul x) v : ℝ) = 0 from hv)
    rw [← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
      (K := K) S] at hxdiv
    obtain ⟨u, hu⟩ := hxdiv
    have hxu :
        x =
          fromNumberFieldUnitsLinearMap (K := K) S u :=
      hu.symm
    have hlog :
        NumberField.Units.logEmbedding K u = 0 := by
      have hfst := congrArg Prod.fst hx
      rw [hxu] at hfst
      simpa [fromNumberFieldUnitsLinearMap] using hfst
    have hutors :
        Additive.toMul u ∈ NumberField.Units.torsion K := by
      exact
        NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp
          hlog
    change
      Additive.toMul x ∈
        CommGroup.torsion (SUnitGroup (K := K) S)
    rw [torsion_eq_rootsOfUnity_range (K := K) S]
    refine ⟨Additive.toMul u, hutors, ?_⟩
    exact (congrArg Additive.toMul hxu).symm
  · intro hx
    change
      Additive.toMul x ∈
        CommGroup.torsion (SUnitGroup (K := K) S) at hx
    rw [torsion_eq_rootsOfUnity_range (K := K) S] at hx
    obtain ⟨u, hu, hux⟩ := hx
    have hxadd :
        x =
          Additive.ofMul
            (fromNumberFieldUnits (K := K) S u) := by
      apply Additive.toMul.injective
      exact hux.symm
    rw [hxadd]
    apply Prod.ext
    ·
      simpa using
        (NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr
          hu)
    ·
      exact reducedLog_snd_fromNumberFieldUnits
        (K := K) S u

open scoped Classical in
/-- The kernel of the reduced logarithmic map is the additive torsion
submodule. -/
theorem reducedLogLinearMap_ker :
    LinearMap.ker (reducedLogLinearMap (K := K) S) =
      (AddCommGroup.torsion
        (Additive (SUnitGroup (K := K) S))).toIntSubmodule := by
  ext x
  rw [LinearMap.mem_ker]
  exact reducedLog_eq_zero_iff (K := K) S x

open scoped Classical in
/-- The reduced `S`-unit lattice. -/
noncomputable def reducedLogLattice :
    Submodule ℤ (ReducedLogSpace (K := K) S) :=
  LinearMap.range (reducedLogLinearMap (K := K) S)

open scoped Classical in
/-- A reduced logarithmic vector in the lattice vanishes when all of its
finite coordinates have norm less than one. -/
theorem norm_reducedLog_finite_lt_one_implies_zero
    {x : Additive (SUnitGroup (K := K) S)}
    (hx :
      ‖reducedLog (K := K) S x‖ < 1) :
    (reducedLog (K := K) S x).2 = 0 := by
  ext v
  have hv :
      ‖(reducedLog (K := K) S x).2 v‖ < 1 := by
    exact
      (norm_le_pi_norm _ v).trans_lt
        ((norm_snd_le
          (reducedLog (K := K) S x)).trans_lt hx)
  change
    (divisorCoordinate (K := K) S
      (Additive.toMul x) v : ℝ) = 0
  change
    |(divisorCoordinate (K := K) S
      (Additive.toMul x) v : ℝ)| < 1 at hv
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at hv
  exact_mod_cast Int.abs_lt_one_iff.mp hv

open scoped Classical in
/-- The reduced logarithmic image is discrete.  Near the origin the
integral finite coordinates must vanish, reducing the assertion to the
ordinary Dirichlet unit lattice. -/
instance instDiscreteTopology_reducedLogLattice :
    DiscreteTopology (reducedLogLattice (K := K) S) := by
  classical
  let :
      DiscreteTopology
        {x :
          NumberField.Units.dirichletUnitTheorem.logSpace K //
          x ∈ NumberField.Units.unitLattice K} := by
    infer_instance
  obtain ⟨ε, hεpos, hε⟩ :=
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (s := (NumberField.Units.unitLattice K :
        Set
          (NumberField.Units.dirichletUnitTheorem.logSpace K)))
      DiscreteTopology.isDiscrete
      (show
        (0 :
          NumberField.Units.dirichletUnitTheorem.logSpace K) ∈
        NumberField.Units.unitLattice K by simp)
  let δ : ℝ := min ε 1
  have hδpos : 0 < δ := lt_min hεpos zero_lt_one
  refine discreteTopology_iff_isOpen_singleton_zero.mpr
    ⟨Metric.ball 0 δ, Metric.isOpen_ball, ?_⟩
  ext z
  constructor
  · intro hz
    have hzlt : ‖(z : ReducedLogSpace (K := K) S)‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    obtain ⟨x, hx⟩ := z.property
    have hxlog :
        reducedLog (K := K) S x =
          (z : ReducedLogSpace (K := K) S) := hx
    have hfin :
        (reducedLog (K := K) S x).2 = 0 := by
      apply norm_reducedLog_finite_lt_one_implies_zero
        (K := K) S
      rw [hxlog]
      exact hzlt.trans_le (min_le_right _ _)
    have hxdiv :
        x ∈ LinearMap.ker
          (divisorLinearMap (K := K) S) := by
      apply LinearMap.mem_ker.mpr
      ext v
      have hv := congrFun hfin v
      change
        divisorCoordinate (K := K) S
          (Additive.toMul x) v = 0
      have hvreal :
          (divisorCoordinate (K := K) S
            (Additive.toMul x) v : ℝ) = 0 := by
        simpa [reducedLog] using hv
      exact_mod_cast hvreal
    rw [← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
      (K := K) S] at hxdiv
    obtain ⟨u, hu⟩ := hxdiv
    have hinf :
        NumberField.Units.logEmbedding K u =
          (z : ReducedLogSpace (K := K) S).1 := by
      rw [← hxlog, ← hu]
      simp [fromNumberFieldUnitsLinearMap]
    have hunitmem :
        NumberField.Units.logEmbedding K u ∈
          NumberField.Units.unitLattice K := by
      exact ⟨u, trivial, rfl⟩
    have hunitball :
        NumberField.Units.logEmbedding K u ∈
          Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right]
      rw [hinf]
      exact
        (norm_fst_le
          (z : ReducedLogSpace (K := K) S)).trans_lt
            (hzlt.trans_le (min_le_left _ _))
    have hunitzero :
        NumberField.Units.logEmbedding K u = 0 := by
      have :
          NumberField.Units.logEmbedding K u ∈
            Metric.ball 0 ε ∩
              (NumberField.Units.unitLattice K :
                Set
                  (NumberField.Units.dirichletUnitTheorem.logSpace K)) :=
        ⟨hunitball, hunitmem⟩
      rw [hε] at this
      exact this
    apply Subtype.ext
    rw [← hxlog]
    apply Prod.ext
    · rw [← hu]
      simpa [fromNumberFieldUnitsLinearMap] using hunitzero
    · exact hfin
  · intro hz
    have hz0 : z = 0 := by
      simpa using hz
    subst z
    simp [Metric.mem_ball, hδpos]

open scoped Classical in
/-- The integral rank of the reduced logarithmic lattice is the
Dirichlet unit rank plus the number of finite places in `S`. -/
theorem finrank_reducedLogLattice :
    Module.finrank ℤ (reducedLogLattice (K := K) S) =
      NumberField.Units.rank K + S.card := by
  let f := reducedLogLinearMap (K := K) S
  calc
    Module.finrank ℤ (reducedLogLattice (K := K) S) =
        Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S) ⧸
            LinearMap.ker f) :=
      f.quotKerEquivRange.symm.finrank_eq
    _ = Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S) ⧸
            (AddCommGroup.torsion
              (Additive
                (SUnitGroup (K := K) S))).toIntSubmodule) := by
      rw [show LinearMap.ker f =
        (AddCommGroup.torsion
          (Additive
            (SUnitGroup (K := K) S))).toIntSubmodule from
          reducedLogLinearMap_ker (K := K) S]
    _ = Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) := by
      exact finrank_quotient_torsion_eq
    _ = NumberField.Units.rank K + S.card :=
      finrank (K := K) S

open scoped Classical in
/-- The reduced logarithmic space has dimension equal to the Dirichlet
unit rank plus the number of finite places in `S`. -/
theorem finrank_reducedLogSpace :
    Module.finrank ℝ (ReducedLogSpace (K := K) S) =
      NumberField.Units.rank K + S.card := by
  classical
  simp [NumberField.Units.rank]

open scoped Classical in
/-- The reduced logarithmic lattice spans its whole real ambient
space. -/
theorem reducedLogLattice_span_eq_top :
    Submodule.span ℝ
      (reducedLogLattice (K := K) S :
        Set (ReducedLogSpace (K := K) S)) = ⊤ := by
  classical
  let :
      DiscreteTopology
        (Submodule.span ℤ
          (reducedLogLattice (K := K) S :
            Set (ReducedLogSpace (K := K) S))) := by
    rw [Submodule.span_eq]
    infer_instance
  apply Submodule.eq_top_of_finrank_eq
  change
    Set.finrank ℝ
      (reducedLogLattice (K := K) S :
        Set (ReducedLogSpace (K := K) S)) =
      Module.finrank ℝ (ReducedLogSpace (K := K) S)
  calc
    Set.finrank ℝ
        (reducedLogLattice (K := K) S :
          Set (ReducedLogSpace (K := K) S)) =
        Set.finrank ℤ
          (reducedLogLattice (K := K) S :
            Set (ReducedLogSpace (K := K) S)) :=
      Real.finrank_eq_int_finrank_of_discrete inferInstance
    _ = Module.finrank ℤ
          (reducedLogLattice (K := K) S) := by
      rw [Set.finrank, Submodule.span_eq]
    _ = NumberField.Units.rank K + S.card :=
      finrank_reducedLogLattice (K := K) S
    _ = Module.finrank ℝ
          (ReducedLogSpace (K := K) S) :=
      (finrank_reducedLogSpace (K := K) S).symm

open scoped Classical in
/-- The reduced logarithmic image of the `S`-units is a complete
`ℤ`-lattice. -/
instance instIsZLattice_reducedLogLattice :
    IsZLattice ℝ (reducedLogLattice (K := K) S) where
  span_top := reducedLogLattice_span_eq_top (K := K) S

section FullLogarithmicSpace

open scoped Classical in
/-- The places occurring in the `S`-unit theorem: every infinite place
and the finite places belonging to `S`. -/
abbrev LogPlace :=
  NumberField.InfinitePlace K ⊕ S

open scoped Classical in
/-- The ambient real coordinate space indexed by all places occurring
in the `S`-unit theorem. -/
abbrev FullLogSpace :=
  LogPlace (K := K) S → ℝ

open scoped Classical in
/-- Sum of all logarithmic coordinates. -/
noncomputable def coordinateSum :
    FullLogSpace (K := K) S →ₗ[ℝ] ℝ where
  toFun z := ∑ p, z p
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    change
      (∑ p : LogPlace (K := K) S, c * x p) =
        c * ∑ p : LogPlace (K := K) S, x p
    rw [Finset.mul_sum]

open scoped Classical in
/-- The coordinate-sum-zero hyperplane in the full logarithmic
space. -/
abbrev LogHyperplane :=
  LinearMap.ker (coordinateSum (K := K) S)

open scoped Classical in
/-- The normalized logarithmic absolute-value map at all places in the
`S`-unit theorem. -/
noncomputable def fullLogAmbient :
    Additive (SUnitGroup (K := K) S) →+
      FullLogSpace (K := K) S where
  toFun x p :=
    match p with
    | Sum.inl w =>
        w.mult *
          Real.log
            (w
              (((Additive.toMul x :
                SUnitGroup (K := K) S) : Kˣ) : K))
    | Sum.inr v =>
        Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K))
  map_zero' := by
    ext p
    cases p <;> simp
  map_add' x y := by
    ext p
    cases p <;> simp [Real.log_mul, mul_add]

open scoped Classical in
@[simp]
theorem fullLogAmbient_infinite
    (x : Additive (SUnitGroup (K := K) S))
    (w : NumberField.InfinitePlace K) :
    fullLogAmbient (K := K) S x (Sum.inl w) =
      w.mult *
        Real.log
          (w
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K)) :=
  rfl

open scoped Classical in
@[simp]
theorem fullLogAmbient_finite
    (x : Additive (SUnitGroup (K := K) S)) (v : S) :
    fullLogAmbient (K := K) S x (Sum.inr v) =
      Real.log
        (NumberField.HeightOneSpectrum.adicAbv K
          (v : HeightOneSpectrum (𝓞 K))
          (((Additive.toMul x :
            SUnitGroup (K := K) S) : Kˣ) : K)) :=
  rfl

open scoped Classical in
/-- An `S`-unit has normalized finite absolute value one outside `S`. -/
theorem adicAbv_eq_one_of_not_mem
    (x : SUnitGroup (K := K) S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    NumberField.HeightOneSpectrum.adicAbv K v
        (((x : Kˣ) : K)) = 1 := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    x.property v hv]
  simp

open scoped Classical in
/-- For an `S`-unit the finite part of the global product formula is
the product over the finite places in `S`. -/
theorem finprod_finitePlace_eq_prod_adicAbv
    (x : SUnitGroup (K := K) S) :
    (∏ᶠ w : NumberField.FinitePlace K,
        w (((x : Kˣ) : K))) =
      ∏ v : S,
        NumberField.HeightOneSpectrum.adicAbv K
          (v : HeightOneSpectrum (𝓞 K))
          (((x : Kˣ) : K)) := by
  rw [← finprod_comp_equiv
    NumberField.FinitePlace.equivHeightOneSpectrum.symm]
  simp_rw
    [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
      NumberField.FinitePlace.norm_embedding,
      NumberField.HeightOneSpectrum.adicAbv_def]
  rw [finprod_eq_prod_of_mulSupport_subset
    (s := S)]
  · exact
      (Finset.prod_coe_sort
        (s := S)
        (f := fun v : HeightOneSpectrum (𝓞 K) =>
          (NumberField.HeightOneSpectrum.adicAbv K v
            (((x : Kˣ) : K))))).symm
  · intro v hv
    by_contra hnot
    apply hv
    simp [x.property v hnot]

open scoped Classical in
/-- Logarithmic form of the product formula, restricted to the places
of the `S`-unit theorem. -/
theorem sum_log_absoluteValues_eq_zero
    (x : SUnitGroup (K := K) S) :
    (∑ w : NumberField.InfinitePlace K,
        w.mult * Real.log (w (((x : Kˣ) : K)))) +
      ∑ v : S,
        Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((x : Kˣ) : K))) = 0 := by
  have hx0 : (((x : Kˣ) : K)) ≠ 0 :=
    Units.ne_zero (x : Kˣ)
  have hprod := NumberField.prod_abs_eq_one hx0
  rw [finprod_finitePlace_eq_prod_adicAbv
    (K := K) S x] at hprod
  calc
    (∑ w : NumberField.InfinitePlace K,
        w.mult * Real.log (w (((x : Kˣ) : K)))) +
      ∑ v : S,
        Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((x : Kˣ) : K))) =
        Real.log
            (∏ w : NumberField.InfinitePlace K,
              w (((x : Kˣ) : K)) ^ w.mult) +
          Real.log
            (∏ v : S,
              NumberField.HeightOneSpectrum.adicAbv K
                (v : HeightOneSpectrum (𝓞 K))
                (((x : Kˣ) : K))) := by
      congr 1
      · rw [Real.log_prod]
        · apply Finset.sum_congr rfl
          intro w _
          rw [Real.log_pow]
        · intro w _
          exact pow_ne_zero _ ((w.pos_iff.mpr hx0).ne')
      · rw [Real.log_prod]
        intro v _
        exact
          ((NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))).pos_iff.mpr hx0).ne'
    _ = Real.log
        ((∏ w : NumberField.InfinitePlace K,
            w (((x : Kˣ) : K)) ^ w.mult) *
          ∏ v : S,
            NumberField.HeightOneSpectrum.adicAbv K
              (v : HeightOneSpectrum (𝓞 K))
              (((x : Kˣ) : K))) := by
      rw [Real.log_mul]
      · exact Finset.prod_ne_zero_iff.mpr fun w _ ↦
          pow_ne_zero _ ((w.pos_iff.mpr hx0).ne')
      · exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
          ((NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))).pos_iff.mpr hx0).ne'
    _ = 0 := by
      rw [hprod, Real.log_one]

open scoped Classical in
theorem fullLogAmbient_mem_logHyperplane
    (x : Additive (SUnitGroup (K := K) S)) :
    fullLogAmbient (K := K) S x ∈
      LogHyperplane (K := K) S := by
  apply LinearMap.mem_ker.mpr
  change
    ∑ p : LogPlace (K := K) S,
      fullLogAmbient (K := K) S x p = 0
  rw [Fintype.sum_sum_type]
  exact
    sum_log_absoluteValues_eq_zero (K := K) S
      (Additive.toMul x)

open scoped Classical in
/-- The normalized all-place logarithmic map with codomain restricted
to the coordinate-sum-zero hyperplane. -/
noncomputable def fullLog :
    Additive (SUnitGroup (K := K) S) →+
      LogHyperplane (K := K) S :=
  (fullLogAmbient (K := K) S).codRestrict
    (LogHyperplane (K := K) S)
    (fullLogAmbient_mem_logHyperplane (K := K) S)

open scoped Classical in
/-- The nonzero scale converting an integral divisor coordinate into
the logarithm of the corresponding normalized finite absolute value. -/
noncomputable def finiteLogWeight (v : S) : ℝ :=
  -Real.log
    (Ideal.absNorm
      (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ)

open scoped Classical in
theorem finiteLogWeight_ne_zero (v : S) :
    finiteLogWeight (K := K) S v ≠ 0 := by
  have hNv :
      (1 : ℝ) <
        (Ideal.absNorm
          (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) := by
    exact_mod_cast
      NumberField.HeightOneSpectrum.one_lt_absNorm
        (v : HeightOneSpectrum (𝓞 K))
  exact neg_ne_zero.mpr (ne_of_gt (Real.log_pos hNv))

open scoped Classical in
/-- Forget the distinguished infinite coordinate and divide the finite
logarithmic coordinates by their nonzero normalizing weights. -/
noncomputable def forgetDistinguishedLog :
    LogHyperplane (K := K) S →ₗ[ℝ]
      ReducedLogSpace (K := K) S where
  toFun z :=
    (fun w => (z : FullLogSpace (K := K) S) (Sum.inl w.1),
      fun v =>
        (z : FullLogSpace (K := K) S) (Sum.inr v) /
          finiteLogWeight (K := K) S v)
  map_add' x y := by
    apply Prod.ext
    · ext w
      rfl
    · ext v
      simp [add_div]
  map_smul' c x := by
    apply Prod.ext
    · ext w
      rfl
    · ext v
      change
        (c *
            (x : FullLogSpace (K := K) S) (Sum.inr v)) /
            finiteLogWeight (K := K) S v =
          c *
            ((x : FullLogSpace (K := K) S) (Sum.inr v) /
              finiteLogWeight (K := K) S v)
      ring

open scoped Classical in
/-- Forgetting the distinguished logarithmic coordinate is injective on
the product-formula hyperplane. -/
theorem forgetDistinguishedLog_injective :
    Function.Injective (forgetDistinguishedLog (K := K) S) := by
  intro x y hxy
  have hinf :
      ∀ w :
          {w : NumberField.InfinitePlace K //
            w ≠
              NumberField.Units.dirichletUnitTheorem.w₀},
        (x : FullLogSpace (K := K) S) (Sum.inl w.1) =
          (y : FullLogSpace (K := K) S) (Sum.inl w.1) := by
    intro w
    exact congrFun (congrArg Prod.fst hxy) w
  have hfin :
      ∀ v : S,
        (x : FullLogSpace (K := K) S) (Sum.inr v) =
          (y : FullLogSpace (K := K) S) (Sum.inr v) := by
    intro v
    have hv := congrFun (congrArg Prod.snd hxy) v
    exact
      (div_left_inj'
        (finiteLogWeight_ne_zero (K := K) S v)).mp hv
  apply Subtype.ext
  funext p
  cases p with
  | inr v => exact hfin v
  | inl w =>
      by_cases hw :
          w =
            NumberField.Units.dirichletUnitTheorem.w₀
      · subst w
        have hxsum :
            (x : FullLogSpace (K := K) S)
                (Sum.inl
                  NumberField.Units.dirichletUnitTheorem.w₀) +
                (∑ v :
                    {w : NumberField.InfinitePlace K //
                      w ≠
                        NumberField.Units.dirichletUnitTheorem.w₀},
                  (x : FullLogSpace (K := K) S)
                    (Sum.inl v.1)) +
              ∑ v : S,
                (x : FullLogSpace (K := K) S)
                  (Sum.inr v) = 0 := by
          have hxker := LinearMap.mem_ker.mp x.property
          change
            ∑ p : LogPlace (K := K) S,
              (x : FullLogSpace (K := K) S) p = 0 at hxker
          rw [Fintype.sum_sum_type,
            Fintype.sum_eq_add_sum_subtype_ne _
              NumberField.Units.dirichletUnitTheorem.w₀] at hxker
          exact hxker
        have hysum :
            (y : FullLogSpace (K := K) S)
                (Sum.inl
                  NumberField.Units.dirichletUnitTheorem.w₀) +
                (∑ v :
                    {w : NumberField.InfinitePlace K //
                      w ≠
                        NumberField.Units.dirichletUnitTheorem.w₀},
                  (y : FullLogSpace (K := K) S)
                    (Sum.inl v.1)) +
              ∑ v : S,
                (y : FullLogSpace (K := K) S)
                  (Sum.inr v) = 0 := by
          have hyker := LinearMap.mem_ker.mp y.property
          change
            ∑ p : LogPlace (K := K) S,
              (y : FullLogSpace (K := K) S) p = 0 at hyker
          rw [Fintype.sum_sum_type,
            Fintype.sum_eq_add_sum_subtype_ne _
              NumberField.Units.dirichletUnitTheorem.w₀] at hyker
          exact hyker
        have hsuminf :
            (∑ v :
                {w : NumberField.InfinitePlace K //
                  w ≠
                    NumberField.Units.dirichletUnitTheorem.w₀},
              (x : FullLogSpace (K := K) S)
                (Sum.inl v.1)) =
              ∑ v :
                {w : NumberField.InfinitePlace K //
                  w ≠
                    NumberField.Units.dirichletUnitTheorem.w₀},
                (y : FullLogSpace (K := K) S)
                  (Sum.inl v.1) := by
          apply Finset.sum_congr rfl
          intro v _
          exact hinf v
        have hsumfin :
            (∑ v : S,
              (x : FullLogSpace (K := K) S)
                (Sum.inr v)) =
              ∑ v : S,
                (y : FullLogSpace (K := K) S)
                  (Sum.inr v) := by
          apply Finset.sum_congr rfl
          intro v _
          exact hfin v
        linarith
      · exact hinf ⟨w, hw⟩

open scoped Classical in
/-- Every reduced logarithmic vector has a lift to the product-formula
hyperplane. -/
theorem forgetDistinguishedLog_surjective :
    Function.Surjective (forgetDistinguishedLog (K := K) S) := by
  intro z
  let completed : FullLogSpace (K := K) S :=
    fun p =>
      match p with
      | Sum.inl w =>
          if hw :
              w =
                NumberField.Units.dirichletUnitTheorem.w₀ then
            -(∑ v :
                {w : NumberField.InfinitePlace K //
                  w ≠
                    NumberField.Units.dirichletUnitTheorem.w₀},
                z.1 v) -
              ∑ v : S,
                finiteLogWeight (K := K) S v * z.2 v
          else
            z.1 ⟨w, hw⟩
      | Sum.inr v =>
          finiteLogWeight (K := K) S v * z.2 v
  have hcompleted :
      completed ∈ LogHyperplane (K := K) S := by
    apply LinearMap.mem_ker.mpr
    change
      ∑ p : LogPlace (K := K) S, completed p = 0
    rw [Fintype.sum_sum_type,
      Fintype.sum_eq_add_sum_subtype_ne _
        NumberField.Units.dirichletUnitTheorem.w₀]
    have hw0 :
        completed
            (Sum.inl
              NumberField.Units.dirichletUnitTheorem.w₀) =
          -(∑ v :
              {w : NumberField.InfinitePlace K //
                w ≠
                  NumberField.Units.dirichletUnitTheorem.w₀},
              z.1 v) -
            ∑ v : S,
              finiteLogWeight (K := K) S v * z.2 v := by
      simp [completed]
    have hinf :
        (∑ v :
            {w : NumberField.InfinitePlace K //
              w ≠
                NumberField.Units.dirichletUnitTheorem.w₀},
          completed (Sum.inl v.1)) =
          ∑ v :
            {w : NumberField.InfinitePlace K //
              w ≠
                NumberField.Units.dirichletUnitTheorem.w₀},
            z.1 v := by
      apply Finset.sum_congr rfl
      intro v _
      simp [completed, v.property]
    have hfin :
        (∑ v : S, completed (Sum.inr v)) =
          ∑ v : S,
            finiteLogWeight (K := K) S v * z.2 v := by
      rfl
    rw [hw0, hinf, hfin]
    ring
  let y : LogHyperplane (K := K) S :=
    ⟨completed, hcompleted⟩
  refine ⟨y, ?_⟩
  apply Prod.ext
  · ext w
    simp [forgetDistinguishedLog, y, completed, w.property]
  · ext v
    simp [forgetDistinguishedLog, y, completed,
      finiteLogWeight_ne_zero (K := K) S v]

open scoped Classical in
/-- Removing the distinguished infinite coordinate and rescaling the
finite coordinates is a real linear equivalence. -/
noncomputable def logHyperplaneEquivReduced :
    LogHyperplane (K := K) S ≃ₗ[ℝ]
      ReducedLogSpace (K := K) S :=
  LinearEquiv.ofBijective
    (forgetDistinguishedLog (K := K) S)
    ⟨forgetDistinguishedLog_injective (K := K) S,
      forgetDistinguishedLog_surjective (K := K) S⟩

open scoped Classical in
/-- Under the coordinate equivalence, the normalized all-place
logarithm is exactly the reduced logarithm. -/
theorem logHyperplaneEquivReduced_fullLog
    (x : Additive (SUnitGroup (K := K) S)) :
    logHyperplaneEquivReduced (K := K) S
        (fullLog (K := K) S x) =
      reducedLog (K := K) S x := by
  apply Prod.ext
  · ext w
    rfl
  · ext v
    have hlog :
        Real.log
          (Ideal.absNorm
            (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) ≠ 0 :=
      neg_ne_zero.mp
        (finiteLogWeight_ne_zero (K := K) S v)
    change
      Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K)) /
          finiteLogWeight (K := K) S v =
        (divisorCoordinate (K := K) S
          (Additive.toMul x) v : ℝ)
    rw [log_adicAbv_eq_neg_divisorCoordinate_mul_log_absNorm
      (K := K) S]
    dsimp [finiteLogWeight]
    field_simp [hlog]

open scoped Classical in
/-- The kernel of the normalized all-place logarithm is the group of
roots of unity. -/
theorem fullLog_eq_zero_iff
    (x : Additive (SUnitGroup (K := K) S)) :
    fullLog (K := K) S x = 0 ↔
      x ∈ AddCommGroup.torsion
        (Additive (SUnitGroup (K := K) S)) := by
  rw [← reducedLog_eq_zero_iff (K := K) S]
  constructor
  · intro hx
    have := congrArg
      (logHyperplaneEquivReduced (K := K) S) hx
    simpa [logHyperplaneEquivReduced_fullLog] using this
  · intro hx
    apply (logHyperplaneEquivReduced (K := K) S).injective
    rw [logHyperplaneEquivReduced_fullLog, hx, map_zero]

open scoped Classical in
/-- The coordinate equivalence as a continuous linear equivalence
(both spaces are finite-dimensional). -/
noncomputable def logHyperplaneContinuousEquivReduced :
    LogHyperplane (K := K) S ≃L[ℝ]
      ReducedLogSpace (K := K) S :=
  (logHyperplaneEquivReduced (K := K) S).toContinuousLinearEquiv

open scoped Classical in
/-- The complete lattice in the coordinate-sum-zero hyperplane. -/
noncomputable def fullLogLattice :
    Submodule ℤ (LogHyperplane (K := K) S) :=
  ZLattice.comap ℝ
    (reducedLogLattice (K := K) S)
    (logHyperplaneContinuousEquivReduced
      (K := K) S).toLinearMap

open scoped Classical in
/-- The complete lattice just defined is exactly the image of the
normalized all-place logarithmic map. -/
theorem fullLogLattice_eq_range :
    fullLogLattice (K := K) S =
      LinearMap.range
        (fullLog (K := K) S).toIntLinearMap := by
  ext z
  constructor
  · intro hz
    change
      logHyperplaneEquivReduced (K := K) S z ∈
        reducedLogLattice (K := K) S at hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    apply (logHyperplaneEquivReduced (K := K) S).injective
    change
      logHyperplaneEquivReduced (K := K) S
          (fullLog (K := K) S x) =
        logHyperplaneEquivReduced (K := K) S z
    rw [logHyperplaneEquivReduced_fullLog]
    exact hx
  · rintro ⟨x, rfl⟩
    change
      logHyperplaneEquivReduced (K := K) S
          (fullLog (K := K) S x) ∈
        reducedLogLattice (K := K) S
    rw [logHyperplaneEquivReduced_fullLog]
    exact LinearMap.mem_range_self _ x

open scoped Classical in
instance instDiscreteTopology_fullLogLattice :
    DiscreteTopology (fullLogLattice (K := K) S) :=
  by
    change
      DiscreteTopology
        (ZLattice.comap ℝ
          (reducedLogLattice (K := K) S)
          (logHyperplaneContinuousEquivReduced
            (K := K) S).toLinearMap)
    infer_instance

open scoped Classical in
/-- The image of the normalized all-place logarithmic embedding is a
complete `ℤ`-lattice in the coordinate-sum-zero hyperplane. -/
instance instIsZLattice_fullLogLattice :
    IsZLattice ℝ (fullLogLattice (K := K) S) :=
  by
    change
      IsZLattice ℝ
        (ZLattice.comap ℝ
          (reducedLogLattice (K := K) S)
          (logHyperplaneContinuousEquivReduced
            (K := K) S).toLinearMap)
    infer_instance

end FullLogarithmicSpace

section Decomposition

open scoped Classical in
/-- The logarithmic rank: the number of places in the
`S`-unit theorem minus one. -/
def logRank : ℕ :=
  Fintype.card (NumberField.InfinitePlace K) + S.card - 1

open scoped Classical in
/-- The additive realization of the roots of unity of `K`. -/
abbrev RootsOfUnityAdditive :=
  (NumberField.Units.torsion K).toAddSubgroup.toIntSubmodule

open scoped Classical in
/-- The additive torsion submodule of the `S`-unit group. -/
abbrev TorsionAdditive :=
  Submodule.torsion ℤ
    (Additive (SUnitGroup (K := K) S))

open scoped Classical in
theorem torsionAdditive_eq :
    TorsionAdditive (K := K) S =
      (AddCommGroup.torsion
        (Additive
          (SUnitGroup (K := K) S))).toIntSubmodule := by
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.torsion_int,
    AddSubgroup.toIntSubmodule_toAddSubgroup]

open scoped Classical in
/-- The torsion-free quotient of the additive `S`-unit group. -/
abbrev FreeQuotient :=
  Additive (SUnitGroup (K := K) S) ⧸
    TorsionAdditive (K := K) S

open scoped Classical in
local instance instModuleFinite_additiveSUnit :
    Module.Finite ℤ (Additive (SUnitGroup (K := K) S)) :=
  moduleFinite (K := K) S

attribute [local instance] instModuleFinite_additiveSUnit

open scoped Classical in
/-- The quotient of the additive S-unit group by torsion carries its induced integer module
structure. -/
local instance instModuleFreeQuotient :
    Module ℤ (FreeQuotient (K := K) S) :=
  Submodule.Quotient.module
    (TorsionAdditive (K := K) S)

attribute [local instance] instModuleFreeQuotient

open scoped Classical in
local instance instModuleFinite_freeQuotient :
    Module.Finite ℤ (FreeQuotient (K := K) S) :=
  Module.Finite.quotient ℤ
    (TorsionAdditive (K := K) S)

attribute [local instance] instModuleFinite_freeQuotient

open scoped Classical in
local instance instModuleFree_freeQuotient :
    Module.Free ℤ (FreeQuotient (K := K) S) :=
  Module.free_of_finite_type_torsion_free'

attribute [local instance] instModuleFree_freeQuotient

open scoped Classical in
/-- The free quotient has rank `#S - 1`, where `S` here includes all
infinite places. -/
theorem finrank_freeQuotient :
    Module.finrank ℤ (FreeQuotient (K := K) S) =
      logRank (K := K) S := by
  calc
    Module.finrank ℤ (FreeQuotient (K := K) S) =
        Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) := by
      exact finrank_quotient_eq_of_le_torsion le_rfl
    _ = NumberField.Units.rank K + S.card :=
      finrank (K := K) S
    _ = logRank (K := K) S := by
      rw [NumberField.Units.rank]
      dsimp [logRank]
      have hpos :
          0 <
            Fintype.card
              (NumberField.InfinitePlace K) :=
        Fintype.card_pos
      omega

open scoped Classical in
/-- A basis of the free quotient, indexed by its logarithmic rank. -/
noncomputable def basisFreeQuotient :
    Basis (Fin (logRank (K := K) S)) ℤ
      (FreeQuotient (K := K) S) :=
  Basis.reindex
    (Module.Free.chooseBasis ℤ
      (FreeQuotient (K := K) S))
    (Fintype.equivOfCardEq <| by
      rw [← Module.finrank_eq_card_chooseBasisIndex,
        finrank_freeQuotient (K := K) S,
        Fintype.card_fin])

open scoped Classical in
/-- The ordinary roots of unity map linearly and bijectively onto the
torsion in the `S`-unit group. -/
noncomputable def rootsOfUnityEquivTorsion :
    RootsOfUnityAdditive (K := K) ≃ₗ[ℤ]
      TorsionAdditive (K := K) S := by
  let f :
      RootsOfUnityAdditive (K := K) →ₗ[ℤ]
        TorsionAdditive (K := K) S :=
    ((fromNumberFieldUnitsLinearMap (K := K) S).domRestrict
      (RootsOfUnityAdditive (K := K))).codRestrict
        (TorsionAdditive (K := K) S) fun u => by
          rw [torsionAdditive_eq (K := K) S]
          change
            Additive.toMul
                (fromNumberFieldUnitsLinearMap (K := K) S
                  (u :
                    Additive (𝓞 K)ˣ)) ∈
              CommGroup.torsion
                (SUnitGroup (K := K) S)
          rw [torsion_eq_rootsOfUnity_range (K := K) S]
          refine
            ⟨Additive.toMul
                (u : Additive (𝓞 K)ˣ), ?_, rfl⟩
          exact u.property
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply fromNumberFieldUnitsLinearMap_injective
      (K := K) S
    exact congrArg Subtype.val hxy
  · intro y
    have hyadd :
        (y :
          Additive (SUnitGroup (K := K) S)) ∈
          AddCommGroup.torsion
            (Additive (SUnitGroup (K := K) S)) := by
      have hy' :
          (y :
            Additive (SUnitGroup (K := K) S)) ∈
            (AddCommGroup.torsion
              (Additive
                (SUnitGroup (K := K) S))).toIntSubmodule := by
        rw [← torsionAdditive_eq (K := K) S]
        exact y.property
      exact hy'
    have hy :
        Additive.toMul
            (y :
              Additive (SUnitGroup (K := K) S)) ∈
          CommGroup.torsion
            (SUnitGroup (K := K) S) :=
      hyadd
    rw [torsion_eq_rootsOfUnity_range (K := K) S] at hy
    obtain ⟨u, hu, huy⟩ := hy
    let x : RootsOfUnityAdditive (K := K) :=
      ⟨Additive.ofMul u, hu⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    exact huy

open scoped Classical in
/-- A linear section of the quotient by torsion.  It exists because
the quotient is a free, hence projective, `ℤ`-module. -/
private noncomputable def torsionQuotientSection :
    FreeQuotient (K := K) S →ₗ[ℤ]
      Additive (SUnitGroup (K := K) S) :=
  (Module.projective_lifting_property
    (TorsionAdditive (K := K) S).mkQ
    LinearMap.id
    (TorsionAdditive (K := K) S).mkQ_surjective).choose

open scoped Classical in
private theorem torsionQuotientSection_spec :
    (TorsionAdditive (K := K) S).mkQ.comp
        (torsionQuotientSection (K := K) S) =
      LinearMap.id :=
  (Module.projective_lifting_property
    (TorsionAdditive (K := K) S).mkQ
    LinearMap.id
    (TorsionAdditive (K := K) S).mkQ_surjective).choose_spec

open scoped Classical in
/-- Splitting the exact sequence consisting of torsion, the `S`-unit
group, and its torsion-free quotient. -/
private noncomputable def torsionProdFreeQuotientEquiv :
    Additive (SUnitGroup (K := K) S) ≃ₗ[ℤ]
      TorsionAdditive (K := K) S ×
        FreeQuotient (K := K) S :=
  (lequivProdOfRightSplitExact
    (TorsionAdditive (K := K) S).injective_subtype
    (by
      rw [Submodule.range_subtype, Submodule.ker_mkQ])
    (torsionQuotientSection_spec (K := K) S)).symm

open scoped Classical in
/-- **`S`-unit theorem, decomposition form.**  Additively, the
`S`-unit group is the product of the roots of unity and a free
`ℤ`-module of rank `#S - 1`. -/
noncomputable def decompositionLinearEquiv :
    Additive (SUnitGroup (K := K) S) ≃ₗ[ℤ]
      RootsOfUnityAdditive (K := K) ×
        (Fin (logRank (K := K) S) →₀ ℤ) :=
  (torsionProdFreeQuotientEquiv (K := K) S).trans
    ((rootsOfUnityEquivTorsion (K := K) S).symm.prodCongr
      (basisFreeQuotient (K := K) S).repr)

open scoped Classical in
/-- The multiplicative realization of the additive roots-of-unity
submodule is canonically the usual group `μ(K)`. -/
noncomputable def multiplicativeRootsOfUnityEquiv :
    Multiplicative (RootsOfUnityAdditive (K := K)) ≃*
      NumberField.Units.torsion K where
  toFun x :=
    ⟨Additive.toMul
      ((Multiplicative.toAdd x :
        RootsOfUnityAdditive (K := K)) :
        Additive (𝓞 K)ˣ),
      (Multiplicative.toAdd x :
        RootsOfUnityAdditive (K := K)).property⟩
  invFun u :=
    Multiplicative.ofAdd
      (⟨Additive.ofMul (u : (𝓞 K)ˣ), u.property⟩ :
        RootsOfUnityAdditive (K := K))
  left_inv x := by
    rfl
  right_inv u := by
    rfl
  map_mul' x y := by
    rfl

open scoped Classical in
/-- **`S`-unit theorem, group form.**

Writing `S` for all infinite places together with the supplied finite
places, the `S`-unit group is `μ(K) × ℤ^(#S-1)`. -/
noncomputable def decomposition :
    SUnitGroup (K := K) S ≃*
      NumberField.Units.torsion K ×
        Multiplicative
          (Fin (logRank (K := K) S) →₀ ℤ) :=
  (AddEquiv.toMultiplicativeRight
      (decompositionLinearEquiv
        (K := K) S).toAddEquiv).trans
    (((MulEquiv.prodMultiplicative
        (RootsOfUnityAdditive (K := K))
        (Fin (logRank (K := K) S) →₀ ℤ)) :
        Multiplicative
            (RootsOfUnityAdditive (K := K) ×
              (Fin (logRank (K := K) S) →₀ ℤ)) ≃*
          Multiplicative (RootsOfUnityAdditive (K := K)) ×
            Multiplicative
              (Fin (logRank (K := K) S) →₀ ℤ)).trans
      ((multiplicativeRootsOfUnityEquiv
        (K := K)).prodCongr
          (MulEquiv.refl
            (Multiplicative
              (Fin (logRank (K := K) S) →₀ ℤ)))))

end Decomposition

end SUnitGroup
