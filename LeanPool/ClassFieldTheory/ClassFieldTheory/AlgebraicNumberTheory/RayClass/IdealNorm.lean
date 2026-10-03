/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
/-!
# Norms of ideals prime to a modulus

For a finite extension `L / K`, the norm of a prime of `L`
above `v` is `v` raised to the inertia degree.  Extending this rule
multiplicatively gives the genuine norm on nonzero fractional ideals.

If `m` is a modulus of `K`, a modulus upstairs is chosen deeply enough
at every prime above `m` that local norms preserve the prescribed
higher-unit conditions.  The norm therefore restricts to the groups of
fractional ideals prime to these moduli.  Its image, together with the
principal ray ideals, is the norm-defined ideal group
`N_{L/K} J_L^m P_K^m`.
-/

@[expose] public section

open scoped BigOperators NumberField Topology
open NumberField IsDedekindDomain

noncomputable
section

namespace RayClass

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [FiniteDimensional K L] in
open scoped Classical in
/-- At a prime `W` above `v`, a sufficiently deep higher-unit group
has norm contained in the higher-unit group prescribed by `m` at `v`.
This is the source of the lifted modulus used for ideal norms. -/
theorem exists_localHigherUnitGroup_le_norm_preimage
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    let v := _root_.finitePlaceBelow (K := K) W
    letI : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
      (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
    ∃ n : ℕ,
      localHigherUnitGroup W n ≤
        (localHigherUnitGroup v (m.finitePart v)).comap
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L)) := by
  classical
  let v := _root_.finitePlaceBelow (K := K) W
  let : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
    (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
  let : IsScalarTower
      K (v.adicCompletion K) (W.adicCompletion L) :=
    _root_.finitePlaceAdicCompletionMap_isScalarTower K L v ⟨W, rfl⟩
  let : ContinuousSMul
      (v.adicCompletion K) (W.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (by
      change Continuous
        (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩)
      exact
        _root_.finitePlaceAdicCompletionMap_continuous
          K L v ⟨W, rfl⟩)
  let : FiniteDimensional
      (v.adicCompletion K) (W.adicCompletion L) :=
    inferInstance
  let : NontriviallyNormedField (v.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne (by
      obtain ⟨ϖ, hϖ⟩ :=
        IsDiscreteValuationRing.exists_irreducible
          (v.adicCompletionIntegers K)
      refine ⟨(ϖ : v.adicCompletion K), ?_, ?_⟩
      · intro h
        exact hϖ.ne_zero (Subtype.ext h)
      · exact ne_of_lt (local_irreducible_norm_lt_one v hϖ))
  let U : Set (W.adicCompletion L)ˣ :=
    (LocalFieldTheory.normUnits
      (v.adicCompletion K) (W.adicCompletion L)) ⁻¹'
        (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ)
  have hTarget :
      (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ) ∈
        𝓝 (1 : (v.adicCompletion K)ˣ) :=
    (isOpen_localHigherUnitGroup v (m.finitePart v)).mem_nhds
      (localHigherUnitGroup v (m.finitePart v)).one_mem
  have hU : U ∈ 𝓝 (1 : (W.adicCompletion L)ˣ) := by
    have hcont :=
      LocalFieldTheory.normUnits_continuous_of_finiteDimensional
        (v.adicCompletion K) (W.adicCompletion L)
    have hTarget' :
        (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ) ∈
          𝓝 (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L) 1) := by
      simpa using hTarget
    simpa [U] using hcont.continuousAt hTarget'
  obtain ⟨n, hn⟩ :=
    exists_localHigherUnitGroup_subset W hU
  refine ⟨n, ?_⟩
  intro x hx
  exact hn hx

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The positive local depth used at `W` in the lifted modulus.  It is
zero precisely away from the inverse image of the support of `m`. -/
noncomputable def idealNormLiftedModulusExponent
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) : ℕ :=
  if _ :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support then
    Nat.find
        (exists_localHigherUnitGroup_le_norm_preimage
          (K := K) (L := L) m W) + 1
  else
    0

omit [FiniteDimensional K L] in
open scoped Classical in
theorem idealNormLiftedModulusExponent_pos
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support) :
    0 < idealNormLiftedModulusExponent
      (K := K) (L := L) m W := by
  rw [idealNormLiftedModulusExponent, dite_eq_left hW]
  exact Nat.zero_lt_succ _

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The chosen positive depth still has the required local norm
property. -/
theorem localHigherUnitGroup_idealNormLiftedModulusExponent_le
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support) :
    let v := _root_.finitePlaceBelow (K := K) W
    letI : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
      (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
    localHigherUnitGroup W
        (idealNormLiftedModulusExponent
          (K := K) (L := L) m W) ≤
      (localHigherUnitGroup v (m.finitePart v)).comap
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion L)) := by
  classical
  let v := _root_.finitePlaceBelow (K := K) W
  let : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
    (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
  rw [idealNormLiftedModulusExponent, dite_eq_left hW]
  exact
    (localHigherUnitGroup_antitone W (Nat.le_succ _)).trans
      (Nat.find_spec
        (exists_localHigherUnitGroup_le_norm_preimage
          (K := K) (L := L) m W))

omit [FiniteDimensional K L] in
open scoped Classical in
/-- At a prime above the support, the selected positive depth is at most the
successor of every depth having the required local norm property. -/
theorem idealNormLiftedModulusExponent_min
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support)
    (r : ℕ)
    (hr :
      let v := _root_.finitePlaceBelow (K := K) W
      letI : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
        (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
      localHigherUnitGroup W r ≤
        (localHigherUnitGroup v (m.finitePart v)).comap
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L))) :
    idealNormLiftedModulusExponent (K := K) (L := L) m W ≤ r + 1 := by
  classical
  let v := _root_.finitePlaceBelow (K := K) W
  let : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
    (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
  rw [idealNormLiftedModulusExponent, dite_eq_left hW]
  exact Nat.add_le_add_right
    (Nat.find_min'
      (exists_localHigherUnitGroup_le_norm_preimage
        (K := K) (L := L) m W) hr) 1

omit [FiniteDimensional K L] in
open scoped Classical in
/-- Away from the pulled-back support, the lifted exponent is zero. -/
@[simp]
theorem idealNormLiftedModulusExponent_eq_zero_of_not_mem
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∉ m.finitePart.support) :
    idealNormLiftedModulusExponent (K := K) (L := L) m W = 0 := by
  rw [idealNormLiftedModulusExponent, dite_eq_right hW]

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The finite set of primes upstairs lying over the support of `m`. -/
def idealNormLiftedSupport (m : Modulus K) :
    Set (HeightOneSpectrum (𝓞 L)) :=
  {W |
    _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support}

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The inverse image of the finite support of a modulus is finite. -/
theorem idealNormLiftedSupport_finite (m : Modulus K) :
    (idealNormLiftedSupport (K := K) (L := L) m).Finite := by
  exact
    _root_.Set.Finite.preimage_finitePlaceBelow
      (K := K) (L := L) m.finitePart.support.finite_toSet

open scoped Classical in
/-- A modulus upstairs whose local higher-unit conditions are carried
by the field norm into the conditions of `m`. -/
noncomputable def idealNormLiftedModulus
    (m : Modulus K) : Modulus L :=
  Modulus.ofFinite <|
    Finsupp.onFinset
      (idealNormLiftedSupport_finite
        (K := K) (L := L) m).toFinset
      (idealNormLiftedModulusExponent
        (K := K) (L := L) m)
      (by
        intro W hW
        rw [Set.Finite.mem_toFinset]
        by_contra hbelow
        apply hW
        rw [idealNormLiftedModulusExponent, dite_eq_right]
        exact hbelow)

omit [FiniteDimensional K L] in
open scoped Classical in
@[simp]
theorem idealNormLiftedModulus_apply
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    (idealNormLiftedModulus (K := K) (L := L) m).finitePart W =
      idealNormLiftedModulusExponent
        (K := K) (L := L) m W :=
  rfl

omit [FiniteDimensional K L] in
open scoped Classical in
theorem mem_idealNormLiftedModulus_support_iff
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    W ∈ (idealNormLiftedModulus
        (K := K) (L := L) m).finitePart.support ↔
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support := by
  rw [Finsupp.mem_support_iff, idealNormLiftedModulus_apply]
  by_cases hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support
  · rw [idealNormLiftedModulusExponent, dite_eq_left hW]
    exact ⟨fun _ => hW, fun _ => Nat.succ_ne_zero _⟩
  · simp [idealNormLiftedModulusExponent, hW]

open scoped Classical in
/-- Pushforward of the prime-exponent vector under ideal norm.  A
prime `W` contributes its exponent multiplied by the inertia degree
to the prime below it. -/
noncomputable def idealNormExponentMap :
    (HeightOneSpectrum (𝓞 L) →₀ ℤ) →+
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  Finsupp.liftAddHom fun W =>
    (Finsupp.singleAddHom
      (_root_.finitePlaceBelow (K := K) W)).comp
        (AddMonoidHom.mulLeft
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ))

omit [FiniteDimensional K L] in
open scoped Classical in
@[simp]
theorem idealNormExponentMap_apply
    (e : HeightOneSpectrum (𝓞 L) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 K)) :
    idealNormExponentMap (K := K) (L := L) e v =
      e.sum fun W n =>
        if _root_.finitePlaceBelow (K := K) W = v then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n
        else
          0 := by
  classical
  simp [idealNormExponentMap, Finsupp.single_apply, eq_comm]

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The exponent pushforward can equivalently be written as the finite
sum over the primes above one fixed base prime. -/
theorem idealNormExponentMap_apply_eq_sum_above
    (e : HeightOneSpectrum (𝓞 L) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v}] :
    idealNormExponentMap (K := K) (L := L) e v =
      ∑ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W.1 := by
  classical
  let p : HeightOneSpectrum (𝓞 L) → Prop :=
    fun W => _root_.finitePlaceBelow (K := K) W = v
  let eAbove : {W : HeightOneSpectrum (𝓞 L) // p W} →₀ ℤ :=
    e.subtypeDomain p
  rw [idealNormExponentMap_apply]
  calc
    e.sum
          (fun W n =>
            if _root_.finitePlaceBelow (K := K) W = v then
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n
            else 0) =
    eAbove.sum
          (fun W n =>
            (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n) := by
      simp only [eAbove, p, Finsupp.sum, Finsupp.support_subtypeDomain,
        Finsupp.subtypeDomain_apply]
      calc
        (∑ W ∈ e.support,
            if _root_.finitePlaceBelow (K := K) W = v then
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W
            else 0) =
            ∑ W ∈ e.support.filter
              (fun W => _root_.finitePlaceBelow (K := K) W = v),
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W :=
          (Finset.sum_filter _ _).symm
        _ =
            ∑ W ∈ Finset.subtype
              (fun W => _root_.finitePlaceBelow (K := K) W = v)
              e.support,
              (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W.1 :=
          (Finset.sum_subtype_eq_sum_filter
            (fun W => (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W)).symm
    _ =
        ∑ W : {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := K) W = v},
          (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W.1 := by
      rw [Finsupp.sum_fintype]
      · rfl
      · intro W
        simp

open scoped Classical in
private theorem factorizationEquiv_symm_toAdd
    (I : FractionalIdealGroup L) :
    ((FractionalIdealGroup.factorizationEquiv
      (K := L)).symm I).toAdd =
        FractionalIdealGroup.countVector I := by
  ext W
  have h := FractionalIdealGroup.count_factorization
    ((FractionalIdealGroup.factorizationEquiv
      (K := L)).symm I) W
  have hfac :=
    (FractionalIdealGroup.factorizationEquiv
      (K := L)).apply_symm_apply I
  change
    FractionalIdealGroup.factorization
      ((FractionalIdealGroup.factorizationEquiv
        (K := L)).symm I) = I at hfac
  rw [hfac] at h
  exact h.symm.trans (FractionalIdealGroup.countVector_apply I W).symm

open scoped Classical in
/-- The genuine relative norm on nonzero fractional ideals. -/
noncomputable def fractionalIdealNorm :
    FractionalIdealGroup L →* FractionalIdealGroup K :=
  (FractionalIdealGroup.factorizationEquiv
      (K := K)).toMonoidHom.comp
    ((idealNormExponentMap
        (K := K) (L := L)).toMultiplicative.comp
      (FractionalIdealGroup.factorizationEquiv
        (K := L)).symm.toMonoidHom)

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The exponent of the norm at `v` is the inertia-degree weighted
pushforward of the upstairs prime exponents. -/
theorem count_fractionalIdealNorm
    (I : FractionalIdealGroup L)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (fractionalIdealNorm (K := K) (L := L) I :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      idealNormExponentMap (K := K) (L := L)
        (FractionalIdealGroup.countVector I) v := by
  change
    FractionalIdeal.count K v
        ((FractionalIdealGroup.factorization
          ((idealNormExponentMap
            (K := K) (L := L)).toMultiplicative
            ((FractionalIdealGroup.factorizationEquiv
              (K := L)).symm I)) : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      _
  rw [FractionalIdealGroup.count_factorization]
  change
    idealNormExponentMap (K := K) (L := L)
        ((FractionalIdealGroup.factorizationEquiv
          (K := L)).symm I).toAdd v =
      _
  rw [factorizationEquiv_symm_toAdd]

omit [FiniteDimensional K L] in
open scoped Classical in
private theorem fractionalIdealNormPrimeBelow_eq_finitePlaceBelow
    (W : HeightOneSpectrum (𝓞 L)) :
    ClassFieldTheory.fractionalIdealNormPrimeBelow K L W =
      _root_.finitePlaceBelow (K := K) W := by
  ext
  rfl

omit [FiniteDimensional K L] in
open scoped Classical in
private theorem idealNormExponentMap_eq_public :
    idealNormExponentMap (K := K) (L := L) =
      ClassFieldTheory.fractionalIdealNormExponentMap K L := by
  unfold idealNormExponentMap ClassFieldTheory.fractionalIdealNormExponentMap
  simp only [fractionalIdealNormPrimeBelow_eq_finitePlaceBelow]

open scoped Classical in
private theorem factorizationEquiv_eq_public
    (F : Type) [Field F] [NumberField F] :
    FractionalIdealGroup.factorizationEquiv (K := F) =
      ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := F) := by
  apply MulEquiv.ext
  intro exps
  apply FractionalIdealGroup.ext_count
  intro v
  change FractionalIdeal.count F v
      ((FractionalIdealGroup.factorization exps : FractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
    FractionalIdeal.count F v
      ((ClassFieldTheory.NumberFieldFractionalIdealGroup.factorization exps :
        FractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  rw [FractionalIdealGroup.count_factorization,
    ClassFieldTheory.NumberFieldFractionalIdealGroup.count_factorization]

open scoped Classical in
/-- The Mathlib-level public fractional-ideal norm agrees with the norm used
by the idelic and ray-class constructions. -/
theorem fractionalIdealNorm_eq_public :
    fractionalIdealNorm (K := K) (L := L) =
      ClassFieldTheory.fractionalIdealNorm K L := by
  unfold fractionalIdealNorm ClassFieldTheory.fractionalIdealNorm
  rw [factorizationEquiv_eq_public K,
    factorizationEquiv_eq_public L,
    idealNormExponentMap_eq_public]

open scoped Classical in
/-- The exponent of the fractional ideal attached to an idèle is its
finite local order. -/
@[simp]
theorem _root_.IdeleGroup.count_fractionalIdeal
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (IdeleGroup.fractionalIdeal a :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (FiniteIdeleGroup.localOrder v
        (IdeleGroup.finiteComponent v a)).toAdd := by
  change
    FractionalIdeal.count K v
        (((FractionalIdealGroup.factorization (K := K))
          (FiniteIdeleGroup.valuationVector a.2) :
            FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      _
  rw [FractionalIdealGroup.count_factorization]
  rfl

open scoped Classical in
/-- The genuine ideal norm is the fractional-ideal image of the
ordinary idèle norm. -/
theorem _root_.IdeleGroup.fractionalIdeal_ideleNorm
    (a : IdeleGroup L) :
    IdeleGroup.fractionalIdeal (IdeleGroup.norm K L a) =
      fractionalIdealNorm (K := K) (L := L)
        (IdeleGroup.fractionalIdeal a) := by
  classical
  apply FractionalIdealGroup.ext_count
  intro v
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    adicAbv_isNontrivial v
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v
  let :=
    AlgebraicNumberTheory.Valuations.completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv
      (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v},
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (_root_.finitePlaceAdicCompletionMap K L v W).toAlgebra
  rw [IdeleGroup.count_fractionalIdeal,
    count_fractionalIdealNorm]
  rw [IdeleGroup.finiteComponent_norm_eq_prod]
  rw [map_prod, toAdd_prod]
  change
    (∑ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v},
      (FiniteIdeleGroup.localOrder v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (IdeleGroup.finiteComponent W.1 a))).toAdd) =
      _
  rw [idealNormExponentMap_apply_eq_sum_above]
  apply Finset.sum_congr rfl
  intro W _hW
  rw [FiniteIdeleGroup.localOrder_normUnits K L v W]
  rw [FractionalIdealGroup.countVector_apply,
    IdeleGroup.count_fractionalIdeal]

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The fractional ideal norm preserves coprimality with a modulus
after passing to the lifted modulus upstairs. -/
theorem fractionalIdealNorm_mem_primeToModulusIdeals
    (m : Modulus K)
    (I : primeToModulusIdeals
      (idealNormLiftedModulus (K := K) (L := L) m)) :
    fractionalIdealNorm (K := K) (L := L)
        (I : FractionalIdealGroup L) ∈
      primeToModulusIdeals m := by
  intro v hv
  rw [count_fractionalIdealNorm,
    idealNormExponentMap_apply]
  classical
  simp only [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro W hW
  by_cases hbelow :
      _root_.finitePlaceBelow (K := K) W = v
  · rw [ite_eq_left hbelow]
    have hLifted :
        W ∈ (idealNormLiftedModulus
          (K := K) (L := L) m).finitePart.support := by
      rw [mem_idealNormLiftedModulus_support_iff, hbelow]
      exact hv
    rw [FractionalIdealGroup.countVector_apply, I.property W hLifted]
    simp
  · rw [ite_eq_right hbelow]

open scoped Classical in
/-- The ideal norm restricted to fractional ideals prime to the
corresponding moduli. -/
noncomputable def primeToModulusIdealNorm
    (m : Modulus K) :
    primeToModulusIdeals
        (idealNormLiftedModulus (K := K) (L := L) m) →*
      primeToModulusIdeals m where
  toFun I :=
    ⟨fractionalIdealNorm (K := K) (L := L)
        (I : FractionalIdealGroup L),
      fractionalIdealNorm_mem_primeToModulusIdeals
        (K := K) (L := L) m I⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' I J := by
    apply Subtype.ext
    exact map_mul _ _ _

omit [FiniteDimensional K L] in
open scoped Classical in
@[simp]
theorem primeToModulusIdealNorm_coe
    (m : Modulus K)
    (I : primeToModulusIdeals
      (idealNormLiftedModulus (K := K) (L := L) m)) :
    (primeToModulusIdealNorm
        (K := K) (L := L) m I :
      FractionalIdealGroup K) =
        fractionalIdealNorm (K := K) (L := L)
          (I : FractionalIdealGroup L) :=
  rfl

open scoped Classical in
/-- The finite component of an idèle prime to the lifted modulus has
norm satisfying the finite prime-to conditions of the base modulus. -/
theorem finite_norm_mem_finitePrimeToModulusSubgroup
    (m : Modulus K)
    (a : idelePrimeToModulusSubgroup
      (idealNormLiftedModulus (K := K) (L := L) m)) :
    (IdeleGroup.norm K L (a : IdeleGroup L)).2 ∈
      finitePrimeToModulusSubgroup m := by
  classical
  intro v hv
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    adicAbv_isNontrivial v
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v
  let :=
    AlgebraicNumberTheory.Valuations.completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv
      (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v},
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (_root_.finitePlaceAdicCompletionMap K L v W).toAlgebra
  change IdeleGroup.finiteComponent v
      (IdeleGroup.norm K L (a : IdeleGroup L)) ∈
        localHigherUnitGroup v (m.finitePart v)
  rw [IdeleGroup.finiteComponent_norm_eq_prod]
  apply Subgroup.prod_mem
  rintro ⟨W, rfl⟩ _
  have hnorm :=
    localHigherUnitGroup_idealNormLiftedModulusExponent_le
      (K := K) (L := L) m W hv
  have hmem := hnorm
    (a.property.2 W
      ((mem_idealNormLiftedModulus_support_iff
        (K := K) (L := L) m W).2 hv))
  let : Algebra
      ((_root_.finitePlaceBelow (K := K) W).adicCompletion K)
      (W.adicCompletion L) :=
    (_root_.finitePlaceAdicCompletionMap K L
      (_root_.finitePlaceBelow (K := K) W) ⟨W, rfl⟩).toAlgebra
  change
    LocalFieldTheory.normUnits
      ((_root_.finitePlaceBelow (K := K) W).adicCompletion K)
      (W.adicCompletion L)
      (IdeleGroup.finiteComponent W (a : IdeleGroup L)) ∈
        localHigherUnitGroup
          (_root_.finitePlaceBelow (K := K) W)
          (m.finitePart (_root_.finitePlaceBelow (K := K) W)) at hmem
  exact hmem

open scoped Classical in
/-- The genuine norm-defined subgroup
`N_{L/K} J_L^m P_K^m` of ideals prime to `m`. -/
noncomputable def idealNormSubgroup
    (m : Modulus K) :
    Subgroup (primeToModulusIdeals m) :=
  (primeToModulusIdealNorm
    (K := K) (L := L) m).range ⊔
      principalRayIdealSubgroup m

end RayClass
