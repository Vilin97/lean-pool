/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Instances.Sign
/-!
# The congruence topology on the idele class group

The local higher-unit groups are open,
the ray congruence subgroups are open (and hence closed) of finite index, and
the congruence subgroups are cofinal among the closed finite-index subgroups
of the idele class group.
-/

@[expose] public section

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain
open Topology

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

open scoped Classical in
/-- The integral representative of a unit in a finite completion. -/
def localIntegralValue
    (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletionIntegers K).units) :
    v.adicCompletionIntegers K :=
  ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y :
    (v.adicCompletionIntegers K)ˣ).1

open scoped Classical in
/-- A local integral unit maps to one modulo the `n`-th maximal-ideal
power exactly when its difference from one belongs to that power. -/
theorem localHigherUnitMap_eq_one_iff
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (y : (v.adicCompletionIntegers K).units) :
    localHigherUnitMap v n y = 1 ↔
      localIntegralValue v y - 1 ∈
          (IsLocalRing.maximalIdeal
            (v.adicCompletionIntegers K)) ^ n := by
  let I :=
    (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ n
  change
    Units.map (Ideal.Quotient.mk I).toMonoidHom
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) =
      1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk I (localIntegralValue v y) =
      Ideal.Quotient.mk I 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := I) (localIntegralValue v y)
      (1 : v.adicCompletionIntegers K)

open scoped Classical in
/-- Local higher-unit groups are contravariant in their depth. -/
theorem localHigherUnitGroup_antitone
    (v : HeightOneSpectrum (𝓞 K))
    {m n : ℕ} (hmn : m ≤ n) :
    localHigherUnitGroup v n ≤ localHigherUnitGroup v m := by
  intro x hx
  rw [mem_localHigherUnitGroup_iff] at hx ⊢
  obtain ⟨y, rfl, hy⟩ := hx
  refine ⟨y, rfl, ?_⟩
  rw [localHigherUnitMap_eq_one_iff] at hy ⊢
  exact Ideal.pow_le_pow_right hmn hy

open scoped Classical in
/-- Every local higher-unit group is open in the multiplicative group of the
finite completion. -/
theorem isOpen_localHigherUnitGroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsOpen
      ((localHigherUnitGroup v n :
        Subgroup (v.adicCompletion K)ˣ) :
          Set (v.adicCompletion K)ˣ) := by
  let D : Subgroup (v.adicCompletion K)ˣ :=
    (v.adicCompletionIntegers K).units
  let I : Ideal (v.adicCompletionIntegers K) :=
    (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ n
  let toInteger : D → v.adicCompletionIntegers K :=
    fun y ↦ localIntegralValue v y
  have htoInteger : Continuous toInteger := by
    apply continuous_induced_rng.mpr
    exact Units.continuous_val.comp continuous_subtype_val
  let W : Set D := {y | toInteger y - 1 ∈ I}
  have : CompactSpace (v.adicCompletionIntegers K) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  have hIOpen : IsOpen (I : Set (v.adicCompletionIntegers K)) := by
    exact IsLocalRing.isOpen_maximalIdeal_pow
      (v.adicCompletionIntegers K) n
  have hWOpen : IsOpen W := by
    exact hIOpen.preimage (htoInteger.sub continuous_const)
  have hDOpen : IsOpen (D : Set (v.adicCompletion K)ˣ) := by
    exact isOpen_finiteLocalUnits K v
  have himageOpen :
      IsOpen (Subtype.val '' W : Set (v.adicCompletion K)ˣ) :=
    hDOpen.isOpenEmbedding_subtypeVal.isOpenMap W hWOpen
  have heq :
      (localHigherUnitGroup v n :
          Set (v.adicCompletion K)ˣ) =
        Subtype.val '' W := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl, hy⟩ :=
        (mem_localHigherUnitGroup_iff v n x).1 hx
      refine ⟨y, ?_, rfl⟩
      exact (localHigherUnitMap_eq_one_iff v n y).1 hy
    · rintro ⟨y, hyW, rfl⟩
      let y' : (v.adicCompletionIntegers K).units := y
      apply (mem_localHigherUnitGroup_iff v n y).2
      refine ⟨y', rfl, ?_⟩
      exact (localHigherUnitMap_eq_one_iff v n y').2 hyW
  rw [heq]
  exact himageOpen

open scoped Classical in
/-- The local higher-unit group lies in the local integral-unit group. -/
theorem localHigherUnitGroup_le_finiteLocalUnits
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localHigherUnitGroup v n ≤
      (v.adicCompletionIntegers K).units := by
  intro x hx
  rw [mem_localHigherUnitGroup_iff] at hx
  obtain ⟨y, rfl, _⟩ := hx
  exact y.property

open scoped Classical in
/-- The finite idele congruence subgroup is open. -/
theorem isOpen_finiteCongruenceSubgroup (m : FiniteModulus K) :
    IsOpen
      ((finiteCongruenceSubgroup m :
        Subgroup (FiniteIdeleGroup K)) :
          Set (FiniteIdeleGroup K)) := by
  let T := m.support
  let U : Set (FiniteIdeleGroup K) :=
    (FiniteIdeleGroup.integralSubgroup (K := K) :
      Set (FiniteIdeleGroup K)) ∩
    ⋂ v ∈ T,
      (fun a : FiniteIdeleGroup K ↦ a v) ⁻¹'
        (localHigherUnitGroup v (m v) :
          Set (v.adicCompletion K)ˣ)
  have hIntegralOpen :
      IsOpen
        ((FiniteIdeleGroup.integralSubgroup (K := K) :
          Subgroup (FiniteIdeleGroup K)) :
            Set (FiniteIdeleGroup K)) := by
    change IsOpen {a : FiniteIdeleGroup K |
      ∀ v, a v ∈ (v.adicCompletionIntegers K).units}
    exact RestrictedProduct.isOpen_forall_mem
      (fun v ↦ isOpen_finiteLocalUnits K v)
  have hUOpen : IsOpen U := by
    apply hIntegralOpen.inter
    apply isOpen_biInter_finset
    intro v hv
    exact (isOpen_localHigherUnitGroup v (m v)).preimage
      (RestrictedProduct.continuous_eval v)
  have heq :
      (finiteCongruenceSubgroup m : Set (FiniteIdeleGroup K)) = U := by
    ext a
    constructor
    · intro ha
      have ha' :=
        (mem_finiteCongruenceSubgroup_iff m a).1 ha
      constructor
      · exact fun v ↦
          localHigherUnitGroup_le_finiteLocalUnits v (m v) (ha' v)
      · apply Set.mem_iInter.mpr
        intro v
        apply Set.mem_iInter.mpr
        intro _hv
        exact ha' v
    · rintro ⟨haIntegral, haT⟩
      apply (mem_finiteCongruenceSubgroup_iff m a).2
      intro v
      by_cases hv : v ∈ T
      · have h₁ := Set.mem_iInter.mp haT v
        exact Set.mem_iInter.mp h₁ hv
      · have hmv : m v = 0 := by
          by_contra hne
          exact hv (Finsupp.mem_support_iff.mpr hne)
        rw [hmv, localHigherUnitGroup_zero]
        exact haIntegral v
  rw [heq]
  exact hUOpen

omit [NumberField K] in
open scoped Classical in
/-- At a real place the positivity subgroup is open; at a complex place it
is the whole local multiplicative group. -/
theorem isOpen_infinitePositiveSubgroup (v : InfinitePlace K) :
    IsOpen
      ((infinitePositiveSubgroup v : Subgroup v.Completionˣ) :
        Set v.Completionˣ) := by
  by_cases hv : v.IsReal
  · rw [show
      (infinitePositiveSubgroup v : Set v.Completionˣ) =
        {x : v.Completionˣ |
          0 <
            InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hv (x : v.Completion)} by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          exact h hv
        · intro h hv'
          simpa only [Subsingleton.elim hv' hv] using h]
    exact isOpen_Ioi.preimage
      ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).continuous.comp
        Units.continuous_val)
  · have htop :
        infinitePositiveSubgroup v = ⊤ := by
      ext x
      simp [mem_infinitePositiveSubgroup_iff, hv]
    rw [htop]
    exact isOpen_univ

open scoped Classical in
/-- The positivity subgroup in the product of all infinite local groups is
open. -/
theorem isOpen_infinitePositivePiSubgroup :
    IsOpen
      ((Subgroup.pi Set.univ (fun v : InfinitePlace K ↦
          infinitePositiveSubgroup v) :
        Subgroup ((v : InfinitePlace K) → v.Completionˣ)) :
          Set ((v : InfinitePlace K) → v.Completionˣ)) := by
  change IsOpen
    (Set.univ.pi fun v : InfinitePlace K ↦
      (infinitePositiveSubgroup v : Set v.Completionˣ))
  exact isOpen_set_pi Set.finite_univ fun v _ ↦
    isOpen_infinitePositiveSubgroup v

open scoped Classical in
/-- The narrow archimedean congruence subgroup is open. -/
theorem isOpen_narrowInfiniteCongruenceSubgroup :
    IsOpen
      ((narrowInfiniteCongruenceSubgroup (K := K) :
        Subgroup (InfiniteIdeleGroup K)) :
          Set (InfiniteIdeleGroup K)) :=
  isOpen_infinitePositivePiSubgroup.preimage
    ContinuousMulEquiv.piUnits.continuous

open scoped Classical in
/-- The archimedean congruence subgroup selected by a full modulus is open. -/
theorem isOpen_infiniteCongruenceSubgroup (m : Modulus K) :
    IsOpen
      ((m.infiniteCongruenceSubgroup :
        Subgroup (InfiniteIdeleGroup K)) :
          Set (InfiniteIdeleGroup K)) := by
  let U : Set (InfiniteIdeleGroup K) :=
    ⋂ v ∈ m.infinitePart,
      (fun a : InfiniteIdeleGroup K ↦ ContinuousMulEquiv.piUnits a v.1) ⁻¹'
        (infinitePositiveSubgroup v.1 : Set v.1.Completionˣ)
  have hUOpen : IsOpen U := by
    apply isOpen_biInter_finset
    intro v hv
    have hEval : Continuous
        (fun a : InfiniteIdeleGroup K ↦ ContinuousMulEquiv.piUnits a v.1) :=
      (continuous_apply v.1).comp ContinuousMulEquiv.piUnits.continuous
    exact (isOpen_infinitePositiveSubgroup v.1).preimage hEval
  have hU :
      (m.infiniteCongruenceSubgroup : Set (InfiniteIdeleGroup K)) = U := by
    ext a
    change a ∈ m.infiniteCongruenceSubgroup ↔ a ∈ U
    rw [Modulus.mem_infiniteCongruenceSubgroup_iff]
    constructor
    · intro ha
      apply Set.mem_iInter.mpr
      intro v
      apply Set.mem_iInter.mpr
      intro hv
      exact ha v hv
    · intro ha v hv
      exact Set.mem_iInter.mp (Set.mem_iInter.mp ha v) hv
  rw [hU]
  exact hUOpen

open scoped Classical in
/-- The idele congruence subgroup `I_K^m` is open. -/
theorem isOpen_ideleCongruenceSubgroup (m : Modulus K) :
    IsOpen
      ((m.ideleCongruenceSubgroup :
        Subgroup (IdeleGroup K)) :
          Set (IdeleGroup K)) :=
  (isOpen_infiniteCongruenceSubgroup m).prod
    (isOpen_finiteCongruenceSubgroup m.finitePart)

open scoped Classical in
/-- Membership in the `n`-th local higher-unit group bounds the norm of
the difference from one by the `n`-th power of a uniformizer norm. -/
theorem localHigherUnit_norm_sub_one_le
    (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (n : ℕ) {x : (v.adicCompletion K)ˣ}
    (hx : x ∈ localHigherUnitGroup v n) :
    ‖(x : v.adicCompletion K) - 1‖ ≤ ‖ϖ‖ ^ n := by
  obtain ⟨y, rfl, hy⟩ :=
    (mem_localHigherUnitGroup_iff v n x).1 hx
  have hyIdeal :
      localIntegralValue v y - 1 ∈
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n :=
    (localHigherUnitMap_eq_one_iff v n y).1 hy
  have hIdealSet :=
    Valuation.Integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
        K v) hϖ n
  have hyVal :
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
          (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K) (localIntegralValue v y - 1)) ≤
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
            (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K) ϖ) ^ n := by
    exact (Set.ext_iff.mp hIdealSet
      (localIntegralValue v y - 1)).mp hyIdeal
  have hcoe :
      (((y : (v.adicCompletionIntegers K).units) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        ((localIntegralValue v y :
          v.adicCompletionIntegers K) : v.adicCompletion K) :=
    rfl
  rw [hcoe]
  change
    ‖((localIntegralValue v y :
        v.adicCompletionIntegers K) : v.adicCompletion K) - 1‖ ≤
      ‖((ϖ : v.adicCompletionIntegers K) :
        v.adicCompletion K)‖ ^ n
  rw [← norm_pow]
  apply Valued.toNormedField.norm_le_iff.mpr
  have hyVal' :
      @LE.le ℤᵐ⁰ WithZero.instPreorder.toLE
        ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
          (((localIntegralValue v y :
            v.adicCompletionIntegers K) :
              v.adicCompletion K) - 1))
        ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
          (((ϖ : v.adicCompletionIntegers K) :
            v.adicCompletion K) ^ n)) := by
    have hAlgebraMap :
        ∀ z : v.adicCompletionIntegers K,
          algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K) z =
            (z : v.adicCompletion K) :=
      fun _ ↦ rfl
    simpa [hAlgebraMap] using hyVal
  have withZeroPreorder_le :
      ∀ a b : ℤᵐ⁰,
        @LE.le ℤᵐ⁰ WithZero.instPreorder.toLE a b →
          a ≤ b := by
    intro a b hab
    cases a <;> cases b <;>
      simp_all
  exact withZeroPreorder_le _ _ hyVal'

open scoped Classical in
/-- An irreducible element of the valuation ring of a finite completion
has norm strictly less than one. -/
theorem local_irreducible_norm_lt_one
    (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    ‖ϖ‖ < 1 := by
  change
    ‖((ϖ : v.adicCompletionIntegers K) :
      v.adicCompletion K)‖ < 1
  apply Valued.toNormedField.norm_lt_one_iff.mpr
  simpa only using!
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      K v).valuation_irreducible_lt_one hϖ)

open scoped Classical in
/-- The higher-unit groups form a neighborhood basis of `1` in a finite
local multiplicative group. -/
theorem exists_localHigherUnitGroup_subset
    (v : HeightOneSpectrum (𝓞 K))
    {U : Set (v.adicCompletion K)ˣ}
    (hU : U ∈ 𝓝 (1 : (v.adicCompletion K)ˣ)) :
    ∃ n : ℕ,
      (localHigherUnitGroup v n :
        Set (v.adicCompletion K)ˣ) ⊆ U := by
  have hU' :
      U ∈ Filter.comap
        (Units.val : (v.adicCompletion K)ˣ →
          v.adicCompletion K)
        (𝓝 (1 : v.adicCompletion K)) := by
    have heq :
        𝓝 (1 : (v.adicCompletion K)ˣ) =
          Filter.comap
            (Units.val : (v.adicCompletion K)ˣ →
              v.adicCompletion K)
            (𝓝 (1 : v.adicCompletion K)) := by
      simpa using
        Units.isEmbedding_val₀.nhds_eq_comap
          (1 : (v.adicCompletion K)ˣ)
    rw [← heq]
    exact hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible
      (v.adicCompletionIntegers K)
  have hϖlt : ‖ϖ‖ < 1 :=
    local_irreducible_norm_lt_one v hϖ
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ, ‖ϖ‖ ^ n < ε :=
    exists_pow_lt_of_lt_one hε hϖlt
  refine ⟨n, ?_⟩
  intro x hx
  apply hVU
  apply hball
  change dist
      (((x : (v.adicCompletion K)ˣ) :
        v.adicCompletion K))
      1 < ε
  rw [dist_eq_norm]
  exact (localHigherUnit_norm_sub_one_le v ϖ hϖ n hx).trans_lt hn

open scoped Classical in
/-- Every identity neighborhood in the finite ideles contains a finite
congruence subgroup. -/
theorem exists_finiteCongruenceSubgroup_subset
    {U : Set (FiniteIdeleGroup K)}
    (hUopen : IsOpen U) (hUone : (1 : FiniteIdeleGroup K) ∈ U) :
    ∃ m : FiniteModulus K,
      (finiteCongruenceSubgroup m :
        Set (FiniteIdeleGroup K)) ⊆ U := by
  let D :=
    fun v : HeightOneSpectrum (𝓞 K) ↦
      (v.adicCompletionIntegers K).units
  let s : (∀ v, D v) → FiniteIdeleGroup K :=
    FiniteIdeleGroup.integralStructureMap
  let V : Set (∀ v, D v) := s ⁻¹' U
  have hs : Continuous s := by
    exact RestrictedProduct.isEmbedding_structureMap.continuous
  have hVopen : IsOpen V :=
    hUopen.preimage hs
  have hVone : (1 : ∀ v, D v) ∈ V := by
    change s 1 ∈ U
    have hsone : s 1 = 1 := by
      ext v
      rfl
    rw [hsone]
    exact hUone
  obtain ⟨T, u, hu, hTu⟩ :=
    isOpen_pi_iff.mp hVopen (1 : ∀ v, D v) hVone
  let W :
      ∀ v : T, Set (v.1.adicCompletion K)ˣ :=
    fun v ↦ Subtype.val '' u v.1
  have hWopen (v : T) : IsOpen (W v) := by
    exact
      (isOpen_finiteLocalUnits K v.1).isOpenEmbedding_subtypeVal.isOpenMap
        (u v.1) (hu v.1 v.2).1
  have hWone (v : T) :
      (1 : (v.1.adicCompletion K)ˣ) ∈ W v := by
    exact ⟨1, (hu v.1 v.2).2, rfl⟩
  have hWnhds (v : T) :
      W v ∈ 𝓝 (1 : (v.1.adicCompletion K)ˣ) :=
    (hWopen v).mem_nhds (hWone v)
  choose n hn using fun v : T ↦
    exists_localHigherUnitGroup_subset v.1 (hWnhds v)
  let exponent : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v ↦ if hv : v ∈ T then n ⟨v, hv⟩ else 0
  have hexponent :
      ∀ v, exponent v ≠ 0 → v ∈ T := by
    intro v hv
    by_contra hvT
    exact hv (by simp [exponent, hvT])
  let m : FiniteModulus K :=
    Finsupp.onFinset T exponent hexponent
  refine ⟨m, ?_⟩
  intro a ha
  have ha' :
      ∀ v, a v ∈ localHigherUnitGroup v (m v) :=
    (mem_finiteCongruenceSubgroup_iff m a).1 ha
  have haIntegral :
      ∀ v, a v ∈ (v.adicCompletionIntegers K).units :=
    fun v ↦ localHigherUnitGroup_le_finiteLocalUnits v (m v) (ha' v)
  let d : ∀ v, D v :=
    fun v ↦ ⟨a v, haIntegral v⟩
  have hdTu : d ∈ (T : Set _).pi u := by
    intro v hv
    have hv' : v ∈ T :=
      Finset.mem_coe.mp hv
    let vt : T := ⟨v, hv'⟩
    have hmv : m v = n vt := by
      simp [m, exponent, hv', vt]
    have hav :
        a v ∈ localHigherUnitGroup v (n vt) := by
      simpa only [hmv] using ha' v
    obtain ⟨z, hzu, hza⟩ := hn vt hav
    have hzd : z = d v :=
      Subtype.ext hza
    rwa [← hzd]
  have hdV : d ∈ V :=
    hTu hdTu
  have hsd : s d = a := by
    ext v
    rfl
  change s d ∈ U at hdV
  rwa [hsd] at hdV

open scoped Classical in
/-- The multiplicative topological equivalence between a real infinite
completion and `ℝ`. -/
def realCompletionContinuousMulEquiv
    (v : InfinitePlace K) (hv : v.IsReal) :
    v.Completion ≃ₜ* ℝ where
  __ :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous

open scoped Classical in
/-- The multiplicative topological equivalence between a complex infinite
completion and `ℂ`. -/
def complexCompletionContinuousMulEquiv
    (v : InfinitePlace K) (hv : v.IsComplex) :
    v.Completion ≃ₜ* ℂ where
  __ :=
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous

open scoped Classical in
/-- A positive real number regarded as a unit. -/
def positiveRealUnit (x : Set.Ioi (0 : ℝ)) : ℝˣ :=
  Units.mk0 x.1 x.2.ne'

open scoped Classical in
/-- The map from positive real numbers to real units is continuous. -/
theorem continuous_positiveRealUnit :
    Continuous positiveRealUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous
      (fun x : Set.Ioi (0 : ℝ) ↦ (x : ℝ))
    exact continuous_subtype_val
  · change Continuous
      (fun x : Set.Ioi (0 : ℝ) ↦ ((x : ℝ)⁻¹))
    exact continuous_subtype_val.inv₀
      (fun x : Set.Ioi (0 : ℝ) ↦ x.2.ne')

omit [NumberField K] in
open scoped Classical in
/-- The positive local multiplicative group at an infinite place is
connected. -/
theorem isConnected_infinitePositiveSubgroup
    (v : InfinitePlace K) :
    IsConnected
      ((infinitePositiveSubgroup v : Subgroup v.Completionˣ) :
        Set v.Completionˣ) := by
  rw [isConnected_iff_connectedSpace]
  by_cases hv : v.IsReal
  · let e : v.Completionˣ ≃ₜ* ℝˣ :=
      Units.mapContinuousMulEquiv
        (realCompletionContinuousMulEquiv v hv)
    let f : Set.Ioi (0 : ℝ) → infinitePositiveSubgroup v :=
      fun x ↦
        ⟨e.symm (positiveRealUnit x), by
          apply (mem_infinitePositiveSubgroup_iff v _).2
          intro hv'
          have heq : hv' = hv :=
            Subsingleton.elim _ _
          subst hv'
          change
            0 < ((e (e.symm (positiveRealUnit x)) : ℝˣ) : ℝ)
          rw [e.apply_symm_apply]
          exact x.2⟩
    let : ConnectedSpace (Set.Ioi (0 : ℝ)) :=
      isConnected_iff_connectedSpace.mp isConnected_Ioi
    apply Function.Surjective.connectedSpace (f := f)
    · intro z
      have hzpos :
          0 < ((e z.1 : ℝˣ) : ℝ) := by
        change 0 <
          InfinitePlace.Completion.extensionEmbeddingOfIsReal
            hv (z.1 : v.Completion)
        exact
          ((mem_infinitePositiveSubgroup_iff v z.1).1 z.2 hv)
      let x : Set.Ioi (0 : ℝ) :=
        ⟨((e z.1 : ℝˣ) : ℝ), hzpos⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change e.symm (positiveRealUnit x) = z.1
      apply e.injective
      simp [x, positiveRealUnit]
    · apply continuous_induced_rng.mpr
      exact e.symm.continuous.comp continuous_positiveRealUnit
  · have hvc : v.IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completionˣ ≃ₜ* ℂˣ :=
      Units.mapContinuousMulEquiv
        (complexCompletionContinuousMulEquiv v hvc)
    let f : ℂˣ → infinitePositiveSubgroup v :=
      fun x ↦
        ⟨e.symm x, by
          apply (mem_infinitePositiveSubgroup_iff v _).2
          intro hv'
          exact (hv hv').elim⟩
    apply Function.Surjective.connectedSpace (f := f)
    · intro z
      refine ⟨e z.1, ?_⟩
      apply Subtype.ext
      exact e.symm_apply_apply z.1
    · apply continuous_induced_rng.mpr
      exact e.symm.continuous

omit [NumberField K] in
open scoped Classical in
/-- The narrow archimedean positivity subgroup is connected. -/
theorem isConnected_narrowInfiniteCongruenceSubgroup :
    IsConnected
      ((narrowInfiniteCongruenceSubgroup (K := K) :
        Subgroup (InfiniteIdeleGroup K)) :
          Set (InfiniteIdeleGroup K)) := by
  rw [isConnected_iff_connectedSpace]
  let (v : InfinitePlace K) :
      ConnectedSpace (infinitePositiveSubgroup v) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_infinitePositiveSubgroup v)
  let f :
      (∀ v : InfinitePlace K, infinitePositiveSubgroup v) →
        narrowInfiniteCongruenceSubgroup (K := K) :=
    fun x ↦
      ⟨ContinuousMulEquiv.piUnits.symm
          (fun v ↦ (x v : v.Completionˣ)), by
        apply (mem_narrowInfiniteCongruenceSubgroup_iff _).2
        intro v
        exact (x v).2⟩
  apply Function.Surjective.connectedSpace (f := f)
  · intro a
    let x : ∀ v : InfinitePlace K, infinitePositiveSubgroup v :=
      fun v ↦
        ⟨ContinuousMulEquiv.piUnits a.1 v,
          (mem_narrowInfiniteCongruenceSubgroup_iff a.1).1 a.2 v⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change ContinuousMulEquiv.piUnits.symm
        (fun v ↦ (x v : v.Completionˣ)) = a.1
    apply ContinuousMulEquiv.piUnits.injective
    simp [x]
  · apply continuous_induced_rng.mpr
    apply ContinuousMulEquiv.piUnits.symm.continuous.comp
    exact continuous_pi fun v ↦
      continuous_subtype_val.comp (continuous_apply v)

open scoped Classical in
/-- The sign of a unit at a real infinite place. -/
def realPlaceSign
    (v : {w : InfinitePlace K // w.IsReal}) :
    v.1.Completionˣ →* SignTypeˣ :=
  (Units.map signHom.toMonoidHom).comp
    (Units.map
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal
        v.2).toMonoidHom)

open scoped Classical in
/-- The tuple of signs of an infinite idele at all real places. -/
def infiniteSign :
    InfiniteIdeleGroup K →*
      ((v : {w : InfinitePlace K // w.IsReal}) → SignTypeˣ) :=
  MonoidHom.pi fun v ↦
    (realPlaceSign v).comp (InfiniteIdeleGroup.component v.1)

omit [NumberField K] in
open scoped Classical in
/-- Positivity at all real places is exactly the kernel of the infinite sign
map. -/
theorem infiniteSign_ker_eq_narrowInfiniteCongruenceSubgroup :
    (infiniteSign (K := K)).ker =
      narrowInfiniteCongruenceSubgroup (K := K) := by
  ext a
  constructor
  · intro ha
    have ha' : infiniteSign (K := K) a = 1 :=
      MonoidHom.mem_ker.mp ha
    apply (mem_narrowInfiniteCongruenceSubgroup_iff a).2
    intro v
    apply (mem_infinitePositiveSubgroup_iff v
      (ContinuousMulEquiv.piUnits a v)).2
    intro hv
    have hsign :=
      congrArg Units.val (congrFun ha' ⟨v, hv⟩)
    change
      SignType.sign
          (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
            ((InfiniteIdeleGroup.component v a :
              v.Completionˣ) : v.Completion)) =
        1 at hsign
    exact sign_eq_one_iff.mp hsign
  · intro ha
    apply MonoidHom.mem_ker.mpr
    funext v
    apply Units.ext
    change
      SignType.sign
          (InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
            ((InfiniteIdeleGroup.component v.1 a :
              v.1.Completionˣ) : v.1.Completion)) =
        1
    rw [sign_eq_one_iff]
    exact
      ((mem_narrowInfiniteCongruenceSubgroup_iff a).1 ha v.1) v.2

open scoped Classical in
/-- The infinite positivity subgroup has finite index (its quotient is
detected by the finitely many real signs). -/
instance narrowInfiniteCongruenceSubgroupFiniteIndex :
    (narrowInfiniteCongruenceSubgroup (K := K)).FiniteIndex := by
  rw [← infiniteSign_ker_eq_narrowInfiniteCongruenceSubgroup (K := K)]
  exact Subgroup.finiteIndex_ker (infiniteSign (K := K))

open scoped Classical in
/-- Every selected-real-place congruence subgroup has finite index, because
it contains the narrow positivity subgroup. -/
instance Modulus.infiniteCongruenceSubgroupFiniteIndex
    (m : Modulus K) :
    m.infiniteCongruenceSubgroup.FiniteIndex := by
  apply Subgroup.finiteIndex_of_le
    (H := narrowInfiniteCongruenceSubgroup (K := K))
    (K := m.infiniteCongruenceSubgroup)
  intro a ha
  rw [Modulus.mem_infiniteCongruenceSubgroup_iff]
  intro v _
  exact (mem_narrowInfiniteCongruenceSubgroup_iff a).1 ha v.1

open scoped Classical in
/-- The finite idele congruence subgroup lies in the everywhere-integral
finite ideles. -/
theorem finiteCongruenceSubgroup_le_integralSubgroup
    (m : FiniteModulus K) :
    finiteCongruenceSubgroup m ≤
      FiniteIdeleGroup.integralSubgroup (K := K) := by
  intro a ha v
  exact localHigherUnitGroup_le_finiteLocalUnits v (m v) (ha v)

open scoped Classical in
/-- Within the compact group of everywhere-integral finite ideles, every
finite congruence subgroup has finite index. -/
instance finiteCongruenceSubgroupFiniteRelIndex
    (m : FiniteModulus K) :
    (finiteCongruenceSubgroup m).IsFiniteRelIndex
      (FiniteIdeleGroup.integralSubgroup (K := K)) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  let U := FiniteIdeleGroup.integralSubgroup (K := K)
  let J := finiteCongruenceSubgroup m
  have hJU : J ≤ U :=
    finiteCongruenceSubgroup_le_integralSubgroup m
  let J' : Subgroup U := J.subgroupOf U
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp
      (FiniteIdeleGroup.isCompact_integralSubgroup (K := K))
  have hJOpen : IsOpen (J' : Set U) := by
    exact Subgroup.subgroupOf_isOpen U J
      (isOpen_finiteCongruenceSubgroup m)
  have : Finite (U ⧸ J') :=
    J'.quotient_finite_of_isOpen hJOpen
  exact Subgroup.finiteIndex_of_finite_quotient

open scoped Classical in
/-- Finite congruence subgroups are contravariant in the finite modulus. -/
theorem finiteCongruenceSubgroup_antitone
    {m n : FiniteModulus K} (hmn : m ≤ n) :
    finiteCongruenceSubgroup n ≤ finiteCongruenceSubgroup m := by
  intro a ha
  rw [mem_finiteCongruenceSubgroup_iff] at ha ⊢
  intro v
  exact localHigherUnitGroup_antitone v (hmn v) (ha v)

open scoped Classical in
/-- Infinite congruence subgroups are contravariant in the selected real
places of a full modulus. -/
theorem Modulus.infiniteCongruenceSubgroup_antitone
    {m n : Modulus K} (hmn : m ≤ n) :
    n.infiniteCongruenceSubgroup ≤ m.infiniteCongruenceSubgroup := by
  intro a ha
  rw [Modulus.mem_infiniteCongruenceSubgroup_iff] at ha ⊢
  intro v hv
  exact ha v (hmn.2 hv)

open scoped Classical in
/-- Idèle congruence subgroups are contravariant in a full modulus. -/
theorem Modulus.ideleCongruenceSubgroup_antitone
    {m n : Modulus K} (hmn : m ≤ n) :
    n.ideleCongruenceSubgroup ≤ m.ideleCongruenceSubgroup := by
  intro a ha
  rw [Modulus.mem_ideleCongruenceSubgroup_iff] at ha ⊢
  exact ⟨Modulus.infiniteCongruenceSubgroup_antitone hmn ha.1,
    finiteCongruenceSubgroup_antitone hmn.1 ha.2⟩

open scoped Classical in
/-- Ray congruence subgroups are contravariant in a full modulus. -/
theorem Modulus.congruenceSubgroup_antitone
    {m n : Modulus K} (hmn : m ≤ n) :
    n.congruenceSubgroup ≤ m.congruenceSubgroup := by
  unfold Modulus.congruenceSubgroup
  apply Subgroup.map_mono
  exact sup_le
    ((Modulus.ideleCongruenceSubgroup_antitone hmn).trans le_sup_left)
    le_sup_right

open scoped Classical in
/-- Ideles integral at all finite places split as the infinite ideles times
the compact group of integral finite ideles. -/
def integralIdeleEquiv :
    IdeleGroup.integralAtFinitePlaces (K := K) ≃*
      InfiniteIdeleGroup K ×
        FiniteIdeleGroup.integralSubgroup (K := K) where
  toFun a := (a.1.1, ⟨a.1.2, a.2⟩)
  invFun a := ⟨(a.1, a.2.1), a.2.2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv a := rfl
  map_mul' a b := rfl

open scoped Classical in
/-- Under `integralIdeleEquiv`, the idele congruence subgroup maps to the
product of its infinite and finite congruence factors. -/
theorem map_ideleCongruenceSubgroup_subgroupOf_integral (m : Modulus K) :
    ((m.ideleCongruenceSubgroup).subgroupOf
      (IdeleGroup.integralAtFinitePlaces (K := K))).map
        (integralIdeleEquiv (K := K)).toMonoidHom =
      m.infiniteCongruenceSubgroup.prod
        ((finiteCongruenceSubgroup m.finitePart).subgroupOf
          (FiniteIdeleGroup.integralSubgroup (K := K))) := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, hx.2⟩
  · rintro ⟨ha, hb⟩
    refine ⟨⟨(a.1, a.2.1), a.2.2⟩, ⟨ha, hb⟩, rfl⟩

open scoped Classical in
/-- The idele congruence subgroup has finite relative index in the ideles
which are integral at every finite place. -/
instance ideleCongruenceSubgroupFiniteRelIndex
    (m : Modulus K) :
    m.ideleCongruenceSubgroup.IsFiniteRelIndex
      (IdeleGroup.integralAtFinitePlaces (K := K)) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex,
    Subgroup.finiteIndex_iff]
  rw [← Subgroup.index_map_equiv
      ((m.ideleCongruenceSubgroup).subgroupOf
        (IdeleGroup.integralAtFinitePlaces (K := K)))
      (integralIdeleEquiv (K := K))]
  change
    (((m.ideleCongruenceSubgroup).subgroupOf
      (IdeleGroup.integralAtFinitePlaces (K := K))).map
        (integralIdeleEquiv (K := K)).toMonoidHom).index ≠ 0
  rw [map_ideleCongruenceSubgroup_subgroupOf_integral]
  let :
      ((finiteCongruenceSubgroup m.finitePart).subgroupOf
        (FiniteIdeleGroup.integralSubgroup (K := K))).FiniteIndex :=
    Subgroup.IsFiniteRelIndex.to_finiteIndex_subgroupOf
  rw [Subgroup.index_prod]
  exact mul_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero :
      m.infiniteCongruenceSubgroup.index ≠ 0)
    (Subgroup.FiniteIndex.index_ne_zero :
      ((finiteCongruenceSubgroup m.finitePart).subgroupOf
        (FiniteIdeleGroup.integralSubgroup (K := K))).index ≠ 0)

open scoped Classical in
/-- The subgroup defining the ordinary ideal class group has finite index. -/
instance ordinaryIdealClassSubgroupFiniteIndex :
    (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
      IdeleGroup.principalSubgroup K).FiniteIndex := by
  let : Finite
      (IdeleGroup K ⧸
        (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K)) :=
    Finite.of_equiv (ClassGroup (𝓞 K))
    (IdeleGroup.quotientIntegralSupPrincipalEquiv
      (K := K)).symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

open scoped Classical in
/-- The subgroup `I_K^m Kˣ` has finite index in the idele group. -/
instance ideleCongruenceSupPrincipalFiniteIndex
    (m : Modulus K) :
    (m.ideleCongruenceSubgroup ⊔
      IdeleGroup.principalSubgroup K).FiniteIndex := by
  let J := m.ideleCongruenceSubgroup
  let P := IdeleGroup.principalSubgroup K
  let U := IdeleGroup.integralAtFinitePlaces (K := K)
  let H := J ⊔ P
  let V := U ⊔ P
  have hJU : J ≤ U := by
    intro a ha
    exact finiteCongruenceSubgroup_le_integralSubgroup m.finitePart ha.2
  have hHV : H ≤ V :=
    sup_le (hJU.trans le_sup_left) le_sup_right
  have hJUfinite : J.IsFiniteRelIndex U :=
    ideleCongruenceSubgroupFiniteRelIndex m
  have hHUfinite : H.IsFiniteRelIndex U :=
    Subgroup.isFiniteRelIndex_of_le_left U le_sup_left
  have hsup : U ⊔ H = V := by
    dsimp only [H, V]
    calc
      U ⊔ (J ⊔ P) = (U ⊔ J) ⊔ P := (sup_assoc U J P).symm
      _ = U ⊔ P := by rw [sup_eq_left.mpr hJU]
  have hrel : H.relIndex V ≠ 0 := by
    rw [← hsup, Subgroup.relIndex_sup_right]
    exact Subgroup.relIndex_ne_zero
  have hVindex : V.index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  change H.FiniteIndex
  rw [Subgroup.finiteIndex_iff,
    ← Subgroup.relIndex_mul_index hHV]
  exact mul_ne_zero hrel hVindex

open scoped Classical in
/-- The ray congruence subgroup in the idele class group is open. -/
theorem isOpen_congruenceSubgroup (m : Modulus K) :
    IsOpen
      ((m.congruenceSubgroup :
        Subgroup (IdeleClassGroup K)) :
          Set (IdeleClassGroup K)) := by
  let J := m.ideleCongruenceSubgroup
  let P := IdeleGroup.principalSubgroup K
  have hsupOpen : IsOpen ((J ⊔ P : Subgroup (IdeleGroup K)) :
      Set (IdeleGroup K)) :=
    Subgroup.isOpen_mono le_sup_left
      (isOpen_ideleCongruenceSubgroup m)
  rw [Modulus.congruenceSubgroup, Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe _ hsupOpen

open scoped Classical in
/-- Every ray congruence subgroup is closed. -/
theorem isClosed_congruenceSubgroup (m : Modulus K) :
    IsClosed
      ((m.congruenceSubgroup :
        Subgroup (IdeleClassGroup K)) :
          Set (IdeleClassGroup K)) :=
  (m.congruenceSubgroup).isClosed_of_isOpen
    (isOpen_congruenceSubgroup m)

open scoped Classical in
/-- Every ray congruence subgroup has finite index. -/
instance congruenceSubgroupFiniteIndex (m : Modulus K) :
    m.congruenceSubgroup.FiniteIndex := by
  let : Finite (RayClassGroup m) :=
    Finite.of_equiv
    (IdeleGroup K ⧸
      (m.ideleCongruenceSubgroup ⊔
        IdeleGroup.principalSubgroup K))
    (rayClassGroupEquivIdeleQuotient m).symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

open scoped Classical in
/-- The image of the connected narrow archimedean positivity subgroup lies in
every open subgroup of the idele class group. -/
theorem narrowInfiniteCongruenceSubgroup_mapsTo_openSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K)))
    {a : InfiniteIdeleGroup K}
    (ha : a ∈ narrowInfiniteCongruenceSubgroup (K := K)) :
    (((a, (1 : FiniteIdeleGroup K)) : IdeleGroup K) :
      IdeleClassGroup K) ∈ H := by
  let : ConnectedSpace
      (narrowInfiniteCongruenceSubgroup (K := K)) :=
    isConnected_iff_connectedSpace.mp
      isConnected_narrowInfiniteCongruenceSubgroup
  let f :
      narrowInfiniteCongruenceSubgroup (K := K) →
        IdeleClassGroup K :=
    fun x ↦
      (((x.1, (1 : FiniteIdeleGroup K)) : IdeleGroup K) :
        IdeleClassGroup K)
  have hf : Continuous f := by
    apply QuotientGroup.continuous_mk.comp
    exact continuous_subtype_val.prodMk continuous_const
  have hf_one : f 1 = 1 := by
    change
      ((QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K))
          ((1 : InfiniteIdeleGroup K),
            (1 : FiniteIdeleGroup K))) = 1
    exact map_one _
  have hinter :
      (Set.range f ∩ (H : Set (IdeleClassGroup K))).Nonempty := by
    refine ⟨1, ?_, H.one_mem⟩
    exact ⟨1, hf_one⟩
  have hsubset : Set.range f ⊆ (H : Set (IdeleClassGroup K)) :=
    (isConnected_range hf).isPreconnected.subset_isClopen
      ⟨H.isClosed_of_isOpen hH, hH⟩ hinter
  exact hsubset ⟨⟨a, ha⟩, rfl⟩

open scoped Classical in
/-- Congruence subgroups are cofinal among the open subgroups of the idele
class group. -/
theorem exists_congruenceSubgroup_le_of_isOpen
    (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    ∃ m : Modulus K, m.congruenceSubgroup ≤ H := by
  let P := IdeleGroup.principalSubgroup K
  let q : IdeleGroup K →* IdeleClassGroup K :=
    QuotientGroup.mk' P
  let g : FiniteIdeleGroup K → IdeleClassGroup K :=
    fun b ↦ q ((1 : InfiniteIdeleGroup K), b)
  let U : Set (FiniteIdeleGroup K) := g ⁻¹' (H : Set _)
  have hq : Continuous q :=
    QuotientGroup.continuous_mk
  have hg : Continuous g := by
    exact hq.comp (continuous_const.prodMk continuous_id)
  have hUopen : IsOpen U :=
    hH.preimage hg
  have hUone : (1 : FiniteIdeleGroup K) ∈ U := by
    change g 1 ∈ H
    have hg_one : g 1 = 1 := by
      change q
          ((1 : InfiniteIdeleGroup K),
            (1 : FiniteIdeleGroup K)) = 1
      exact map_one q
    rw [hg_one]
    exact H.one_mem
  obtain ⟨f, hf⟩ :=
    exists_finiteCongruenceSubgroup_subset hUopen hUone
  let m : Modulus K := Modulus.narrowOfFinite f
  have hJ :
      m.ideleCongruenceSubgroup ≤ Subgroup.comap q H := by
    intro x hx
    have hx' := (Modulus.mem_ideleCongruenceSubgroup_iff m x).1 hx
    have hinf :
        q (x.1, (1 : FiniteIdeleGroup K)) ∈ H := by
      apply narrowInfiniteCongruenceSubgroup_mapsTo_openSubgroup H hH
      rw [← Modulus.infiniteCongruenceSubgroup_narrowOfFinite f]
      simpa [m] using hx'.1
    have hfin :
        q ((1 : InfiniteIdeleGroup K), x.2) ∈ H := by
      have hfinite : x.2 ∈ finiteCongruenceSubgroup f := by
        simpa [m] using hx'.2
      have := hf hfinite
      change g x.2 ∈ H at this
      exact this
    have hmul := H.mul_mem hinf hfin
    have hqx :
        q x =
          q (x.1, (1 : FiniteIdeleGroup K)) *
            q ((1 : InfiniteIdeleGroup K), x.2) := by
      rw [← map_mul]
      apply congrArg q
      apply Prod.ext
      · exact (mul_one x.1).symm
      · exact (one_mul x.2).symm
    rw [← hqx] at hmul
    exact hmul
  refine ⟨m, ?_⟩
  rw [Modulus.congruenceSubgroup, Subgroup.map_le_iff_le_comap]
  apply sup_le
  · exact hJ
  · intro x hx
    change q x ∈ H
    have hxone : q x = 1 := by
      exact QuotientGroup.eq_one_iff x |>.2 hx
    rw [hxone]
    exact H.one_mem

open scoped Classical in
/-- A modulus whose ray congruence subgroup lies in the given open
subgroup. -/
noncomputable def chosenModulusInside
    (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    Modulus K :=
  Classical.choose
    (exists_congruenceSubgroup_le_of_isOpen H hH)

open scoped Classical in
/-- The chosen modulus has the required subgroup
inclusion. -/
theorem chosenModulusInside_spec
    (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    (chosenModulusInside H hH).congruenceSubgroup ≤ H :=
  Classical.choose_spec
    (exists_congruenceSubgroup_le_of_isOpen H hH)

open scoped Classical in
/-- Closed finite-index subgroups are open, hence also contain a chosen ray
congruence subgroup. -/
noncomputable def modulusInsideClosedFiniteIndex
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Modulus K :=
  chosenModulusInside H
    (H.isOpen_of_isClosed_of_finiteIndex hclosed)

open scoped Classical in
/-- Specification of the modulus selected for a closed finite-index
subgroup. -/
theorem modulusInsideClosedFiniteIndex_spec
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (modulusInsideClosedFiniteIndex H hclosed).congruenceSubgroup ≤ H :=
  chosenModulusInside_spec H
    (H.isOpen_of_isClosed_of_finiteIndex hclosed)

open scoped Classical in
/-- A subgroup of the idele class group is closed of
finite index exactly when it contains a ray congruence subgroup. -/
theorem isClosed_and_finiteIndex_iff_exists_congruenceSubgroup_le
    (H : Subgroup (IdeleClassGroup K)) :
    (IsClosed (H : Set (IdeleClassGroup K)) ∧ H.FiniteIndex) ↔
      ∃ m : Modulus K, m.congruenceSubgroup ≤ H := by
  constructor
  · rintro ⟨hHclosed, hHfinite⟩
    let : H.FiniteIndex := hHfinite
    exact exists_congruenceSubgroup_le_of_isOpen H
      (H.isOpen_of_isClosed_of_finiteIndex hHclosed)
  · rintro ⟨m, hm⟩
    have hHopen : IsOpen (H : Set (IdeleClassGroup K)) :=
      Subgroup.isOpen_mono hm (isOpen_congruenceSubgroup m)
    have : H.FiniteIndex :=
      Subgroup.finiteIndex_of_le hm
    exact ⟨H.isClosed_of_isOpen hHopen, inferInstance⟩

end RayClass
