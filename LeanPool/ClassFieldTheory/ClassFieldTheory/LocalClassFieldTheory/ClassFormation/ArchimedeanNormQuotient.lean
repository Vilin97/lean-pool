/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanHilbert90
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.InfinitePlaceTensorBlock
public import Mathlib.Basic.Real.Sign
public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import Mathlib.RingTheory.Complex
/-!
# The real/complex norm quotient

At a ramified infinite place the local extension is `ℂ/ℝ`.  Its norm
subgroup consists exactly of the positive real units, so the sign map
identifies the norm quotient with `ℤˣ`, a group of order two.
-/

@[expose] public section

open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

namespace LocalClassFieldTheory

universe u v w z

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open NumberField
open scoped NumberField.LiesOver

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- An infinite place above another one, written in the absolute-value
extension format used by the algebraic-localization API. -/
def infinitePlaceAbsoluteValueExtension
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    AbsoluteValueExtension v.1 L :=
  ⟨w.1, fun x =>
    congrArg
      (fun q : InfinitePlace K => q.1 x) hw⟩

open scoped Classical in
/-- The underlying absolute-value completion of a real infinite place
is the real numbers. -/
def absoluteCompletionRingEquivReal
    (v : InfinitePlace K) (hv : v.IsReal) :
    v.1.Completion ≃+* ℝ :=
  (InfinitePlace.Completion.equiv v).symm.trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv)

open scoped Classical in
/-- The underlying absolute-value completion of a complex infinite
place is the complex numbers. -/
def absoluteCompletionRingEquivComplex
    (v : InfinitePlace K) (hv : v.IsComplex) :
    v.1.Completion ≃+* ℂ :=
  (InfinitePlace.Completion.equiv v).symm.trans
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
open scoped Classical in
/-- For an infinite place, the absolute-value decomposition
group is the ordinary Galois stabilizer of that place. -/
theorem absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer
    (w : InfinitePlace L) :
    absoluteValueDecompositionGroup K w.1 =
      MulAction.stabilizer (L ≃ₐ[K] L) w := by
  ext σ
  constructor
  · intro hσ
    have hσi :
        σ⁻¹ ∈ absoluteValueDecompositionGroup K w.1 :=
      (absoluteValueDecompositionGroup K w.1).inv_mem hσ
    rw [mem_absoluteValueDecompositionGroup_iff_equivalent,
      LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv] at hσi
    rw [MulAction.mem_stabilizer_iff]
    apply
      (InfinitePlace.eq_iff_isEquiv
        (w := σ • w) (v := w)).2
    exact hσi
  · intro hσ
    rw [MulAction.mem_stabilizer_iff] at hσ
    have hσi :
        σ⁻¹ ∈ absoluteValueDecompositionGroup K w.1 := by
      rw [mem_absoluteValueDecompositionGroup_iff_equivalent,
        LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv]
      exact
        (InfinitePlace.eq_iff_isEquiv
          (w := σ • w) (v := w)).1 hσ
    simpa using
      (absoluteValueDecompositionGroup K w.1).inv_mem hσi

open scoped Classical in
/-- Field norms commute with compatible changes of both the base and
extension fields. -/
theorem normUnits_map_ringEquiv
    {K : Type u} {L : Type v} {K' : Type w} {L' : Type z}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L))
    (x : Lˣ) :
    Units.mapEquiv eK.toMulEquiv (normUnits K L x) =
      normUnits K' L'
        (Units.mapEquiv eL.toMulEquiv x) := by
  apply Units.ext
  change
    eK (Algebra.norm K (x : L)) =
      Algebra.norm K' (eL (x : L))
  rw [Algebra.norm_eq_of_equiv_equiv eK eL he]
  exact eK.apply_symm_apply _

open scoped Classical in
/-- Compatibility of a square of ring equivalences is symmetric. -/
theorem ringEquiv_compat_symm
    {K : Type u} {L : Type v} {K' : Type w} {L' : Type z}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L)) :
    RingHom.comp (algebraMap K L) eK.symm =
      RingHom.comp eL.symm (algebraMap K' L') := by
  ext x
  apply eL.injective
  have hx := DFunLike.congr_fun he (eK.symm x)
  simpa using hx.symm

open scoped Classical in
/-- A compatible pair of field equivalences induces a map of norm
quotients. -/
def normQuotientMapOfRingEquiv
    {K L K' L' : Type}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L)) :
    NormQuotient K L →* NormQuotient K' L' :=
  normQuotientLift
    ((normClass K' L').comp
      (Units.mapEquiv eK.toMulEquiv).toMonoidHom)
    (by
      rintro x ⟨y, rfl⟩
      rw [MonoidHom.mem_ker]
      change
        normClass K' L'
          (Units.mapEquiv eK.toMulEquiv
            (normUnits K L y)) = 1
      rw [normUnits_map_ringEquiv eK eL he]
      exact mk_normUnits_eq_one K' L'
        (Units.mapEquiv eL.toMulEquiv y))

open scoped Classical in
/-- Transporting a norm class through compatible field equivalences agrees
with transporting its representative unit. -/
@[simp]
theorem normQuotientMapOfRingEquiv_normClass
    {K L K' L' : Type}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L))
    (x : Kˣ) :
    normQuotientMapOfRingEquiv eK eL he
        (normClass K L x) =
      normClass K' L'
        (Units.mapEquiv eK.toMulEquiv x) :=
  normQuotientLift_normClass _ _ x

open scoped Classical in
/-- Norm quotients are invariant under compatible equivalences of the
base and extension fields. -/
def normQuotientEquivOfRingEquiv
    {K L K' L' : Type}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L)) :
    NormQuotient K L ≃* NormQuotient K' L' where
  toFun := normQuotientMapOfRingEquiv eK eL he
  invFun :=
    normQuotientMapOfRingEquiv eK.symm eL.symm
      (ringEquiv_compat_symm eK eL he)
  left_inv q := by
    refine NormQuotient.inductionOn
      (motive := fun q =>
        normQuotientMapOfRingEquiv eK.symm eL.symm
            (ringEquiv_compat_symm eK eL he)
            (normQuotientMapOfRingEquiv eK eL he q) =
          q)
      q ?_
    intro x
    rw [normQuotientMapOfRingEquiv_normClass,
      normQuotientMapOfRingEquiv_normClass]
    congr 1
    exact (Units.mapEquiv eK.toMulEquiv).symm_apply_apply x
  right_inv q := by
    refine NormQuotient.inductionOn
      (motive := fun q =>
        normQuotientMapOfRingEquiv eK eL he
            (normQuotientMapOfRingEquiv eK.symm eL.symm
              (ringEquiv_compat_symm eK eL he) q) =
          q)
      q ?_
    intro x
    rw [normQuotientMapOfRingEquiv_normClass,
      normQuotientMapOfRingEquiv_normClass]
    congr 1
    exact (Units.mapEquiv eK.toMulEquiv).apply_symm_apply x
  map_mul' := fun x y =>
    map_mul (normQuotientMapOfRingEquiv eK eL he) x y

open scoped Classical in
/-- A one-element acting group has trivial degree-zero Herbrand
cohomology. -/
theorem herbrandH0_card_eq_one_of_group_card_eq_one
    {G A : Type*}
    [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]
    (hG : Nat.card G = 1) :
    Nat.card (HerbrandH0 G A) = 1 := by
  let : Subsingleton G :=
    (Nat.card_eq_one_iff_unique.mp hG).1
  let : Subsingleton (HerbrandH0 G A) :=
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup
      (G := G) (A := A) (by
        intro a ha
        refine ⟨a, ?_⟩
        rw [tateNormHom_apply]
        unfold tateNorm
        classical
        have huniv : (Finset.univ : Finset G) = {1} := by
          ext g
          simp [Subsingleton.elim g 1]
        rw [huniv]
        simp)
  exact Nat.card_unique

open scoped Classical in
/-- At a complex place above a real place, the completion norm quotient
is the concrete quotient for `ℂ/ℝ`. -/
def infiniteCompletionNormQuotientEquivRealComplex
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hv : v.IsReal) (hwc : w.IsComplex) :
    letI : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    NormQuotient v.Completion w.Completion ≃*
      NormQuotient ℝ ℂ := by
  letI : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  letI :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      w hv
  exact
    normQuotientEquivOfRingEquiv
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv)
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc)
      (by ext; simp)

open scoped Classical in
/-- The algebraic localization used in the local cohomology block is
canonically the whole absolute-value completion, also at an infinite
place. -/
def localizedCompletionNormQuotientEquivAbsoluteCompletions
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI hL :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hL.toSMul
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    letI : Algebra v.1.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 w.1
        (infinitePlaceAbsoluteValueExtension v w hw).2
    NormQuotient v.1.Completion
        (LocalizedCompletion v.1 u) ≃*
      NormQuotient v.1.Completion w.1.Completion := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  letI hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  letI : SMul K u.1.Completion := hL.toSMul
  letI : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  letI : Algebra v.1.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 w.1
      (infinitePlaceAbsoluteValueExtension v w hw).2
  let eLAlg :
      LocalizedCompletion v.1 u ≃ₐ[v.1.Completion]
        w.1.Completion :=
    localizedCompletionEquivCompletion
      v.1 v.isNontrivial u
  let eL : LocalizedCompletion v.1 u ≃+* w.1.Completion :=
    eLAlg.toRingEquiv
  exact
    normQuotientEquivOfRingEquiv
      (RingEquiv.refl v.1.Completion) eL
      (by
        ext x
        exact eLAlg.commutes x)

open scoped Classical in
/-- Written using the underlying absolute-value completions, the norm
quotient at a complex place above a real place is again the concrete
quotient for `ℂ/ℝ`. -/
def absoluteCompletionNormQuotientEquivRealComplex
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hv : v.IsReal) (hwc : w.IsComplex) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI hL :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hL.toSMul
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    letI : Algebra v.1.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 w.1
        (infinitePlaceAbsoluteValueExtension v w hw).2
    NormQuotient v.1.Completion w.1.Completion ≃*
      NormQuotient ℝ ℂ := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  letI hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  letI : SMul K u.1.Completion := hL.toSMul
  letI : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  letI : Algebra v.1.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 w.1
      (infinitePlaceAbsoluteValueExtension v w hw).2
  letI : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  have hEmbedding :
      w.embedding.comp (algebraMap K L) =
        v.embedding :=
    (InfinitePlace.LiesOver.embedding_liesOver_of_isReal
      w hv).over
  have hCompletionEmbedding :
      ∀ x : v.1.Completion,
        InfinitePlace.Completion.extensionEmbedding w
            ((InfinitePlace.Completion.equiv w).symm
              (AbsoluteValue.completionMap
                v.1 w.1
                (infinitePlaceAbsoluteValueExtension
                  v w hw).2 x)) =
          InfinitePlace.Completion.extensionEmbedding v
            ((InfinitePlace.Completion.equiv v).symm x) := by
    intro x
    refine
      UniformSpace.Completion.induction_on
        (α := WithAbs v.1) x ?_ ?_
    · exact
        isClosed_eq
          ((InfinitePlace.Completion.isometry_extensionEmbedding
              w).continuous.comp
            ((InfinitePlace.Completion.continuous_ofCompletion
              w).comp
              (AbsoluteValue.completionMap_isometry
                v.1 w.1
                (infinitePlaceAbsoluteValueExtension
                  v w hw).2).continuous))
          ((InfinitePlace.Completion.isometry_extensionEmbedding
              v).continuous.comp
            (InfinitePlace.Completion.continuous_ofCompletion v))
    · intro y
      have hy :
          (y : v.1.Completion) =
            algebraMap K v.1.Completion
              (WithAbs.equiv v.1 y) := by
        rw [← AbsoluteValue.toCompletion_eq_algebraMap]
        simp
      have hmap :
          AbsoluteValue.completionMap v.1 w.1
              (infinitePlaceAbsoluteValueExtension v w hw).2
              (y : v.1.Completion) =
            AbsoluteValue.toCompletion w.1
              (algebraMap K L (WithAbs.equiv v.1 y)) :=
        (congrArg
          (AbsoluteValue.completionMap v.1 w.1
            (infinitePlaceAbsoluteValueExtension v w hw).2) hy).trans
          (AbsoluteValue.completionMap_coe v.1 w.1
            (infinitePlaceAbsoluteValueExtension v w hw).2
            (WithAbs.equiv v.1 y))
      have hwEmbedding :
          InfinitePlace.Completion.extensionEmbedding w
              ((InfinitePlace.Completion.equiv w).symm
                (AbsoluteValue.toCompletion w.1
                  (algebraMap K L (WithAbs.equiv v.1 y)))) =
            w.embedding (algebraMap K L (WithAbs.equiv v.1 y)) :=
        (InfinitePlace.Completion.extensionEmbedding_coe w
          ((WithAbs.equiv w.1).symm
            (algebraMap K L (WithAbs.equiv v.1 y)))).trans
          (congrArg w.embedding
            ((WithAbs.equiv w.1).apply_symm_apply
              (algebraMap K L (WithAbs.equiv v.1 y))))
      exact
        (congrArg (fun z : w.1.Completion =>
          InfinitePlace.Completion.extensionEmbedding w
            ((InfinitePlace.Completion.equiv w).symm z)) hmap).trans
          (hwEmbedding.trans
            ((DFunLike.congr_fun hEmbedding (WithAbs.equiv v.1 y)).trans
              (InfinitePlace.Completion.extensionEmbedding_coe v y).symm))
  exact
    normQuotientEquivOfRingEquiv
      (absoluteCompletionRingEquivReal v hv)
      (absoluteCompletionRingEquivComplex w hwc)
      (by
        ext x
        exact
          (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv
            ((InfinitePlace.Completion.equiv v).symm x)).trans
            (hCompletionEmbedding x).symm)

open scoped Classical in
/-- The sign of a nonzero real number, regarded as an integral unit. -/
def realUnitsSign : ℝˣ →* ℤˣ :=
  Units.map
    ((SignType.castHom (α := ℤ)).comp
      (signHom (α := ℝ)))

open scoped Classical in
/-- Coercing `realUnitsSign x` to an integer recovers the usual sign of
the underlying nonzero real number. -/
@[simp]
theorem realUnitsSign_coe (x : ℝˣ) :
    ((realUnitsSign x : ℤˣ) : ℤ) =
      (SignType.sign (x : ℝ) : ℤ) :=
  rfl

open scoped Classical in
/-- Both integral signs occur. -/
theorem realUnitsSign_surjective :
    Function.Surjective realUnitsSign := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, by simp [realUnitsSign]⟩
  · exact ⟨-1, by
      apply Units.ext
      simp [realUnitsSign]⟩

open scoped Classical in
/-- A nonzero real unit has trivial sign precisely when it is positive. -/
theorem mem_realUnitsSign_ker_iff (x : ℝˣ) :
    x ∈ realUnitsSign.ker ↔ 0 < (x : ℝ) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxv := congrArg Units.val hx
    have hs : SignType.sign (x : ℝ) = 1 := by
      cases hsign : SignType.sign (x : ℝ) <;>
        simp [realUnitsSign_coe, hsign] at hxv ⊢
    exact sign_eq_one_iff.mp hs
  · intro hx
    apply Units.ext
    simp [realUnitsSign, sign_pos hx]

open scoped Classical in
/-- The sign homomorphism is continuous for the native topology on
real units and the discrete topology on `ℤˣ`. -/
@[fun_prop]
theorem realUnitsSign_continuous :
    Continuous realUnitsSign := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def, map_one]
  intro V hV
  have hposOpen :
      IsOpen {x : ℝˣ | 0 < (x : ℝ)} :=
    isOpen_Ioi.preimage Units.continuous_val
  have hposOne :
      (1 : ℝˣ) ∈ {x : ℝˣ | 0 < (x : ℝ)} := by
    norm_num
  apply Filter.mem_of_superset (hposOpen.mem_nhds hposOne)
  intro x hx
  have hsign : realUnitsSign x = 1 :=
    MonoidHom.mem_ker.mp
      ((mem_realUnitsSign_ker_iff x).2 hx)
  change realUnitsSign x ∈ V
  rw [hsign]
  exact mem_of_mem_nhds hV

open scoped Classical in
/-- The norms from `ℂˣ` are precisely the positive real units. -/
theorem realUnitsSign_ker_eq_complexNormSubgroup :
    realUnitsSign.ker = localNormSubgroup ℝ ℂ := by
  ext x
  rw [mem_realUnitsSign_ker_iff]
  change 0 < (x : ℝ) ↔
    ∃ u : ℂˣ, normUnits ℝ ℂ u = x
  constructor
  · intro hx
    let z : ℂ :=
      (Real.sqrt (x : ℝ) : ℝ)
    have hz : z ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.sqrt_pos.2 hx))
    let u : ℂˣ := Units.mk0 z hz
    refine ⟨u, ?_⟩
    apply Units.ext
    change Algebra.norm ℝ (u : ℂ) = (x : ℝ)
    rw [Algebra.norm_complex_apply]
    simpa [u, z, Complex.normSq_ofReal] using
      Real.mul_self_sqrt hx.le
  · rintro ⟨u, rfl⟩
    change 0 < Algebra.norm ℝ (u : ℂ)
    rw [Algebra.norm_complex_apply, Complex.normSq_pos]
    exact Units.ne_zero u

open scoped Classical in
/-- The norm quotient for `ℂ/ℝ` is the two-element sign group. -/
def realComplexNormQuotientEquivSign :
    NormQuotient ℝ ℂ ≃* ℤˣ :=
  normQuotientEquivOfSurjective
    realUnitsSign
    realUnitsSign_surjective
    realUnitsSign_ker_eq_complexNormSubgroup

open scoped Classical in
/-- The real/complex norm quotient is finite via its equivalence with
the integral sign group. -/
noncomputable instance realComplexNormQuotientFinite :
    Finite (NormQuotient ℝ ℂ) :=
  Finite.of_equiv ℤˣ
    realComplexNormQuotientEquivSign.symm.toEquiv

open scoped Classical in
/-- The real/complex local norm quotient has order two. -/
theorem realComplexNormQuotient_card_eq_two :
    Nat.card (NormQuotient ℝ ℂ) = 2 := by
  rw [Nat.card_congr realComplexNormQuotientEquivSign.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

omit [NumberField L] in
omit [NumberField L] in
open scoped Classical in
/-- The degree-zero local Herbrand group at an infinite place has
cardinality equal to the archimedean local degree: one at an
unramified place and two at a ramified real-to-complex place. -/
theorem infinitePlaceLocalHerbrandH0_card_eq_localDegree
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI hL :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hL.toSMul
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    letI := localizedCompletionGlobalAlgebra v.1 u
    letI := localizedCompletionIsScalarTower v.1 u
    letI : FiniteDimensional v.1.Completion
        (LocalizedCompletion v.1 u) :=
      localizedCompletionModuleFinite v.1 v.isNontrivial u
    letI : IsGalois v.1.Completion
        (LocalizedCompletion v.1 u) :=
      HilbertRamification.algebraicLocalization_isGalois v.1 u
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ :=
      decompositionGroupLocalUnitsAction
        v.1 v.isNontrivial u
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion v.1 u)ˣ) =
      if w.IsUnramified K then 1 else 2 := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let := localizedCompletionGlobalAlgebra v.1 u
  let := localizedCompletionIsScalarTower v.1 u
  let : FiniteDimensional v.1.Completion
      (LocalizedCompletion v.1 u) :=
    localizedCompletionModuleFinite v.1 v.isNontrivial u
  let : IsGalois v.1.Completion
      (LocalizedCompletion v.1 u) :=
    HilbertRamification.algebraicLocalization_isGalois v.1 u
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion v.1 u)ˣ :=
    decompositionGroupLocalUnitsAction
      v.1 v.isNontrivial u
  by_cases hUnramified : w.IsUnramified K
  · rw [ite_eq_left hUnramified]
    apply herbrandH0_card_eq_one_of_group_card_eq_one
    rw [absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer w,
      InfinitePlace.card_stabilizer, ite_eq_left hUnramified]
  · rw [ite_eq_right hUnramified]
    have hRamified : w.IsRamified K := hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    have hwComplex : w.IsComplex :=
      hRamified.isComplex
    let eH0 :=
      localHerbrandH0EquivNormQuotient
        v.1 v.isNontrivial u
    let eCompletion :=
      localizedCompletionNormQuotientEquivAbsoluteCompletions
        v w hw
    let eRealComplex :=
      absoluteCompletionNormQuotientEquivRealComplex
        v w hw hvReal hwComplex
    calc
      Nat.card
          (HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ) =
          Nat.card (NormQuotient ℝ ℂ) :=
        Nat.card_congr
          (eH0.trans
            (eCompletion.trans eRealComplex)).toEquiv
      _ = 2 := realComplexNormQuotient_card_eq_two

omit [NumberField L] in
open scoped Classical in
/-- Complete archimedean local class-field axiom, in the exact form
used in the relative-idele Herbrand quotient: Hilbert 90 gives
`#H⁻¹ = 1`, while the norm quotient gives the local degree in `H⁰`. -/
theorem infinitePlaceLocalClassAxiom_cards
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI hL :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hL.toSMul
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    letI := localizedCompletionGlobalAlgebra v.1 u
    letI := localizedCompletionIsScalarTower v.1 u
    letI : FiniteDimensional v.1.Completion
        (LocalizedCompletion v.1 u) :=
      localizedCompletionModuleFinite v.1 v.isNontrivial u
    letI : IsGalois v.1.Completion
        (LocalizedCompletion v.1 u) :=
      HilbertRamification.algebraicLocalization_isGalois v.1 u
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ :=
      decompositionGroupLocalUnitsAction
        v.1 v.isNontrivial u
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion v.1 u)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K w.1)
            σ hgen)) = 1 ∧
      Nat.card
          (HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ) =
        if w.IsUnramified K then 1 else 2 := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let := localizedCompletionGlobalAlgebra v.1 u
  let := localizedCompletionIsScalarTower v.1 u
  let : FiniteDimensional v.1.Completion
      (LocalizedCompletion v.1 u) :=
    localizedCompletionModuleFinite v.1 v.isNontrivial u
  let : IsGalois v.1.Completion
      (LocalizedCompletion v.1 u) :=
    HilbertRamification.algebraicLocalization_isGalois v.1 u
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion v.1 u)ˣ :=
    decompositionGroupLocalUnitsAction
      v.1 v.isNontrivial u
  exact
    ⟨localHerbrandHMinusOne_card_eq_one_of_absoluteValue
        v.1 v.isNontrivial u σ hgen,
      infinitePlaceLocalHerbrandH0_card_eq_localDegree
        v w hw⟩

omit [NumberField L] in
open scoped Classical in
/-- Finiteness of the archimedean degree-zero local Herbrand group,
deduced from its explicit nonzero cardinality. -/
theorem infinitePlaceLocalHerbrandH0Finite
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ :=
      decompositionGroupLocalUnitsAction
        v.1 v.isNontrivial u
    Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ) := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let := localizedCompletionGlobalAlgebra v.1 u
  let := localizedCompletionIsScalarTower v.1 u
  let : FiniteDimensional v.1.Completion
      (LocalizedCompletion v.1 u) :=
    localizedCompletionModuleFinite v.1 v.isNontrivial u
  let : IsGalois v.1.Completion
      (LocalizedCompletion v.1 u) :=
    HilbertRamification.algebraicLocalization_isGalois v.1 u
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion v.1 u)ˣ :=
    decompositionGroupLocalUnitsAction
      v.1 v.isNontrivial u
  change
    Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ)
  by_cases hUnramified : w.IsUnramified K
  · have hGroup :
        Nat.card (absoluteValueDecompositionGroup K w.1) = 1 := by
      rw [absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer w,
        InfinitePlace.card_stabilizer, ite_eq_left hUnramified]
    let : Subsingleton (absoluteValueDecompositionGroup K w.1) :=
      (Nat.card_eq_one_iff_unique.mp hGroup).1
    let :
        Subsingleton
          (HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ) :=
      herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup
        (G := absoluteValueDecompositionGroup K w.1)
        (A := (LocalizedCompletion v.1 u)ˣ) (by
          intro a ha
          refine ⟨a, ?_⟩
          rw [tateNormHom_apply]
          unfold tateNorm
          classical
          have huniv :
              (Finset.univ :
                Finset (absoluteValueDecompositionGroup K w.1)) =
                {1} := by
            ext g
            simp [Subsingleton.elim g 1]
          rw [huniv]
          simp)
    exact
      Finite.of_injective
        (fun _ :
          HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ => false)
        (fun x y _ => Subsingleton.elim x y)
  · have hRamified : w.IsRamified K := hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    have hwComplex : w.IsComplex :=
      hRamified.isComplex
    let eH0 :=
      localHerbrandH0EquivNormQuotient
        v.1 v.isNontrivial u
    let eCompletion :=
      localizedCompletionNormQuotientEquivAbsoluteCompletions
        v w hw
    let eRealComplex :=
      absoluteCompletionNormQuotientEquivRealComplex
        v w hw hvReal hwComplex
    exact
      Finite.of_equiv
        (NormQuotient ℝ ℂ)
        (eH0.trans
          (eCompletion.trans eRealComplex)).symm.toEquiv

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- Finiteness of the archimedean degree-minus-one local Herbrand
group. -/
theorem infinitePlaceLocalHerbrandHMinusOneFinite
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ :=
      decompositionGroupLocalUnitsAction
        v.1 v.isNontrivial u
    Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen)) := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let := localizedCompletionGlobalAlgebra v.1 u
  let := localizedCompletionIsScalarTower v.1 u
  let : FiniteDimensional v.1.Completion
      (LocalizedCompletion v.1 u) :=
    localizedCompletionModuleFinite v.1 v.isNontrivial u
  let : IsGalois v.1.Completion
      (LocalizedCompletion v.1 u) :=
    HilbertRamification.algebraicLocalization_isGalois v.1 u
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion v.1 u)ˣ :=
    decompositionGroupLocalUnitsAction
      v.1 v.isNontrivial u
  change
    Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen))
  let :
      Subsingleton
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion v.1 u)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K w.1)
            σ hgen)) :=
    localHerbrandHMinusOne_subsingleton
      v.1 v.isNontrivial u σ hgen
  exact
    Finite.of_injective
      (fun _ => false)
      (fun x y _ => Subsingleton.elim x y)

end LocalClassFieldTheory
