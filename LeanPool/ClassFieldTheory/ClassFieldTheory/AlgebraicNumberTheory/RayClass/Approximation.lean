/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
/-!
# Multiplicative weak approximation for ideles

This file extracts the simultaneous approximation statement needed for ray
class groups. At finitely many
finite places one may prescribe an arbitrary open multiplicative coset and
move a given idele into all of those cosets by a single principal idele.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

open scoped Classical in
/-- The full modulus whose finite part has exponent one exactly at the places
of a finite set and whose infinite part is empty.  It lets the ray-class
approximation space serve as an arbitrary finite-place approximation space. -/
noncomputable def modulusOfFinset
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RayClass.Modulus K := by
  classical
  exact RayClass.Modulus.ofFinite
    (Finsupp.onFinset S
      (fun v => if v ∈ S then 1 else 0)
      (by
        intro v hv
        simpa using hv))

open scoped Classical in
@[simp]
theorem modulusOfFinset_apply
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) :
    (modulusOfFinset S).finitePart v = if v ∈ S then 1 else 0 := by
  classical
  rfl

open scoped Classical in
@[simp]
theorem modulusOfFinset_support
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (modulusOfFinset S).finitePart.support = S := by
  classical
  ext v
  simp [modulusOfFinset, RayClass.Modulus.ofFinite]

open scoped Classical in
/-- The product of the prescribed finite local cosets and harmless
nonzero cosets at the infinite places.  The latter ensure that the global
approximating element is nonzero. -/
def openLocalCosetTarget
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ) :
    ∀ i : RayClass.ApproximationPlace m,
      Set (RayClass.approximationCompletion m i)
  | Sum.inl v => RayClass.unitRatioSet (a.2 v.1) (U v)
  | Sum.inr w =>
      RayClass.unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w) ⊤

open scoped Classical in
/-- Every coordinate of `openLocalCosetTarget` is open. -/
theorem isOpen_openLocalCosetTarget
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (hU : ∀ v, IsOpen (U v : Set (v.1.adicCompletion K)ˣ)) :
    ∀ i, IsOpen (openLocalCosetTarget m a U i)
  | Sum.inl v => by
      change IsOpen (RayClass.unitRatioSet (a.2 v.1) (U v))
      exact RayClass.isOpen_unitRatioSet _ _ (hU v)
  | Sum.inr w => by
      change IsOpen
        (RayClass.unitRatioSet
          (ContinuousMulEquiv.piUnits a.1 w) ⊤)
      exact RayClass.isOpen_unitRatioSet _ _ isOpen_univ

open scoped Classical in
/-- The given idele supplies a point in the product of the prescribed
local cosets. -/
def openLocalCosetTargetPoint
    (m : RayClass.Modulus K) (a : IdeleGroup K) :
    (i : RayClass.ApproximationPlace m) →
      RayClass.approximationCompletion m i
  | Sum.inl v => (a.2 v.1 : v.1.adicCompletion K)
  | Sum.inr w =>
      (ContinuousMulEquiv.piUnits a.1 w : w.Completion)

open scoped Classical in
/-- The target product used for multiplicative weak approximation is
nonempty. -/
theorem openLocalCosetTargetPoint_mem
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ) :
    openLocalCosetTargetPoint m a ∈
      Set.univ.pi (openLocalCosetTarget m a U) := by
  intro i _hi
  cases i with
  | inl v =>
      exact RayClass.val_mem_unitRatioSet _ _
  | inr w =>
      exact RayClass.val_mem_unitRatioSet _ _

open scoped Classical in
/-- Multiplicative weak approximation at finitely many finite places.

For arbitrary open subgroups `U_v ≤ K_vˣ` and an idele `a`, a single
global element `x ∈ Kˣ` makes every local quotient `a_v / x` lie in
`U_v`.  This is the precise approximation input in the proof of
the cyclic prime-power norm argument, and it is also used in roots-of-unity descent. -/
theorem exists_principal_quotient_mem_openLocalSubgroups
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (hU : ∀ v, IsOpen (U v : Set (v.1.adicCompletion K)ˣ)) :
    ∃ x : Kˣ, ∀ v : ↥m.finitePart.support,
      a.2 v.1 *
          ((principalIdele K x).2 v.1)⁻¹ ∈ U v := by
  let W : Set
      ((i : RayClass.ApproximationPlace m) →
        RayClass.approximationCompletion m i) :=
    Set.univ.pi (openLocalCosetTarget m a U)
  have hWOpen : IsOpen W := by
    exact isOpen_set_pi Set.finite_univ fun i _hi =>
      isOpen_openLocalCosetTarget m a U hU i
  have hWNonempty : W.Nonempty :=
    ⟨openLocalCosetTargetPoint m a,
      openLocalCosetTargetPoint_mem m a U⟩
  obtain ⟨x, hx⟩ :=
    (RayClass.denseRange_approximationEmbedding m).exists_mem_open
      hWOpen hWNonempty
  let w₀ : InfinitePlace K := Classical.choice inferInstance
  have hxw₀ :=
    hx (Sum.inr w₀) (Set.mem_univ (Sum.inr w₀))
  change
    (x : w₀.Completion) ∈
      RayClass.unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w₀) ⊤ at hxw₀
  obtain ⟨y₀, _hy₀, hy₀x⟩ := hxw₀
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply Units.ne_zero y₀
    rw [hy₀x, hxzero,
      NumberField.InfinitePlace.Completion.coe_zero]
  let xu : Kˣ := Units.mk0 x hx0
  refine ⟨xu, ?_⟩
  intro v
  have hvx :=
    hx (Sum.inl v) (Set.mem_univ (Sum.inl v))
  change
    FinitePlace.embedding v.1 x ∈
      RayClass.unitRatioSet (a.2 v.1) (U v) at hvx
  obtain ⟨y, hy, hyx⟩ := hvx
  have hprincipal :
      (principalIdele K xu).2 v.1 = y := by
    apply Units.ext
    calc
      (((principalIdele K xu).2 v.1 :
          (v.1.adicCompletion K)ˣ) :
          v.1.adicCompletion K) =
          (xu : K) :=
        finiteComponent_principalIdele xu v.1
      _ = (x : K) := rfl
      _ = (y : v.1.adicCompletion K) := hyx.symm
  rw [hprincipal]
  exact hy

open scoped Classical in
/-- Finset-indexed form of multiplicative weak approximation. -/
theorem exists_principal_quotient_mem_openLocalSubgroups_finset
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : IdeleGroup K)
    (U : ∀ v : ↥S, Subgroup (v.1.adicCompletion K)ˣ)
    (hU : ∀ v, IsOpen (U v : Set (v.1.adicCompletion K)ˣ)) :
    ∃ x : Kˣ, ∀ v : ↥S,
      a.2 v.1 *
          ((principalIdele K x).2 v.1)⁻¹ ∈ U v := by
  let m : RayClass.Modulus K := modulusOfFinset S
  have hm : m.finitePart.support = S := by
    simp [m]
  let U' : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ :=
    fun v => U ⟨v.1, hm ▸ v.2⟩
  have hU' :
      ∀ v, IsOpen (U' v : Set (v.1.adicCompletion K)ˣ) :=
    fun v => hU ⟨v.1, hm ▸ v.2⟩
  obtain ⟨x, hx⟩ :=
    exists_principal_quotient_mem_openLocalSubgroups
      m a U' hU'
  refine ⟨x, ?_⟩
  intro v
  have hv : v.1 ∈ m.finitePart.support := hm.symm ▸ v.2
  exact hx ⟨v.1, hv⟩

open scoped Classical in
/-- The product of prescribed open multiplicative cosets at every
archimedean place and at the finite places in a modulus. -/
def openAllLocalCosetTarget
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ) :
    ∀ i : RayClass.ApproximationPlace m,
      Set (RayClass.approximationCompletion m i)
  | Sum.inl v => RayClass.unitRatioSet (a.2 v.1) (U v)
  | Sum.inr w =>
      RayClass.unitRatioSet
        (IdeleGroup.infiniteComponent w a) (V w)

open scoped Classical in
/-- Every coordinate of the all-place multiplicative target is open. -/
theorem isOpen_openAllLocalCosetTarget
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ)
    (hU : ∀ v, IsOpen
      (U v : Set (v.1.adicCompletion K)ˣ))
    (hV : ∀ w, IsOpen
      (V w : Set w.Completionˣ)) :
    ∀ i, IsOpen
      (openAllLocalCosetTarget m a U V i)
  | Sum.inl v => by
      change IsOpen
        (RayClass.unitRatioSet (a.2 v.1) (U v))
      exact RayClass.isOpen_unitRatioSet _ _ (hU v)
  | Sum.inr w => by
      change IsOpen
        (RayClass.unitRatioSet
          (IdeleGroup.infiniteComponent w a) (V w))
      exact RayClass.isOpen_unitRatioSet _ _ (hV w)

open scoped Classical in
/-- The given idele supplies a point in the simultaneous all-place
multiplicative target. -/
theorem openLocalCosetTargetPoint_mem_all
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ) :
    openLocalCosetTargetPoint m a ∈
      Set.univ.pi
        (openAllLocalCosetTarget m a U V) := by
  intro i _hi
  cases i with
  | inl v =>
      exact RayClass.val_mem_unitRatioSet _ _
  | inr w =>
      exact RayClass.val_mem_unitRatioSet _ _

open scoped Classical in
/-- Multiplicative weak approximation simultaneously at all
archimedean places and at the finite support of a modulus.

For prescribed open subgroups `U_v ≤ K_vˣ` and
`V_w ≤ K_wˣ`, one global `x ∈ Kˣ` makes every quotient
`a_v / x` lie in the corresponding subgroup. -/
theorem exists_principal_quotient_mem_openAllLocalSubgroups
    (m : RayClass.Modulus K) (a : IdeleGroup K)
    (U : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ)
    (hU : ∀ v, IsOpen
      (U v : Set (v.1.adicCompletion K)ˣ))
    (hV : ∀ w, IsOpen
      (V w : Set w.Completionˣ)) :
    ∃ x : Kˣ,
      (∀ v : ↥m.finitePart.support,
        a.2 v.1 *
            ((principalIdele K x).2 v.1)⁻¹ ∈ U v) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (principalIdele K x))⁻¹ ∈ V w) := by
  let W : Set
      ((i : RayClass.ApproximationPlace m) →
        RayClass.approximationCompletion m i) :=
    Set.univ.pi (openAllLocalCosetTarget m a U V)
  have hWOpen : IsOpen W := by
    exact isOpen_set_pi Set.finite_univ fun i _hi =>
      isOpen_openAllLocalCosetTarget
        m a U V hU hV i
  have hWNonempty : W.Nonempty :=
    ⟨openLocalCosetTargetPoint m a,
      openLocalCosetTargetPoint_mem_all m a U V⟩
  obtain ⟨x, hx⟩ :=
    (RayClass.denseRange_approximationEmbedding m).exists_mem_open
      hWOpen hWNonempty
  let w₀ : InfinitePlace K := Classical.choice inferInstance
  have hxw₀ :=
    hx (Sum.inr w₀) (Set.mem_univ (Sum.inr w₀))
  change
    (x : w₀.Completion) ∈
      RayClass.unitRatioSet
        (IdeleGroup.infiniteComponent w₀ a)
        (V w₀) at hxw₀
  obtain ⟨y₀, _hy₀, hy₀x⟩ := hxw₀
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply Units.ne_zero y₀
    rw [hy₀x, hxzero,
      NumberField.InfinitePlace.Completion.coe_zero]
  let xu : Kˣ := Units.mk0 x hx0
  refine ⟨xu, ?_, ?_⟩
  · intro v
    have hvx :=
      hx (Sum.inl v) (Set.mem_univ (Sum.inl v))
    change
      FinitePlace.embedding v.1 x ∈
        RayClass.unitRatioSet (a.2 v.1) (U v) at hvx
    obtain ⟨y, hy, hyx⟩ := hvx
    have hprincipal :
        (principalIdele K xu).2 v.1 = y := by
      apply Units.ext
      calc
        (((principalIdele K xu).2 v.1 :
            (v.1.adicCompletion K)ˣ) :
            v.1.adicCompletion K) =
            (xu : K) :=
          finiteComponent_principalIdele xu v.1
        _ = (x : K) := rfl
        _ = (y : v.1.adicCompletion K) := hyx.symm
    rw [hprincipal]
    exact hy
  · intro w
    have hwx :=
      hx (Sum.inr w) (Set.mem_univ (Sum.inr w))
    change
      (x : w.Completion) ∈
        RayClass.unitRatioSet
          (IdeleGroup.infiniteComponent w a)
          (V w) at hwx
    obtain ⟨y, hy, hyx⟩ := hwx
    have hprincipal :
        IdeleGroup.infiniteComponent w
            (principalIdele K xu) = y := by
      apply Units.ext
      calc
        ((IdeleGroup.infiniteComponent w
            (principalIdele K xu) : w.Completionˣ) :
            w.Completion) =
            (xu : K) :=
          infiniteComponent_principalIdele xu w
        _ = (x : K) := rfl
        _ = (y : w.Completion) := hyx.symm
    rw [hprincipal]
    exact hy

open scoped Classical in
/-- Finset-indexed simultaneous finite-and-infinite multiplicative weak
approximation. -/
theorem exists_principal_quotient_mem_openAllLocalSubgroups_finset
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K)
    (U : ∀ v : ↥S,
      Subgroup (v.1.adicCompletion K)ˣ)
    (V : ∀ w : InfinitePlace K,
      Subgroup w.Completionˣ)
    (hU : ∀ v, IsOpen
      (U v : Set (v.1.adicCompletion K)ˣ))
    (hV : ∀ w, IsOpen
      (V w : Set w.Completionˣ)) :
    ∃ x : Kˣ,
      (∀ v : ↥S,
        a.2 v.1 *
            ((principalIdele K x).2 v.1)⁻¹ ∈ U v) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (principalIdele K x))⁻¹ ∈ V w) := by
  let m : RayClass.Modulus K := modulusOfFinset S
  have hm : m.finitePart.support = S := by
    simp [m]
  let U' : ∀ v : ↥m.finitePart.support,
      Subgroup (v.1.adicCompletion K)ˣ :=
    fun v => U ⟨v.1, hm ▸ v.2⟩
  have hU' :
      ∀ v, IsOpen (U' v : Set (v.1.adicCompletion K)ˣ) :=
    fun v => hU ⟨v.1, hm ▸ v.2⟩
  obtain ⟨x, hfinite, hinfinite⟩ :=
    exists_principal_quotient_mem_openAllLocalSubgroups
      m a U' V hU' hV
  refine ⟨x, ?_, hinfinite⟩
  intro v
  have hv : v.1 ∈ m.finitePart.support := hm.symm ▸ v.2
  exact hfinite ⟨v.1, hv⟩

open scoped Classical in
/-- A finite local family, extended by `1`, is a finite idele. -/
def finiteIdeleOfFinset
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    FiniteIdeleGroup K := by
  let f : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K)ˣ :=
    fun v => if hv : v ∈ S then a ⟨v, hv⟩ else 1
  refine ⟨f, ?_⟩
  have haway :
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        v ∉ S := by
    rw [Filter.eventually_cofinite]
    convert S.finite_toSet using 1
    ext v
    simp
  filter_upwards [haway] with v hv
  change f v ∈ (v.adicCompletionIntegers K).units
  simp [f, hv]

open scoped Classical in
@[simp]
theorem finiteIdeleOfFinset_apply_mem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : ↥S) :
    finiteIdeleOfFinset S a v.1 = a v := by
  classical
  change (if hv : v.1 ∈ S then a ⟨v.1, hv⟩ else 1) = a v
  exact dite_eq_left v.2

open scoped Classical in
@[simp]
theorem finiteIdeleOfFinset_apply_notMem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finiteIdeleOfFinset S a v = 1 := by
  classical
  change (if hmem : v ∈ S then a ⟨v, hmem⟩ else 1) =
    (1 : (v.adicCompletion K)ˣ)
  exact dite_eq_right hv

open scoped Classical in
/-- The idele whose prescribed finite components are `a` and whose other
finite and all infinite components are `1`. -/
def ideleOfFiniteLocalFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    IdeleGroup K :=
  (1, finiteIdeleOfFinset S a)

open scoped Classical in
@[simp]
theorem ideleOfFiniteLocalFamily_finiteComponent
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : ↥S) :
    (ideleOfFiniteLocalFamily S a).2 v.1 = a v :=
  finiteIdeleOfFinset_apply_mem S a v

open scoped Classical in
/-- The diagonal map from `Kˣ` to a finite product of local multiplicative
quotients. -/
def principalLocalQuotientMap
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : ∀ v : ↥S, Subgroup (v.1.adicCompletion K)ˣ) :
    Kˣ →* (∀ v : ↥S, (v.1.adicCompletion K)ˣ ⧸ U v) :=
  MonoidHom.pi fun v =>
    (QuotientGroup.mk' (U v)).comp
      ((finiteComponent v.1).comp (principalIdele K))

open scoped Classical in
@[simp]
theorem principalLocalQuotientMap_apply
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : ∀ v : ↥S, Subgroup (v.1.adicCompletion K)ˣ)
    (x : Kˣ) (v : ↥S) :
    principalLocalQuotientMap S U x v =
      QuotientGroup.mk' (U v) ((principalIdele K x).2 v.1) :=
  rfl

open scoped Classical in
/-- Multiplicative weak approximation is equivalently surjectivity of the
diagonal map to every finite product of quotients by open local subgroups. -/
theorem principalLocalQuotientMap_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : ∀ v : ↥S, Subgroup (v.1.adicCompletion K)ˣ)
    (hU : ∀ v, IsOpen (U v : Set (v.1.adicCompletion K)ˣ)) :
    Function.Surjective (principalLocalQuotientMap S U) := by
  intro q
  choose a ha using fun v : ↥S =>
    QuotientGroup.mk_surjective (q v)
  let α : IdeleGroup K :=
    ideleOfFiniteLocalFamily S a
  obtain ⟨x, hx⟩ :=
    exists_principal_quotient_mem_openLocalSubgroups_finset
      S α U hU
  refine ⟨x, ?_⟩
  funext v
  rw [principalLocalQuotientMap_apply, ← ha v]
  apply Eq.symm
  apply (QuotientGroup.eq_iff_div_mem).2
  simpa [α, div_eq_mul_inv] using hx v

end IdeleGroup
