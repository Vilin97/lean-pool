/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
/-!
# Narrow finite conductors

This file constructs the finite part of the conductor in the convention
where every real place has the positive ray condition.  It is therefore a
*narrow finite conductor*, not yet the full global conductor of an
arbitrary modulus with an archimedean component.

The narrow finite conductor is the gcd of all finite moduli whose ray
class fields contain the given class field.  On norm subgroups, those are
exactly the moduli `m` for which `C_K^m ≤ H`.

We construct the gcd rather than postulating it.  At each finite prime its
exponent is the least exponent occurring among all defining moduli.  A
single defining modulus bounds the support, so these pointwise minima
assemble into a genuine finitely supported modulus.
-/

open scoped NumberField
noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A modulus defines a ray class field containing the class field
corresponding to `H` exactly when its congruence subgroup lies in `H`. -/
def IsDefiningModulus
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K) : Prop :=
  m.congruenceSubgroup ≤ H

open scoped Classical in
/-- An idèle-class subgroup for which a finite ray-class defining modulus
exists.  This is precisely the domain on which the narrow finite conductor
is defined. -/
abbrev ConductorialSubgroup
    (K : Type*) [Field K] [NumberField K] :=
  {H : Subgroup (IdeleClassGroup K) //
    ∃ m : RayClass.Modulus K, IsDefiningModulus H m}

open scoped Classical in
/-- At every finite place, some defining full modulus supplies a finite
defining exponent.  This is the nonemptiness input for the pointwise finite
conductor minimum. -/
theorem exists_definingFiniteExponent
    (H : Subgroup (IdeleClassGroup K))
    (h : ∃ m, IsDefiningModulus H m)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, ∃ m : RayClass.Modulus K,
      IsDefiningModulus H m ∧ m.finitePart v = n := by
  let m := Classical.choose h
  exact ⟨m.finitePart v, m, Classical.choose_spec h, rfl⟩

namespace ConductorialSubgroup

open scoped Classical in
/-- A chosen full modulus defining a conductorial subgroup. -/
noncomputable def chosenDefiningModulus
    (H : ConductorialSubgroup K) :
    RayClass.Modulus K :=
  Classical.choose H.2

open scoped Classical in
/-- The chosen full defining modulus has the advertised defining property. -/
theorem chosenDefiningModulus_spec
    (H : ConductorialSubgroup K) :
    IsDefiningModulus H.1 H.chosenDefiningModulus :=
  Classical.choose_spec H.2

open scoped Classical in
/-- The finite part of one chosen defining modulus, used to bound the
support of the narrow finite conductor. -/
noncomputable def narrowFiniteConductorBoundingModulus
    (H : ConductorialSubgroup K) :
    RayClass.FiniteModulus K :=
  H.chosenDefiningModulus.finitePart

open scoped Classical in
/-- The finite bounding modulus comes from an actual defining full modulus. -/
theorem narrowFiniteConductorBoundingModulus_spec
    (H : ConductorialSubgroup K) :
    ∃ m : RayClass.Modulus K,
      IsDefiningModulus H.1 m ∧
        m.finitePart = H.narrowFiniteConductorBoundingModulus :=
  ⟨H.chosenDefiningModulus, H.chosenDefiningModulus_spec, rfl⟩

open scoped Classical in
/-- The least narrow finite conductor exponent at `v` among all defining
moduli. -/
noncomputable def narrowFiniteConductorExponent
  (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find (exists_definingFiniteExponent H.1 H.2 v)

open scoped Classical in
/-- The least narrow finite conductor exponent is attained by an actual
defining modulus. -/
theorem narrowFiniteConductorExponent_spec
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ m : RayClass.Modulus K,
      IsDefiningModulus H.1 m ∧
        m.finitePart v = H.narrowFiniteConductorExponent v :=
  Nat.find_spec (exists_definingFiniteExponent H.1 H.2 v)

open scoped Classical in
/-- The narrow finite conductor exponent is no larger than the exponent in
any defining modulus. -/
theorem narrowFiniteConductorExponent_le
    (H : ConductorialSubgroup K)
    {m : RayClass.Modulus K}
    (hm : IsDefiningModulus H.1 m)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorExponent v ≤ m.finitePart v := by
  exact Nat.find_min'
    (exists_definingFiniteExponent H.1 H.2 v)
    ⟨m, hm, rfl⟩

open scoped Classical in
/-- The finite part of the conductor in the all-real-positive (narrow)
convention. -/
noncomputable def narrowFiniteConductor
    (H : ConductorialSubgroup K) :
    RayClass.FiniteModulus K where
  toFun := H.narrowFiniteConductorExponent
  support :=
    H.narrowFiniteConductorBoundingModulus.support.filter
      (fun v => H.narrowFiniteConductorExponent v ≠ 0)
  mem_support_toFun := by
    intro v
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · exact fun hv => hv.2
    · intro hv
      refine ⟨?_, hv⟩
      intro hbound
      have hle :
          H.narrowFiniteConductorExponent v ≤
            H.narrowFiniteConductorBoundingModulus v := by
        simpa only [narrowFiniteConductorBoundingModulus] using
        H.narrowFiniteConductorExponent_le
          H.chosenDefiningModulus_spec v
      rw [hbound] at hle
      exact hv (Nat.eq_zero_of_le_zero hle)

open scoped Classical in
/-- Evaluating the narrow finite conductor returns its finite local
conductor exponent. -/
@[simp]
theorem narrowFiniteConductor_apply
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductor v = H.narrowFiniteConductorExponent v :=
  rfl

open scoped Classical in
/-- The narrow finite conductor divides every defining modulus
(equivalently, its exponents are pointwise no larger). -/
theorem narrowFiniteConductor_le
    (H : ConductorialSubgroup K)
    {m : RayClass.Modulus K}
    (hm : IsDefiningModulus H.1 m) :
    H.narrowFiniteConductor ≤ m.finitePart := by
  intro v
  exact H.narrowFiniteConductorExponent_le hm v

open scoped Classical in
/-- Universal gcd characterization of the narrow finite conductor. -/
theorem le_narrowFiniteConductor_iff
    (H : ConductorialSubgroup K)
    (d : RayClass.FiniteModulus K) :
    d ≤ H.narrowFiniteConductor ↔
      ∀ m, IsDefiningModulus H.1 m → d ≤ m.finitePart := by
  constructor
  · intro hd m hm
    exact hd.trans (H.narrowFiniteConductor_le hm)
  · intro hd v
    obtain ⟨m, hm, hmv⟩ :=
      H.narrowFiniteConductorExponent_spec v
    change d v ≤ H.narrowFiniteConductorExponent v
    rw [← hmv]
    exact hd m hm v

open scoped Classical in
/-- A conductorial subgroup is open because it contains a ray congruence
subgroup. -/
theorem isOpen
    (H : ConductorialSubgroup K) :
    IsOpen ((H.1 : Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) := by
  obtain ⟨m, hm⟩ := H.2
  exact Subgroup.isOpen_mono hm (RayClass.isOpen_congruenceSubgroup m)

open scoped Classical in
/-- A conductorial subgroup is closed. -/
theorem isClosed
    (H : ConductorialSubgroup K) :
    IsClosed ((H.1 : Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) :=
  H.1.isClosed_of_isOpen H.isOpen

open scoped Classical in
/-- A conductorial subgroup has finite index. -/
instance finiteIndex
    (H : ConductorialSubgroup K) :
    H.1.FiniteIndex := by
  obtain ⟨m, hm⟩ := H.2
  exact Subgroup.finiteIndex_of_le hm

open scoped Classical in
/-- The narrow finite conductor is the gcd of the finite parts of the
defining full moduli. -/
theorem narrowFiniteConductor_is_gcd
    (H : ConductorialSubgroup K) :
    (∀ m, IsDefiningModulus H.1 m → H.narrowFiniteConductor ≤ m.finitePart) ∧
      (∀ d, (∀ m, IsDefiningModulus H.1 m → d ≤ m.finitePart) →
        d ≤ H.narrowFiniteConductor) := by
  constructor
  · intro m hm
    exact H.narrowFiniteConductor_le hm
  · intro d hd
    exact (H.le_narrowFiniteConductor_iff d).2 hd

end ConductorialSubgroup

open scoped Classical in
/-- A closed finite-index subgroup always has at least one defining
modulus. -/
theorem exists_definingModulus_of_isClosed_finiteIndex
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ∃ m, IsDefiningModulus H m :=
  ⟨RayClass.modulusInsideClosedFiniteIndex H hclosed,
    by
      simpa only [IsDefiningModulus] using
        RayClass.modulusInsideClosedFiniteIndex_spec H hclosed⟩

namespace ConductorialSubgroup

open scoped Classical in
/-- The conductorial subgroup canonically associated to a closed
finite-index idèle-class subgroup. -/
noncomputable def ofClosedFiniteIndex
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ConductorialSubgroup K :=
  ⟨H, exists_definingModulus_of_isClosed_finiteIndex H hclosed⟩

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
