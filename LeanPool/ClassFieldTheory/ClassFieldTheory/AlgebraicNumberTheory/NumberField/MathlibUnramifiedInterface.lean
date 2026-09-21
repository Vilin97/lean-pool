/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsEverywhereUnramified
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
/-!
# Finite-place unramifiedness comparison

The implementation quantifies over primes of the extension, while the public
definition quantifies over primes of the base.  These are equivalent because
every prime above a nonzero base prime is itself nonzero.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

/-- A number-field equivalence over `K` restricts to an equivalence of
integer rings over the integer ring of `K`. -/
noncomputable def ringOfIntegersEquivOfAlgEquiv
    (K L E : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra K E]
    (e : L ≃ₐ[K] E) : 𝓞 L ≃ₐ[𝓞 K] 𝓞 E := by
  let eℤ : L ≃ₐ[ℤ] E := e.restrictScalars ℤ
  let e𝓞 : 𝓞 L ≃ₐ[ℤ] 𝓞 E := eℤ.mapIntegralClosure
  exact AlgEquiv.ofRingEquiv (f := e𝓞.toRingEquiv) (fun x => by
    apply Subtype.ext
    change e (algebraMap (𝓞 K) L x) = algebraMap (𝓞 K) E x
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L x,
      IsScalarTower.algebraMap_apply (𝓞 K) K E x]
    exact e.commutes (algebraMap (𝓞 K) K x))

/-- Unramifiedness at all nonzero primes is equivalent to formal
unramifiedness of the entire integer-ring extension; the zero prime is
automatically unramified in characteristic zero. -/
theorem isUnramifiedAtFinitePlaces_iff_formallyUnramified
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    _root_.IsUnramifiedAtFinitePlaces K L ↔
      Algebra.FormallyUnramified (𝓞 K) (𝓞 L) := by
  rw [Algebra.formallyUnramified_iff_forall]
  constructor
  · intro h q
    by_cases hq : q.asIdeal = ⊥
    · simpa only [hq] using
        (Algebra.isUnramifiedAt_bot (R := 𝓞 K) (S := 𝓞 L))
    · exact h ⟨q.asIdeal, q.isPrime, hq⟩
  · intro h W
    exact h ⟨W.asIdeal, W.isPrime⟩

/-- The base-prime and extension-prime formulations of finite-place
unramifiedness agree. -/
theorem isUnramifiedAtFinitePlaces_iff_original
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    ClassFieldTheory.IsUnramifiedAtFinitePlaces K L ↔
      _root_.IsUnramifiedAtFinitePlaces K L := by
  constructor
  · intro h W
    let v := finitePlaceBelow (K := K) W
    exact h v W.asIdeal W.isPrime ⟨rfl⟩
  · intro h v P hP hOver
    let W : HeightOneSpectrum (𝓞 L) :=
      ⟨P, hP,
        @Ideal.ne_bot_of_liesOver_of_ne_bot
          (𝓞 K) (𝓞 L) _ _ _ _ v.asIdeal v.ne_bot P hOver⟩
    exact h W

/-- Finite-place unramifiedness is invariant under a number-field
equivalence over the base. -/
theorem isUnramifiedAtFinitePlaces_iff_of_algEquiv
    (K L E : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra K E]
    (e : L ≃ₐ[K] E) :
    ClassFieldTheory.IsUnramifiedAtFinitePlaces K L ↔
      ClassFieldTheory.IsUnramifiedAtFinitePlaces K E := by
  rw [isUnramifiedAtFinitePlaces_iff_original,
    isUnramifiedAtFinitePlaces_iff_original,
    isUnramifiedAtFinitePlaces_iff_formallyUnramified,
    isUnramifiedAtFinitePlaces_iff_formallyUnramified]
  exact Algebra.FormallyUnramified.iff_of_equiv
    (ringOfIntegersEquivOfAlgEquiv K L E e)

/-- Unramifiedness at infinite places is also invariant under a
number-field equivalence over the base. -/
theorem isUnramifiedAtInfinitePlaces_iff_of_algEquiv
    (K L E : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra K E]
    (e : L ≃ₐ[K] E) :
    IsUnramifiedAtInfinitePlaces K L ↔
      IsUnramifiedAtInfinitePlaces K E := by
  constructor
  · intro h
    refine ⟨fun w => ?_⟩
    have hw := (h.isUnramified (w.comap (e : L →+* E))).comap_algHom
      e.symm.toAlgHom
    have hcomp :
        (e : L →+* E).comp (e.symm.toAlgHom : E →+* L) = RingHom.id E := by
      ext x
      exact e.apply_symm_apply x
    simpa only [← InfinitePlace.comap_comp, hcomp,
      InfinitePlace.comap_id] using hw
  · intro h
    refine ⟨fun w => ?_⟩
    have hw := (h.isUnramified (w.comap (e.symm : E →+* L))).comap_algHom
      e.toAlgHom
    have hcomp :
        (e.symm : E →+* L).comp (e.toAlgHom : L →+* E) = RingHom.id L := by
      ext x
      exact e.symm_apply_apply x
    simpa only [← InfinitePlace.comap_comp, hcomp,
      InfinitePlace.comap_id] using hw

/-- The public conjunction and the implementation's bundled predicate for
unramifiedness at all places agree. -/
theorem isEverywhereUnramified_iff_original
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    ClassFieldTheory.IsEverywhereUnramified K L ↔
      _root_.IsEverywhereUnramified K L := by
  constructor
  · rintro ⟨hfinite, hinfinite⟩
    exact ⟨(isUnramifiedAtFinitePlaces_iff_original K L).mp hfinite, hinfinite⟩
  · intro h
    exact ⟨(isUnramifiedAtFinitePlaces_iff_original K L).mpr h.finitePlaces,
      h.infinitePlaces⟩

/-- Everywhere-unramifiedness is invariant under a number-field
equivalence over the base. -/
theorem isEverywhereUnramified_iff_of_algEquiv
    (K L E : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra K E]
    (e : L ≃ₐ[K] E) :
    ClassFieldTheory.IsEverywhereUnramified K L ↔
      ClassFieldTheory.IsEverywhereUnramified K E := by
  exact and_congr
    (isUnramifiedAtFinitePlaces_iff_of_algEquiv K L E e)
    (isUnramifiedAtInfinitePlaces_iff_of_algEquiv K L E e)

end ClassFieldTheory
