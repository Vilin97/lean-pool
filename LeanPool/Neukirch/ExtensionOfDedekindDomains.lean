/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Abel
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# LeanPool.Neukirch.ExtensionOfDedekindDomains

Imported Lean Pool material for `LeanPool.Neukirch.ExtensionOfDedekindDomains`.
-/

open IsDedekindDomain Algebra UniqueFactorizationMonoid Ideal.IsDedekindDomain Multiset
  Module

attribute [local instance] Ideal.Quotient.field

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Multiplicativity of the ramification index in a tower of Dedekind domains, stated with the
hypotheses used by the Hilbert ramification development. -/
theorem ramificationIdx_algebra_tower_of_eq [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : IsPrime P] [hqm : IsPrime Q]
    (_hf0 : map (algebraMap R S) p ≠ ⊥) (hg0 : map (algebraMap S T) P ≠ ⊥)
    (hfg : map (algebraMap R T) p ≠ ⊥) (_hp0 : P ≠ ⊥) (_hq0 : Q ≠ 0)
    (hg : P = comap (algebraMap S T) Q) : ramificationIdx p Q =
    ramificationIdx p P * ramificationIdx P Q :=
  ramificationIdx_algebra_tower hg0 hfg (map_le_iff_le_comap.mpr (le_of_eq hg))

/-- Multiplicativity of the inertia degree in a tower of Dedekind domains, stated with the
hypotheses used by the Hilbert ramification development. -/
theorem inertiaDeg_algebra_tower_of_eq {p : Ideal R} {P : Ideal S} {I : Ideal T} [IsMaximal p]
    [IsMaximal P] [Nontrivial (T ⧸ I)] (hp : p = comap (algebraMap R S) P)
    (hP : P = comap (algebraMap S T) I) : inertiaDeg p I =
    inertiaDeg p P * inertiaDeg P I :=
  letI : P.LiesOver p := ⟨hp⟩
  letI : I.LiesOver P := ⟨hP⟩
  inertiaDeg_algebra_tower p P I

/-- The decomposition of a prime in a tower is `Nonsplit` when there is a unique prime above. -/
class Nonsplit {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Ideal R) : Prop where
  /-- There is at most one maximal ideal lying over `p`. -/
  nonsplit : ∀ P : Ideal S, P.IsMaximal → p = comap f P →
    ∀ Q : Ideal S, Q.IsMaximal → p = comap f Q → P = Q

end Ideal
