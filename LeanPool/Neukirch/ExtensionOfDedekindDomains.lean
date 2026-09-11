/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.Abel
public import Mathlib.NumberTheory.KummerDedekind
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# LeanPool.Neukirch.ExtensionOfDedekindDomains

Imported Lean Pool material for `LeanPool.Neukirch.ExtensionOfDedekindDomains`.
-/

@[expose] public section

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
    (hg : P = comap (algebraMap S T) Q) : ramificationIdx' p Q =
    ramificationIdx' p P * ramificationIdx' P Q :=
  ramificationIdx'_algebra_tower hg0 hfg (map_le_iff_le_comap.mpr (le_of_eq hg))

/-- Multiplicativity of the inertia degree in a tower of Dedekind domains, stated with the
hypotheses used by the Hilbert ramification development. -/
theorem inertiaDeg_algebra_tower_of_eq {p : Ideal R} {P : Ideal S} {I : Ideal T} [IsMaximal p]
    [IsMaximal P] (hp : p = comap (algebraMap R S) P)
    (hP : P = comap (algebraMap S T) I) : inertiaDeg' p I =
    inertiaDeg' p P * inertiaDeg' P I :=
  letI : P.LiesOver p := ⟨hp⟩
  letI : I.LiesOver P := ⟨hP⟩
  inertiaDeg'_algebra_tower p P I

/-- The decomposition of a prime in a tower is `Nonsplit` when there is a unique prime above. -/
class Nonsplit {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Ideal R) : Prop where
  /-- There is at most one maximal ideal lying over `p`. -/
  nonsplit : ∀ P : Ideal S, P.IsMaximal → p = comap f P →
    ∀ Q : Ideal S, Q.IsMaximal → p = comap f Q → P = Q

end Ideal
