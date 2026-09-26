/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Core.Patterns
public import LeanPool.Nivat.Dynamics.HalfPlanePair

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Orbit closure and pattern inheritance

This module formalizes the orbit closure and finite-pattern inheritance in
Section 1.1 of `paper/nivat.tex`. It proves that nonperiodicity gives an infinite
orbit closure, then applies Lemma 3.1 (`lem:halfplane-pair`) to the finite range
subtype with its discrete topology.

The main results are `finite_pattern_occurs`,
`patternAt_mem_patterns_of_mem_orbitClosure`, and
`halfPlane_pair_of_finiteRange_not_periodic`. The last theorem returns the full
pattern-language inclusion needed for Laurent annihilator inheritance.
-/

public section

namespace Nivat.Dynamics

open Set
open scoped Topology

/-- The set of all integer translates of a configuration, as defined in Section 1.1. -/
def orbit {A : Type*} (c : Configuration A) : Set (Configuration A) :=
  Set.range (fun h : Lattice => shift h c)

/-- The closure of the translation orbit in the product topology, denoted by `X_c` in
Section 1.1. -/
def orbitClosure {A : Type*} [TopologicalSpace A] (c : Configuration A) :
    Set (Configuration A) := closure (orbit c)

/-- Each shift is continuous in the product topology. This gives the shift invariance of `X_c`
used in Section 1.1 and Lemma 3.1 (`lem:halfplane-pair`). -/
theorem continuous_shift {A : Type*} [TopologicalSpace A] (h : Lattice) :
    Continuous (shift h : Configuration A → Configuration A) := by
  exact continuous_pi (fun z => continuous_apply (z + h))

/-- The orbit closure `X_c` of Section 1.1 is closed in the product topology. -/
theorem isClosed_orbitClosure {A : Type*} [TopologicalSpace A] (c : Configuration A) :
    IsClosed (orbitClosure c) := isClosed_closure

/-- Every translate of the original configuration belongs to its orbit closure `X_c`, as used in
Section 1.1. -/
theorem shift_mem_orbitClosure {A : Type*} [TopologicalSpace A] (c : Configuration A)
    (h : Lattice) : shift h c ∈ orbitClosure c := subset_closure ⟨h, rfl⟩

/-- The original configuration belongs to the orbit closure `X_c` of Section 1.1. -/
theorem mem_orbitClosure {A : Type*} [TopologicalSpace A] (c : Configuration A) :
    c ∈ orbitClosure c := by simpa using shift_mem_orbitClosure c 0

/-- The orbit closure `X_c` is invariant under every integer shift, as required by Lemma 3.1
(`lem:halfplane-pair`). -/
theorem shift_orbitClosure {A : Type*} [TopologicalSpace A] (c : Configuration A)
    (h : Lattice) {x : Configuration A} (hx : x ∈ orbitClosure c) :
    shift h x ∈ orbitClosure c := by
  apply closure_minimal (s := orbit c)
    (t := (shift h) ⁻¹' orbitClosure c) ?_
    ((isClosed_orbitClosure c).preimage (continuous_shift h)) hx
  rintro _ ⟨t, rfl⟩
  change shift h (shift t c) ∈ orbitClosure c
  rw [← shift_add]
  exact shift_mem_orbitClosure c (h + t)

/-- Every finite restriction of a point of `X_c` occurs in the original configuration. This is the
finite-pattern inheritance property of Section 1.1; discreteness is needed only for the
alphabet. -/
theorem finite_pattern_occurs {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (c : Configuration A) {x : Configuration A} (hx : x ∈ orbitClosure c)
    (D : Finset Lattice) : ∃ h : Lattice, ∀ z ∈ D, x z = c (z + h) := by
  let U : Set (Configuration A) := (D : Set Lattice).pi (fun z => {x z})
  have hU : IsOpen U := isOpen_set_pi D.finite_toSet (fun _ _ => isOpen_discrete _)
  have hxU : x ∈ U := by intro z _; rfl
  obtain ⟨y, hyU, hyo⟩ := mem_closure_iff.mp hx U hU hxU
  obtain ⟨h, rfl⟩ := hyo
  refine ⟨h, ?_⟩
  intro z hz
  exact (hyU z hz).symm

/-- Every translated pattern of an orbit-closure point belongs to the original pattern language,
by the inheritance property of Section 1.1. -/
theorem patternAt_mem_patterns_of_mem_orbitClosure {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Configuration A) {x : Configuration A}
    (hx : x ∈ orbitClosure c) (D : Finset Lattice) (u : Lattice) :
    patternAt x D u ∈ patterns c D := by
  obtain ⟨h, hh⟩ := finite_pattern_occurs c (shift_orbitClosure c u hx) D
  refine ⟨h, ?_⟩
  funext z
  exact (hh z.val z.property).symm

/-- A nonperiodic configuration has an injective translation orbit and hence infinite orbit
closure. This supplies the hypothesis of Lemma 3.1 in Corollary 3.6
(`cor:periodic-difference`). -/
theorem infinite_orbitClosure_of_not_periodic {A : Type*} [TopologicalSpace A]
    (c : Configuration A) (hn : ¬ Periodic c) : (orbitClosure c).Infinite := by
  have hinj : Function.Injective (fun h : Lattice => shift h c) := by
    intro h t heq
    by_contra hne
    apply hn
    refine ⟨h - t, sub_ne_zero.mpr hne, ?_⟩
    intro z
    have hval := congrFun heq (z - t)
    simpa [shift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hval
  exact (Set.infinite_range_of_injective hinj).mono subset_closure

/-- Lemma 3.1 (`lem:halfplane-pair`) for a nonperiodic configuration with arbitrary finite range,
together with the language inheritance of Section 1.1. Compactness is applied to the range
subtype with its discrete topology. -/
theorem halfPlane_pair_of_finiteRange_not_periodic {A : Type*}
    (c : Configuration A) (hc : FiniteRange c) (hn : ¬ Periodic c) :
    ∃ x y : Configuration A, ∃ ν : ℝ × ℝ,
      FiniteRange x ∧ FiniteRange y ∧ ν.1 ^ 2 + ν.2 ^ 2 = 1 ∧ x 0 ≠ y 0 ∧
        (∀ D : Finset Lattice, patternAt x D 0 ∈ patterns c D) ∧
        (∀ D : Finset Lattice, patternAt y D 0 ∈ patterns c D) ∧
        ∀ z : Lattice, ν.1 * (z.1 : ℝ) + ν.2 * (z.2 : ℝ) < 0 → x z = y z := by
  classical
  let Alphabet := Set.range c
  let _ : TopologicalSpace Alphabet := ⊥
  let _ : DiscreteTopology Alphabet := ⟨rfl⟩
  let _ : Finite Alphabet := hc
  let c' : Configuration Alphabet := fun z => ⟨c z, z, rfl⟩
  have hn' : ¬ Periodic c' := by
    intro hp
    apply hn
    exact (periodic_map_iff c' Subtype.val_injective).mpr hp
  obtain ⟨x, hx, y, hy, ν, hν, hxy, hhalf⟩ :=
    exists_halfPlane_pair_coordinates (orbitClosure c')
      (infinite_orbitClosure_of_not_periodic c' hn') (isClosed_orbitClosure c')
      (fun h x hx => shift_orbitClosure c' h hx)
  refine ⟨fun z => (x z).val, fun z => (y z).val, ν, ?_, ?_, hν, ?_, ?_, ?_, ?_⟩
  · apply hc.subset
    rintro _ ⟨z, rfl⟩
    exact (x z).property
  · apply hc.subset
    rintro _ ⟨z, rfl⟩
    exact (y z).property
  · intro heq
    exact hxy (Subtype.ext heq)
  · intro D
    obtain ⟨h, hh⟩ := patternAt_mem_patterns_of_mem_orbitClosure c' hx D 0
    refine ⟨h, ?_⟩
    funext z
    simpa only [patternAt, add_zero] using congrArg Subtype.val (congrFun hh z)
  · intro D
    obtain ⟨h, hh⟩ := patternAt_mem_patterns_of_mem_orbitClosure c' hy D 0
    refine ⟨h, ?_⟩
    funext z
    simpa only [patternAt, add_zero] using congrArg Subtype.val (congrFun hh z)
  · intro z hz
    exact congrArg Subtype.val (hhalf z hz)

end Nivat.Dynamics
