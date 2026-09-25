/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum

/-!
# Open Ideals and the Topological Nilradical

We prove Lemma 6.6 and Remark 7.30(1) of [Wedhorn, *Adic Spaces*]:
an ideal of an f-adic ring is open iff the topological nilradical is contained
in its radical.

## Main results

* `IsTopologicallyNilpotent.mem_ideal_radical` : A topologically nilpotent element
  lies in the radical of any open ideal.
* `topologicalNilradical_le_radical_of_isOpen` : Forward direction of Lemma 6.6.
* `ideal_isOpen_of_topologicalNilradical_le_radical` : Backward direction of
  Lemma 6.6 (using an abstract f-adic hypothesis).
* `ideal_isOpen_iff_topologicalNilradical_le_radical` : Lemma 6.6 (iff).
* `finset_span_isOpen_iff` : Remark 7.30(1).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 6.6, Remark 7.30(1)
-/

@[expose] public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- Topologically nilpotent elements lie in the radical of any open ideal. -/
theorem IsTopologicallyNilpotent.mem_ideal_radical
    {f : A} (hf : IsTopologicallyNilpotent f)
    {𝔞 : Ideal A} (h𝔞 : IsOpen (𝔞 : Set A)) :
    f ∈ 𝔞.radical :=
  Ideal.mem_radical_iff.mpr (hf.eventually (h𝔞.mem_nhds 𝔞.zero_mem)).exists

section LinearTopology

variable [IsLinearTopology A A]

/-- The topological nilradical is contained in the radical of any open ideal (Lemma 6.6). -/
theorem topologicalNilradical_le_radical_of_isOpen
    {𝔞 : Ideal A} (h𝔞 : IsOpen (𝔞 : Set A)) :
    topologicalNilradical A ≤ 𝔞.radical :=
  fun _ ha ↦
    (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp ha).mem_ideal_radical h𝔞

variable [ContinuousAdd A]

/-- An ideal is open if the topological nilradical is in its radical (Lemma 6.6, backward). -/
theorem ideal_isOpen_of_topologicalNilradical_le_radical
    (hJ : ∃ J : Ideal A, J.FG ∧ J ≤ topologicalNilradical A ∧
          ∀ n : ℕ, IsOpen ((J ^ n : Ideal A) : Set A))
    {𝔞 : Ideal A} (h : topologicalNilradical A ≤ 𝔞.radical) :
    IsOpen (𝔞 : Set A) := by
  obtain ⟨J, hfg, hle, hopen⟩ := hJ
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (hle.trans h) hfg
  have hopen_m := hopen m
  rw [show (𝔞 : Set A) = (𝔞.toAddSubgroup : Set A) from
    (Submodule.coe_toAddSubgroup 𝔞).symm]
  rw [show ((J ^ m : Ideal A) : Set A) = ((J ^ m).toAddSubgroup : Set A) from
    (Submodule.coe_toAddSubgroup (J ^ m)).symm] at hopen_m
  exact AddSubgroup.isOpen_mono ((Submodule.toAddSubgroup_le _ _).mpr hm) hopen_m

/-- An ideal is open iff the topological nilradical is in its radical (Lemma 6.6). -/
theorem ideal_isOpen_iff_topologicalNilradical_le_radical
    (hJ : ∃ J : Ideal A, J.FG ∧ J ≤ topologicalNilradical A ∧
          ∀ n : ℕ, IsOpen ((J ^ n : Ideal A) : Set A))
    (𝔞 : Ideal A) :
    IsOpen (𝔞 : Set A) ↔ topologicalNilradical A ≤ 𝔞.radical :=
  ⟨topologicalNilradical_le_radical_of_isOpen,
   ideal_isOpen_of_topologicalNilradical_le_radical hJ⟩

/-- `Ideal.span T` is open iff the topological nilradical is in its radical (Remark 7.30(1)). -/
theorem finset_span_isOpen_iff
    (hJ : ∃ J : Ideal A, J.FG ∧ J ≤ topologicalNilradical A ∧
          ∀ n : ℕ, IsOpen ((J ^ n : Ideal A) : Set A))
    (T : Finset A) :
    IsOpen ((Ideal.span (↑T : Set A) : Ideal A) : Set A) ↔
      topologicalNilradical A ≤ (Ideal.span (↑T : Set A)).radical :=
  ideal_isOpen_iff_topologicalNilradical_le_radical hJ _

end LinearTopology
