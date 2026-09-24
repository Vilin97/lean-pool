/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedLocality
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSelectionCore

/-!
# Gluing weak partial derivatives over an open cover

Weak partial derivatives produced separately on the members of an open cover
agree almost everywhere on the overlaps, because a locally integrable weak
partial derivative is unique almost everywhere on an open set.  They therefore
glue: over a countable open cover the pieces are represented by one function,
and by locality that function is the weak partial derivative on the union.

The second statement is the form used in practice.  It says that the existence
of a weak partial derivative is a purely local matter: if every point of an
open set has a neighbourhood on which `u` has a locally integrable `i`th weak
partial derivative, then `u` has one on the whole set.  Second countability of
`Fin d → ℝ` reduces the given family to a countable subfamily.
-/

@[expose] public section

open MeasureTheory Set
noncomputable section
namespace CKN

/-- Weak partial derivatives given on the members of a countable open cover of
`U` glue to a single locally integrable weak partial derivative on `U`, which
agrees almost everywhere with each given piece. -/
theorem exists_weakPartialDerivOn_of_countable_cover {d : ℕ}
    {U : Set (Vec d)} {V : ℕ → Set (Vec d)} {i : Fin d} {u : Vec d → ℝ}
    {g : ℕ → Vec d → ℝ}
    (hU : MeasurableSet U) (hV : ∀ n, IsOpen (V n)) (hcover : U ⊆ ⋃ n, V n)
    (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ n, LocallyIntegrableOn (g n) (V n) volume)
    (hweak : ∀ n, HasWeakPartialDerivOn (V n) i u (g n)) :
    ∃ G : Vec d → ℝ, LocallyIntegrableOn G U volume ∧
      HasWeakPartialDerivOn U i u G ∧
      ∀ n, G =ᵐ[volume.restrict (V n)] g n := by
  have hagree : ∀ m n, g m =ᵐ[volume.restrict (V m ∩ V n)] g n := by
    intro m n
    have hopen : IsOpen (V m ∩ V n) := (hV m).inter (hV n)
    exact HasWeakPartialDerivOn.ae_eq hopen
      ((hg m).mono_set inter_subset_left) ((hg n).mono_set inter_subset_right)
      ((hweak m).restrict hopen inter_subset_left)
      ((hweak n).restrict hopen inter_subset_right)
  obtain ⟨G, hG⟩ := exists_ae_eq_of_countable_family (fun n => (hV n).measurableSet) hagree
  have hGloc : LocallyIntegrableOn G U volume :=
    locallyIntegrableOn_of_ae_eq_cover hV hcover hg hG
  refine ⟨G, hGloc, ?_, hG⟩
  refine hasWeakPartialDerivOn_of_isOpen_cover hU hV hcover hu hGloc fun n => ?_
  exact (hweak n).congr_deriv_ae (hG n).symm

/-- Existence of a weak partial derivative is local: a function with a locally
integrable `i`th weak partial derivative near every point of an open set has
one on the whole set. -/
theorem exists_weakPartialDerivOn_of_local {d : ℕ}
    {U : Set (Vec d)} {i : Fin d} {u : Vec d → ℝ}
    (hU : IsOpen U) (hu : LocallyIntegrableOn u U volume)
    (hlocal : ∀ x ∈ U, ∃ W : Set (Vec d), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ g : Vec d → ℝ, LocallyIntegrableOn g W volume ∧
        HasWeakPartialDerivOn W i u g) :
    ∃ G : Vec d → ℝ, LocallyIntegrableOn G U volume ∧
      HasWeakPartialDerivOn U i u G := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · refine ⟨fun _ => 0, fun x hx => absurd hx (notMem_empty x), ?_⟩
    intro φ _ _ _
    simp
  · choose! W hWopen hWmem _hWU g hgloc hgweak using hlocal
    set Wsub : U → Set (Vec d) := fun a => W (a : Vec d) with hWsubdef
    have hUcov : U ⊆ ⋃ a : U, Wsub a := fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, hWmem x hx⟩
    obtain ⟨T, hTc, hTeq⟩ :=
      TopologicalSpace.isOpen_iUnion_countable Wsub (fun a => hWopen (a : Vec d) a.2)
    obtain ⟨x₀, hx₀⟩ := hUne
    have hTne : T.Nonempty := by
      have hx₀mem : x₀ ∈ ⋃ a ∈ T, Wsub a := by rw [hTeq]; exact hUcov hx₀
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx₀mem
      obtain ⟨haT, -⟩ := mem_iUnion.mp ha
      exact ⟨a, haT⟩
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hcover : U ⊆ ⋃ n : ℕ, Wsub (f n) := by
      intro x hx
      have hxmem : x ∈ ⋃ a ∈ T, Wsub a := by rw [hTeq]; exact hUcov hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hxmem
      obtain ⟨haT, hxa⟩ := mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := hf ▸ haT
      exact mem_iUnion.mpr ⟨n, hn ▸ hxa⟩
    obtain ⟨G, hGloc, hGweak, -⟩ :=
      exists_weakPartialDerivOn_of_countable_cover (V := fun n => Wsub (f n))
        hU.measurableSet (fun n => hWopen (f n : Vec d) (f n).2) hcover hu
        (fun n => hgloc (f n : Vec d) (f n).2)
        (fun n => hgweak (f n : Vec d) (f n).2)
    exact ⟨G, hGloc, hGweak⟩

end CKN
