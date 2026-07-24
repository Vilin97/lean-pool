/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetVerification
import LeanPool.HadwigerNelsonBounds.PartsGadgetSymmetry

/-!
# The forced pair in the second-stage Parts gadget

The checked finite constraints force the opposite radius-two vertices 5 and 31
to have the same color.  Color renamings and central inversion reduce every
case to the independently checked normalized trees.
-/

namespace HadwigerNelsonBounds

/-- Renaming colors preserves both gadget constraints. -/
lemma PartsGadgetValid.rename {coloring : Fin 73 → Fin 4}
    (hvalid : PartsGadgetValid coloring) (rename : Fin 4 ≃ Fin 4) :
    PartsGadgetValid (fun vertex => rename (coloring vertex)) := by
  constructor
  · intro vertex neighbor hadj heq
    exact hvalid.1 vertex neighbor hadj (rename.injective heq)
  · intro vertex pair hpair
    rintro ⟨hleft, hright⟩
    exact hvalid.2 vertex pair hpair
      ⟨rename.injective hleft, rename.injective hright⟩

/-- Pulling a coloring back through central inversion preserves validity. -/
lemma PartsGadgetValid.negation {coloring : Fin 73 → Fin 4}
    (hvalid : PartsGadgetValid coloring) :
    PartsGadgetValid (fun vertex => coloring (partsGadgetNegation vertex)) := by
  constructor
  · intro vertex neighbor hadj
    exact hvalid.1 _ _ (partsGadgetNegation_neighbor hadj)
  · intro vertex pair hpair
    rintro ⟨hleft, hright⟩
    rcases partsGadgetNegation_triple hpair with hforward | hreverse
    · exact hvalid.2 _ _ hforward ⟨hleft, hright⟩
    · exact hvalid.2 _ _ hreverse ⟨hleft.trans hright, hright.symm⟩

/-- Swap the two residual colors while fixing zero and three. -/
def partsGadgetSwapOneTwo : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

/-- Swap the endpoint colors zero and three. -/
def partsGadgetSwapZeroThree : Fin 4 ≃ Fin 4 := Equiv.swap 0 3

@[simp] lemma partsGadgetSwapOneTwo_zero : partsGadgetSwapOneTwo 0 = 0 := by decide
@[simp] lemma partsGadgetSwapOneTwo_one : partsGadgetSwapOneTwo 1 = 2 := by decide
@[simp] lemma partsGadgetSwapOneTwo_two : partsGadgetSwapOneTwo 2 = 1 := by decide
@[simp] lemma partsGadgetSwapOneTwo_three : partsGadgetSwapOneTwo 3 = 3 := by decide

@[simp] lemma partsGadgetSwapZeroThree_zero : partsGadgetSwapZeroThree 0 = 3 := by decide
@[simp] lemma partsGadgetSwapZeroThree_one : partsGadgetSwapZeroThree 1 = 1 := by decide
@[simp] lemma partsGadgetSwapZeroThree_two : partsGadgetSwapZeroThree 2 = 2 := by decide
@[simp] lemma partsGadgetSwapZeroThree_three : partsGadgetSwapZeroThree 3 = 0 := by decide

lemma partsGadgetHardRoots {coloring : Fin 73 → Fin 4}
    (ha : coloring 5 = 0) (hb : coloring 31 = 3)
    (hcenter : coloring 18 = 0) (hanchor : coloring 25 = 1) :
    PartsGadgetExtends coloring partsGadgetHardCaseTree.roots := by
  intro assignment hin
  simp only [partsGadgetHardCaseTree, List.mem_cons, List.not_mem_nil,
    or_false] at hin
  rcases hin with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hcenter
  · exact hanchor

lemma partsGadgetMiddleRoots {coloring : Fin 73 → Fin 4}
    (ha : coloring 5 = 0) (hb : coloring 31 = 3)
    (hcenter : coloring 18 = 1) :
    PartsGadgetExtends coloring partsGadgetMiddleCertificate.roots := by
  intro assignment hin
  simp only [partsGadgetMiddleCertificate, List.mem_cons,
    List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hcenter

lemma no_partsGadget_coloring_of_hard_roots {coloring : Fin 73 → Fin 4}
    (hvalid : PartsGadgetValid coloring) (ha : coloring 5 = 0)
    (hb : coloring 31 = 3) (hcenter : coloring 18 = 0) : False := by
  have hnotZero : coloring 25 ≠ 0 := by
    intro hzero
    exact hvalid.1 18 25 (by decide) (hcenter.trans hzero.symm)
  have hnotThree : coloring 25 ≠ 3 := by
    intro hthree
    exact hvalid.1 25 31 (by decide) (hthree.trans hb.symm)
  generalize hanchor : coloring 25 = anchor
  fin_cases anchor
  · exact hnotZero hanchor
  · exact PartsGadgetCaseTree.not_colorable
      partsGadgetHardCaseTree partsGadgetHardCertificates
      partsGadgetHardCaseTree_verifiesRouting
      partsGadgetHardCertificates_verify hvalid
      (partsGadgetHardRoots ha hb hcenter hanchor)
  · let renamed := fun vertex => partsGadgetSwapOneTwo (coloring vertex)
    have hvalid' : PartsGadgetValid renamed := hvalid.rename partsGadgetSwapOneTwo
    apply PartsGadgetCaseTree.not_colorable
      partsGadgetHardCaseTree partsGadgetHardCertificates
      partsGadgetHardCaseTree_verifiesRouting
      partsGadgetHardCertificates_verify hvalid'
    exact partsGadgetHardRoots (coloring := renamed)
      (by simp [renamed, ha]) (by simp [renamed, hb])
      (by simp [renamed, hcenter]) (by simp [renamed, hanchor])
  · exact hnotThree hanchor

lemma no_partsGadget_coloring_of_middle_roots {coloring : Fin 73 → Fin 4}
    (hvalid : PartsGadgetValid coloring) (ha : coloring 5 = 0)
    (hb : coloring 31 = 3) (hcenter : coloring 18 = 1) : False := by
  exact partsGadgetMiddleCertificate.not_colorable
    partsGadgetMiddleCertificate_verifies hvalid
    (partsGadgetMiddleRoots ha hb hcenter)

lemma no_partsGadget_coloring_of_normalized_endpoints
    {coloring : Fin 73 → Fin 4} (hvalid : PartsGadgetValid coloring)
    (ha : coloring 5 = 0) (hb : coloring 31 = 3) : False := by
  generalize hcenter : coloring 18 = center
  fin_cases center
  · exact no_partsGadget_coloring_of_hard_roots hvalid ha hb hcenter
  · exact no_partsGadget_coloring_of_middle_roots hvalid ha hb hcenter
  · let renamed := fun vertex => partsGadgetSwapOneTwo (coloring vertex)
    have hvalid' : PartsGadgetValid renamed := hvalid.rename partsGadgetSwapOneTwo
    apply no_partsGadget_coloring_of_middle_roots hvalid'
    · simp [renamed, ha]
    · simp [renamed, hb]
    · simp [renamed, hcenter]
  · let reflected := fun vertex =>
      partsGadgetSwapZeroThree (coloring (partsGadgetNegation vertex))
    have hvalid' : PartsGadgetValid reflected :=
      hvalid.negation.rename partsGadgetSwapZeroThree
    have hcenter' : coloring 18 = 3 := by simpa using hcenter
    apply no_partsGadget_coloring_of_hard_roots hvalid'
    · norm_num [reflected, partsGadgetNegation, hb]
    · norm_num [reflected, partsGadgetNegation, ha]
    · norm_num [reflected, partsGadgetNegation, hcenter']

/-- The finite Parts gadget forces its opposite distance-four pair to be
monochromatic under the unit-edge and non-mono-triple constraints. -/
theorem parts_gadget_forces_monochromatic_pair
    {coloring : Fin 73 → Fin 4} (hvalid : PartsGadgetValid coloring) :
    coloring 5 = coloring 31 := by
  by_contra hne
  let rename := partsColorEquiv (coloring 5) (coloring 31)
  have hspec := partsColorEquiv_spec hne
  have hvalid' : PartsGadgetValid (fun vertex => rename (coloring vertex)) :=
    hvalid.rename rename
  exact no_partsGadget_coloring_of_normalized_endpoints hvalid' hspec.1 hspec.2

end HadwigerNelsonBounds
