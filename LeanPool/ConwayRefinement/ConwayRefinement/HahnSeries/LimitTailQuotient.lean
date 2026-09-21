/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.Module.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.OrderedAddGroup
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Ordered common-tail quotients

A family of finite Archimedean classes determines a common convex rational subspace. Its quotient
is ordered by representatives and carries its order topology and right uniformity. These are the
explicit Hahn exponent quotients used in the limit hypothesis of the standalone Conway theorem.
-/

open Set

universe u

public noncomputable section

namespace FiniteArchimedeanClass

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G]

/-- The ordered rational quotient by the common tail of a family of finite Archimedean
classes. -/
abbrev TailQuotient (T : Set (FiniteArchimedeanClass G)) := G ⧸ tailSubmodule ℚ T

noncomputable instance tailQuotientLinearOrder (T : Set (FiniteArchimedeanClass G)) :
    LinearOrder (TailQuotient T) :=
  ConvexQuotient.instLinearOrder (H := (tailSubmodule ℚ T).toAddSubgroup)

instance tailQuotientIsOrderedAddMonoid (T : Set (FiniteArchimedeanClass G)) :
    IsOrderedAddMonoid (TailQuotient T) :=
  ConvexQuotient.instIsOrderedAddMonoid (H := (tailSubmodule ℚ T).toAddSubgroup)

instance tailQuotientPosSMulMono (T : Set (FiniteArchimedeanClass G)) :
    PosSMulMono ℚ (TailQuotient T) where
  smul_le_smul_of_nonneg_left q hq x y hxy := by
    change ∃ a b : G, Submodule.Quotient.mk a = x ∧
      Submodule.Quotient.mk b = y ∧ a ≤ b at hxy
    obtain ⟨a, b, ha, hb, hab⟩ := hxy
    change ∃ a b : G, Submodule.Quotient.mk a = q • x ∧
      Submodule.Quotient.mk b = q • y ∧ a ≤ b
    refine ⟨q • a, q • b, ?_, ?_, smul_le_smul_of_nonneg_left hab hq⟩
    · simpa only [Submodule.Quotient.mk_smul] using congrArg (q • ·) ha
    · simpa only [Submodule.Quotient.mk_smul] using congrArg (q • ·) hb

instance tailQuotientPosSMulStrictMono (T : Set (FiniteArchimedeanClass G)) :
    PosSMulStrictMono ℚ (TailQuotient T) := PosSMulMono.toPosSMulStrictMono

noncomputable instance tailQuotientTopologicalSpace (T : Set (FiniteArchimedeanClass G)) :
    TopologicalSpace (TailQuotient T) := Preorder.topology (TailQuotient T)

instance tailQuotientOrderTopology (T : Set (FiniteArchimedeanClass G)) :
    OrderTopology (TailQuotient T) := ⟨rfl⟩

instance tailQuotientDenselyOrdered (T : Set (FiniteArchimedeanClass G)) :
    DenselyOrdered (TailQuotient T) := by
  constructor
  intro a b hab
  refine ⟨(2 : ℚ)⁻¹ • (a + b), ?_, ?_⟩
  · calc
      a = (2 : ℚ)⁻¹ • (a + a) := by rw [smul_add, ← add_smul]; norm_num
      _ < (2 : ℚ)⁻¹ • (a + b) := smul_lt_smul_of_pos_left
        (add_lt_add_left hab a |>.trans_eq (add_comm _ _)) (by norm_num)
  · calc
      (2 : ℚ)⁻¹ • (a + b) < (2 : ℚ)⁻¹ • (b + b) :=
        smul_lt_smul_of_pos_left
          (by simpa [add_comm] using add_lt_add_left hab b) (by norm_num)
      _ = b := by rw [smul_add, ← add_smul]; norm_num

instance tailQuotientIsTopologicalAddGroup (T : Set (FiniteArchimedeanClass G)) :
    IsTopologicalAddGroup (TailQuotient T) where
  toContinuousAdd := continuousAdd_of_orderTopology (TailQuotient T)
  toContinuousNeg := continuousNeg_of_orderTopology (TailQuotient T)

noncomputable instance tailQuotientUniformSpace (T : Set (FiniteArchimedeanClass G)) :
    UniformSpace (TailQuotient T) :=
  IsTopologicalAddGroup.rightUniformSpace (TailQuotient T)

instance tailQuotientIsUniformAddGroup (T : Set (FiniteArchimedeanClass G)) :
    IsUniformAddGroup (TailQuotient T) := isUniformAddGroup_of_addCommGroup

/-- Absolute value commutes with projection to a rational tail quotient. -/
theorem tailQuotient_abs (T : Set (FiniteArchimedeanClass G)) (x : G) :
    |(Submodule.Quotient.mk x : TailQuotient T)| = Submodule.Quotient.mk |x| := by
  rcases le_total 0 x with hx | hx
  · have hxq : (0 : TailQuotient T) ≤ Submodule.Quotient.mk x := by
      rw [← Submodule.Quotient.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonneg hx, abs_of_nonneg hxq]
  · have hxq : (Submodule.Quotient.mk x : TailQuotient T) ≤ 0 := by
      rw [← Submodule.Quotient.mk_zero]
      exact ConvexQuotient.mk_le_mk hx
    rw [abs_of_nonpos hx, abs_of_nonpos hxq, ← Submodule.Quotient.mk_neg]

/-- A strict class comparison in a rational tail quotient reflects to representatives. -/
theorem archimedeanClass_mk_lt_of_tailQuotient_mk_lt
    (T : Set (FiniteArchimedeanClass G)) {x y : G}
    (h : ArchimedeanClass.mk (Submodule.Quotient.mk x : TailQuotient T) <
      ArchimedeanClass.mk (Submodule.Quotient.mk y : TailQuotient T)) :
    ArchimedeanClass.mk x < ArchimedeanClass.mk y := by
  rw [ArchimedeanClass.mk_lt_mk] at h ⊢
  intro n
  have hn := h n
  have hn' : (Submodule.Quotient.mk (n • |y|) : TailQuotient T) <
      Submodule.Quotient.mk |x| := by
    have heq : (Submodule.Quotient.mk (n • |y|) : TailQuotient T) =
        n • Submodule.Quotient.mk |y| := by
      change QuotientAddGroup.mk' _ (n • |y|) = n • QuotientAddGroup.mk' _ |y|
      exact map_nsmul (QuotientAddGroup.mk' _) n |y|
    rw [heq]
    simpa only [tailQuotient_abs] using hn
  exact ConvexQuotient.lt_of_mk_lt_mk hn'

/-- Canonical representatives of a limit family are coinitial in its rational tail quotient. -/
theorem exists_tailQuotient_positiveRepresentative_le
    {T : Set (FiniteArchimedeanClass G)}
    {x : TailQuotient T} (hx : 0 < x) :
    ∃ c : T, (Submodule.Quotient.mk (positiveRepresentative c.1) : TailQuotient T) ≤ x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have hxq : (Submodule.Quotient.mk (0 : G) : TailQuotient T) <
        Submodule.Quotient.mk x := by
      simpa using hx
    have hx0 : 0 < x := ConvexQuotient.lt_of_mk_lt_mk hxq
    have hxP : x ∉ tailSubmodule ℚ T := by
      simpa using (ConvexQuotient.mk_lt_mk_iff.mp hxq).2
    rw [mem_tailSubmodule_iff, mem_tailKernel_iff] at hxP
    push Not at hxP
    obtain ⟨c, hxc⟩ := hxP
    refine ⟨c, ConvexQuotient.mk_le_mk ?_⟩
    apply (ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ hx0.le).le
    rwa [mk_positiveRepresentative]

end FiniteArchimedeanClass
