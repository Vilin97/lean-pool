/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
/-!
# Ray moduli with selected real places

A ray modulus consists of a finite modulus together with the real places at
which positivity is imposed.  This file defines the corresponding idèle and
idèle-class congruence subgroups without fixing an archimedean convention.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

open scoped Classical in
/-- A real infinite place of a number field. -/
abbrev RealPlace (K : Type*) [Field K] :=
  {v : InfinitePlace K // v.IsReal}

open scoped Classical in
/-- A ray modulus consists of its finite part and the selected real places
at which the positivity condition is imposed. -/
structure Modulus (K : Type*) [Field K] [NumberField K] where
  /-- The finite prime-power part of the modulus. -/
  finitePart : FiniteModulus K
  /-- The real places at which positivity is imposed. -/
  infinitePart : Finset (RealPlace K)

namespace Modulus

open scoped Classical in
/-- The full modulus with a prescribed finite part and no archimedean
positivity condition. -/
def ofFinite (m : FiniteModulus K) : Modulus K where
  finitePart := m
  infinitePart := ∅

open scoped Classical in
/-- The full modulus with a prescribed finite part and positivity at every
real place. -/
noncomputable def narrowOfFinite (m : FiniteModulus K) : Modulus K where
  finitePart := m
  infinitePart := Finset.univ

open scoped Classical in
instance : Zero (Modulus K) where
  zero := ofFinite 0

open scoped Classical in
@[simp]
theorem finitePart_ofFinite (m : FiniteModulus K) :
    (ofFinite m).finitePart = m :=
  rfl

open scoped Classical in
@[simp]
theorem infinitePart_ofFinite (m : FiniteModulus K) :
    (ofFinite m).infinitePart = ∅ :=
  rfl

open scoped Classical in
@[simp]
theorem finitePart_narrowOfFinite (m : FiniteModulus K) :
    (narrowOfFinite m).finitePart = m :=
  rfl

open scoped Classical in
@[simp]
theorem infinitePart_narrowOfFinite (m : FiniteModulus K) :
    (narrowOfFinite m).infinitePart = Finset.univ :=
  rfl

open scoped Classical in
@[simp]
theorem finitePart_zero :
    (0 : Modulus K).finitePart = 0 :=
  rfl

open scoped Classical in
@[simp]
theorem infinitePart_zero :
    (0 : Modulus K).infinitePart = ∅ :=
  rfl

open scoped Classical in
theorem ext {m n : Modulus K}
    (hfinite : m.finitePart = n.finitePart)
    (hinfinite : m.infinitePart = n.infinitePart) :
    m = n := by
  cases m
  cases n
  cases hfinite
  cases hinfinite
  rfl

open scoped Classical in
instance : LE (Modulus K) where
  le m n :=
    m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart

open scoped Classical in
@[simp]
theorem le_iff {m n : Modulus K} :
    m ≤ n ↔
      m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart :=
  Iff.rfl

open scoped Classical in
instance : PartialOrder (Modulus K) where
  le_refl m := ⟨le_rfl, fun _ hx => hx⟩
  le_trans m n p hmn hnp :=
    ⟨hmn.1.trans hnp.1, fun x hx => hnp.2 (hmn.2 hx)⟩
  le_antisymm m n hmn hnm :=
    ext (le_antisymm hmn.1 hnm.1) (by
      apply Finset.ext
      intro x
      exact ⟨fun hx => hmn.2 hx, fun hx => hnm.2 hx⟩)
open scoped Classical in
noncomputable instance : SemilatticeInf (Modulus K) where
  inf m n :=
    { finitePart := m.finitePart ⊓ n.finitePart
      infinitePart := m.infinitePart ∩ n.infinitePart }
  inf_le_left _ _ :=
    ⟨inf_le_left, fun _ hx => (Finset.mem_inter.mp hx).1⟩
  inf_le_right _ _ :=
    ⟨inf_le_right, fun _ hx => (Finset.mem_inter.mp hx).2⟩
  le_inf _ _ _ hmn hmp :=
    ⟨le_inf hmn.1 hmp.1,
      fun _ hx => Finset.mem_inter.mpr ⟨hmn.2 hx, hmp.2 hx⟩⟩

open scoped Classical in
noncomputable instance : SemilatticeSup (Modulus K) where
  sup m n :=
    { finitePart := m.finitePart ⊔ n.finitePart
      infinitePart := m.infinitePart ∪ n.infinitePart }
  le_sup_left _ _ :=
    ⟨le_sup_left, fun _ hx => Finset.mem_union.mpr (Or.inl hx)⟩
  le_sup_right _ _ :=
    ⟨le_sup_right, fun _ hx => Finset.mem_union.mpr (Or.inr hx)⟩
  sup_le _ _ _ hmp hnp :=
    ⟨sup_le hmp.1 hnp.1, fun _ hx => by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hmp.2 hx
      · exact hnp.2 hx⟩

open scoped Classical in
instance : Bot (Modulus K) where
  bot := 0

open scoped Classical in
instance : OrderBot (Modulus K) where
  bot_le _ := ⟨bot_le, Finset.empty_subset _⟩

open scoped Classical in
/-- Replace the finite part of a full modulus while retaining exactly its
selected real places. -/
def replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) : Modulus K where
  finitePart := f
  infinitePart := m.infinitePart

open scoped Classical in
@[simp]
theorem finitePart_replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) :
    (m.replaceFinitePart f).finitePart = f :=
  rfl

open scoped Classical in
@[simp]
theorem infinitePart_replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) :
    (m.replaceFinitePart f).infinitePart = m.infinitePart :=
  rfl

open scoped Classical in
/-- Remove the positivity condition at one real place. -/
noncomputable def eraseRealPlace
    (m : Modulus K) (v : RealPlace K) : Modulus K where
  finitePart := m.finitePart
  infinitePart := m.infinitePart.erase v

open scoped Classical in
@[simp]
theorem finitePart_eraseRealPlace
    (m : Modulus K) (v : RealPlace K) :
    (m.eraseRealPlace v).finitePart = m.finitePart :=
  rfl

open scoped Classical in
@[simp]
theorem infinitePart_eraseRealPlace
    (m : Modulus K) (v : RealPlace K) :
    (m.eraseRealPlace v).infinitePart = m.infinitePart.erase v :=
  rfl

open scoped Classical in
/-- Remove the positivity conditions at a finite set of real places. -/
noncomputable def eraseRealPlaces
    (m : Modulus K) (s : Finset (RealPlace K)) : Modulus K where
  finitePart := m.finitePart
  infinitePart := m.infinitePart \ s

open scoped Classical in
@[simp]
theorem finitePart_eraseRealPlaces
    (m : Modulus K) (s : Finset (RealPlace K)) :
    (m.eraseRealPlaces s).finitePart = m.finitePart :=
  rfl

open scoped Classical in
@[simp]
theorem infinitePart_eraseRealPlaces
    (m : Modulus K) (s : Finset (RealPlace K)) :
    (m.eraseRealPlaces s).infinitePart = m.infinitePart \ s :=
  rfl

open scoped Classical in
@[simp]
theorem eraseRealPlaces_empty (m : Modulus K) :
    m.eraseRealPlaces ∅ = m := by
  apply ext
  · rfl
  · exact Finset.sdiff_empty

open scoped Classical in
@[simp]
theorem eraseRealPlaces_insert
    (m : Modulus K) (s : Finset (RealPlace K)) (v : RealPlace K) :
    m.eraseRealPlaces (insert v s) =
      (m.eraseRealPlaces s).eraseRealPlace v := by
  apply ext
  · rfl
  · exact Finset.sdiff_insert _ _ _

open scoped Classical in
/-- The local infinite congruence condition at an infinite place.  It is the
positive subgroup exactly at a real place selected by the modulus, and the
whole local group otherwise. -/
noncomputable def localInfiniteCongruenceSubgroup (m : Modulus K)
    (w : InfinitePlace K) : Subgroup w.Completionˣ := by
  classical
  exact if hw : w.IsReal then
    if hmem : (⟨w, hw⟩ : RealPlace K) ∈ m.infinitePart then
      infinitePositiveSubgroup w
    else ⊤
  else ⊤

open scoped Classical in
@[simp]
theorem localInfiniteCongruenceSubgroup_replaceFinitePart
    (m : Modulus K) (f : FiniteModulus K) (w : InfinitePlace K) :
    (m.replaceFinitePart f).localInfiniteCongruenceSubgroup w =
      m.localInfiniteCongruenceSubgroup w := by
  rfl

open scoped Classical in
@[simp]
theorem localInfiniteCongruenceSubgroup_of_mem
    (m : Modulus K) (v : RealPlace K) (hv : v ∈ m.infinitePart) :
    m.localInfiniteCongruenceSubgroup v.1 = infinitePositiveSubgroup v.1 := by
  simp [localInfiniteCongruenceSubgroup, v.property, hv]

open scoped Classical in
@[simp]
theorem localInfiniteCongruenceSubgroup_of_not_mem
    (m : Modulus K) (v : RealPlace K) (hv : v ∉ m.infinitePart) :
    m.localInfiniteCongruenceSubgroup v.1 = ⊤ := by
  simp [localInfiniteCongruenceSubgroup, v.property, hv]

open scoped Classical in
@[simp]
theorem localInfiniteCongruenceSubgroup_of_not_isReal
    (m : Modulus K) (w : InfinitePlace K) (hw : ¬ w.IsReal) :
    m.localInfiniteCongruenceSubgroup w = ⊤ := by
  simp [localInfiniteCongruenceSubgroup, hw]

open scoped Classical in
/-- The subgroup of infinite idèles positive at the real places selected by
the modulus. -/
def infiniteCongruenceSubgroup (m : Modulus K) :
    Subgroup (InfiniteIdeleGroup K) :=
  Subgroup.comap ContinuousMulEquiv.piUnits.toMonoidHom
    (Subgroup.pi Set.univ (fun w => m.localInfiniteCongruenceSubgroup w))

open scoped Classical in
@[simp]
theorem mem_infiniteCongruenceSubgroup_iff_local
    (m : Modulus K) (a : InfiniteIdeleGroup K) :
    a ∈ m.infiniteCongruenceSubgroup ↔
      ∀ w, ContinuousMulEquiv.piUnits a w ∈ m.localInfiniteCongruenceSubgroup w := by
  change ContinuousMulEquiv.piUnits a ∈
      Subgroup.pi Set.univ (fun w => m.localInfiniteCongruenceSubgroup w) ↔ _
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]

open scoped Classical in
theorem mem_infiniteCongruenceSubgroup_iff
    (m : Modulus K) (a : InfiniteIdeleGroup K) :
    a ∈ m.infiniteCongruenceSubgroup ↔
      ∀ v : RealPlace K, v ∈ m.infinitePart →
        ContinuousMulEquiv.piUnits a v.1 ∈ infinitePositiveSubgroup v.1 :=
  by
    rw [mem_infiniteCongruenceSubgroup_iff_local]
    constructor
    · intro ha v hv
      have hlocal := ha v.1
      rw [localInfiniteCongruenceSubgroup_of_mem m v hv] at hlocal
      exact hlocal
    · intro ha w
      by_cases hw : w.IsReal
      · by_cases hmem : (⟨w, hw⟩ : RealPlace K) ∈ m.infinitePart
        · simpa [localInfiniteCongruenceSubgroup, hw, hmem] using
            ha ⟨w, hw⟩ hmem
        · simp [localInfiniteCongruenceSubgroup, hw, hmem]
      · simp [localInfiniteCongruenceSubgroup, hw]

open scoped Classical in
/-- Selecting every real place recovers the narrow infinite congruence
subgroup. -/
theorem infiniteCongruenceSubgroup_narrowOfFinite (f : FiniteModulus K) :
    (narrowOfFinite f).infiniteCongruenceSubgroup =
      narrowInfiniteCongruenceSubgroup (K := K) := by
  ext a
  rw [mem_infiniteCongruenceSubgroup_iff,
    mem_narrowInfiniteCongruenceSubgroup_iff]
  simp only [infinitePart_narrowOfFinite, Finset.mem_univ, true_implies]
  constructor
  · intro ha w
    by_cases hw : w.IsReal
    · exact ha ⟨w, hw⟩
    · rw [mem_infinitePositiveSubgroup_iff]
      exact fun hreal => (hw hreal).elim
  · intro ha v
    exact ha v.1

open scoped Classical in
/-- The idèle congruence subgroup attached to a full ray modulus. -/
def ideleCongruenceSubgroup (m : Modulus K) :
    Subgroup (IdeleGroup K) :=
  m.infiniteCongruenceSubgroup.prod
    (finiteCongruenceSubgroup m.finitePart)

open scoped Classical in
@[simp]
theorem mem_ideleCongruenceSubgroup_iff
    (m : Modulus K) (a : IdeleGroup K) :
    a ∈ m.ideleCongruenceSubgroup ↔
      a.1 ∈ m.infiniteCongruenceSubgroup ∧
        a.2 ∈ finiteCongruenceSubgroup m.finitePart :=
  Iff.rfl

open scoped Classical in
/-- Selecting every real place recovers the narrow idèle congruence subgroup. -/
theorem ideleCongruenceSubgroup_narrowOfFinite (f : FiniteModulus K) :
    (narrowOfFinite f).ideleCongruenceSubgroup =
      (narrowInfiniteCongruenceSubgroup (K := K)).prod
        (finiteCongruenceSubgroup f) := by
  simp only [ideleCongruenceSubgroup, finitePart_narrowOfFinite]
  rw [infiniteCongruenceSubgroup_narrowOfFinite]

open scoped Classical in
/-- The ray congruence subgroup of the idèle class group attached to a full
modulus. -/
def congruenceSubgroup (m : Modulus K) :
    Subgroup (IdeleClassGroup K) :=
  Subgroup.map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))
    (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K)

open scoped Classical in
/-- The full ray congruence subgroup is normal in the idèle class group. -/
instance congruenceSubgroup_normal (m : Modulus K) :
    m.congruenceSubgroup.Normal := by
  let : IsMulCommutative (IdeleClassGroup K) := ⟨⟨fun a b => mul_comm a b⟩⟩
  exact Subgroup.normal_of_isMulCommutative _

end Modulus

open scoped Classical in
/-- The ray class group attached to a full modulus. -/
abbrev RayClassGroup (m : Modulus K) :=
  IdeleClassGroup K ⧸ m.congruenceSubgroup

open scoped Classical in
/-- The ray class group is equivalently the idèle group modulo the product
of its congruence subgroup with the principal idèles. -/
def rayClassGroupEquivIdeleQuotient (m : Modulus K) :
    RayClassGroup m ≃*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K) :=
  QuotientGroup.quotientQuotientEquivQuotient
    (IdeleGroup.principalSubgroup K)
    (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K)
    le_sup_right

end RayClass
