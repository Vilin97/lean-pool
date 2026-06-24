/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import LeanPool.SetTheory.Omega

/-!
# Elementary embeddings of models of ZF

This module defines nontrivial elementary embeddings of a model of ZF into itself, their
critical points, and the basic properties of the iterates of the critical point.
-/

noncomputable section

open FirstOrder Language Function Ordinal SetTheory

variable {M M₀} [ZFStructure M] [ZFStructure M₀]

variable (M) in
/-- The `NontrivialElementaryEmbedding` type. -/
class NontrivialElementaryEmbedding extends M ↪ₑ[𝓛ZF] M where
  nontrivial' : toElementaryEmbedding ≠ .refl ..

namespace NontrivialElementaryEmbedding

variable {j k : NontrivialElementaryEmbedding M}

instance : FunLike (NontrivialElementaryEmbedding M) M M where
  coe j := j.toElementaryEmbedding
  coe_injective := by
    rintro ⟨j, hj⟩ ⟨k, hk⟩ eq
    congr 1
    simpa using eq

@[ext] lemma ext (eq : ∀ x, j x = k x) : j = k := by
  rcases j with ⟨j, hj⟩
  rcases k with ⟨j, hk⟩
  congr 1
  ext1 x
  exact eq x

instance : ElementaryEmbeddingClass (NontrivialElementaryEmbedding M) M M where
  map_formula j := j.toElementaryEmbedding.map_formula'

lemma nontrivial : ∃ x : M, j x ≠ x := by
  have := j.nontrivial'
  contrapose! this
  ext x
  exact this x

end NontrivialElementaryEmbedding

variable [hM : IsVonNeumann M] [hM₀ : IsVonNeumannWithOmega M₀]

namespace SetTheory

section BasicProperties

variable {F} [FunLike F M M] [ElementaryEmbeddingClass F M M] {j : F}
    {F₀} [FunLike F₀ M₀ M₀] [ElementaryEmbeddingClass F₀ M₀ M₀] {j₀ : F₀}

lemma IsOrdinal.le_j {α} (ord_α : IsOrdinal α) : α ≤ j α := by
  induction α using rank_induction with
  | _ α ind =>
    intro β hβ
    have ord_β := ord_α.mem hβ
    specialize ind β
    rw [rank_ordinal ord_α, rank_ordinal ord_β, ← ord_β.mem_iff_lt ord_α] at ind
    specialize ind hβ ord_β
    change β ∈ j α
    rw [ord_β.mem_iff_lt (by simpa only [elementary_simps])]
    change β ∈ α at hβ
    rw [ord_β.mem_iff_lt ord_α] at hβ
    exact lt_of_le_of_lt ind (by simpa only [elementary_simps])

lemma j_natCast (n : ℕ) : j (n : M) = (n : M) := by
  induction n with
  | zero => simp only [← ofNat_eq_natCast, natCast_zero, elementary_simps_rev]
  | succ n ih => simp only [natCast_succ, elementary_simps_rev, ih]

lemma j_eq_of_mem_ωₛ {α : M₀} (hα : α ∈ (ωₘ : M₀)) : j₀ α = α := by
  rw [ωₘ.spec] at hα
  obtain ⟨n, ⟨_⟩⟩ := eq_natCast_of_memOmega hα
  rw [j_natCast]

end BasicProperties

variable {j : NontrivialElementaryEmbedding M} {j₀ : NontrivialElementaryEmbedding M₀}

lemma crit_exists : ∃ α, IsOrdinal α ∧ j α ≠ α := by
  have hj := j.nontrivial
  contrapose! hj
  intro x
  induction x using rank_induction with
  | _ x ind =>
    ext1 y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have := rankAux.elementarity x j
      simp only [rankAux_eq_rank] at this
      have := ind _ (hj _ isOrdinal_rank ▸ this ▸ rank_mem hy)
      rwa [← this, Membership.mem.elementarity] at hy
    · rwa [← ind _ (rank_mem hy), Membership.mem.elementarity]

variable (j) in
/-- The `crit` declaration. -/
def crit : M := sInf {α : M | j α ≠ α ∧ IsOrdinal α}

lemma crit_eq_ordinal_sInf : crit j = (sInf {α : Ordinals M | j α ≠ α}).1 := by
  rw [crit, show {α | j α ≠ α ∧ IsOrdinal α} = (·.1) '' {α : Ordinals M | j α ≠ α} by ext; simp,
    ← comOrdinals.map_sInf']
  · obtain ⟨α, ord_α, hα⟩ := crit_exists (j := j)
    exact ⟨⟨α, ord_α⟩, hα⟩
  · exact OrderBot.bddBelow _

@[simp] lemma isOrdinal_crit : IsOrdinal (crit j) := by
  rw [crit_eq_ordinal_sInf]
  exact Subtype.property _

lemma j_crit_ne_crit : j (crit j) ≠ crit j := by
  rw [crit_eq_ordinal_sInf]
  refine csInf_mem (s := {α : Ordinals M | j α ≠ α}) ?_
  obtain ⟨α, ord, hα⟩ := crit_exists (j := j)
  exact ⟨⟨α, ord⟩, hα⟩

lemma crit_mem_j_crit : crit j ∈ j (crit j) := by
  rw [isOrdinal_crit.mem_iff_lt (by simp [elementary_simps, *]), lt_iff_le_and_ne]
  exact ⟨IsOrdinal.le_j (by simp [*]), j_crit_ne_crit.symm⟩

lemma j_eq_of_mem_crit {α} (hα : α ∈ crit j) : j α = α := by
  have ord_α := isOrdinal_crit.mem hα
  replace hα := notMem_of_lt_csInf (isOrdinal_crit.lt_of_mem hα) (by simp)
  simp only [ne_eq, Set.mem_setOf_eq, not_and, not_imp_not] at hα
  exact hα ord_α

lemma j_ne_crit {α} : j α ≠ crit j := by
  intro hα
  replace hα : j (rank α) = crit j := by
    apply_fun rank at hα
    conv_rhs at hα => rw [rank_ordinal isOrdinal_crit]
    rwa [← rankAux_eq_rank, ← rankAux.elementarity, rankAux_eq_rank]
  by_cases rank_cmp : rank α < crit j
  · rw [← isOrdinal_rank.mem_iff_lt isOrdinal_crit] at rank_cmp
    have := j_eq_of_mem_crit rank_cmp
    rw [hα] at this
    rw [isOrdinal_rank.mem_iff_lt isOrdinal_crit, ← this] at rank_cmp
    exact lt_irrefl _ rank_cmp
  · rw [← (IsOrdinal.not_le_iff isOrdinal_crit isOrdinal_rank).not_right,
      ← LE.le.elementarity (j := j)] at rank_cmp
    exact not_mem_self (hα ▸ rank_cmp crit_mem_j_crit)

lemma isStrongLimit_crit : IsStrongLimit (crit j) := by
  simp only [IsStrongLimit]
  set κ := crit j with κ_eq
  refine ⟨isOrdinal_crit, fun α hα => ?_⟩
  by_contra h
  simp only [cardLT_iff, not_lt] at h
  rcases h with ⟨⟨g, hg⟩⟩
  haveI inst₁ : Nonempty κ := by
    rw [nonempty_iff]
    intro hκ
    have := j_crit_ne_crit (j := j)
    rw [← κ_eq, hκ, ← EmptyCollection.emptyCollection.elementarity] at this
    simp at this
  have := invFun_surjective hg
  set f := invFun g
  clear_value f
  clear g hg inst₁
  have j_f_prop : ∃ j_f : j 𝓟 α → j κ, Surjective j_f ∧ funcToSet j_f = j (funcToSet f) := by
    have : j (funcToSet f) ∈ Func (j (𝓟 α)) (j κ) := by
      simp only [elementary_simps, funcToSet_mem_Func]
    use setToFunc ⟨_, this⟩
    have : Ran (j (funcToSet f)) = j κ := by
      simpa only [elementary_simps, ran_funcToSet_eq]
    simp only [← ran_funcToSet_eq, funcToSet_setToFunc, this, true_and]
  rw [← powerset.elementarity, j_eq_of_mem_crit hα] at j_f_prop
  rcases j_f_prop with ⟨j_f, surj, eq⟩
  have : ∀ x, j_f x = j (f x) := by
    intro ⟨x, hx⟩
    simp only [apply_funcToSet_rev, eq]
    have : j x = x := by
      change x ∈ 𝓟 α at hx
      simp only [powerset.spec] at hx
      have hj_x : j x ⊆ α := by rw [← j_eq_of_mem_crit hα]; simpa only [elementary_simps]
      refine ext_of_subset hj_x hx fun β hβ => ?_
      have := j_eq_of_mem_crit (isOrdinal_crit.1 hα hβ)
      rw [← this]
      conv_lhs => rw [← this]
      simp only [elementary_simps]
    conv_lhs => rw [← this]
    simp only [elementary_simps]
  obtain ⟨x, hx⟩ := surj ⟨_, crit_mem_j_crit⟩
  specialize this x
  simp only [hx] at this
  exact not_mem_self ((j_eq_of_mem_crit (f x).2 ▸ this).symm ▸ (f x).2)

lemma ωₘ_le_crit : ωₘ ≤ crit j₀ := by
  apply le_csInf
  · exact ⟨crit j₀, j_crit_ne_crit, isOrdinal_crit⟩
  · intro α ⟨hα, ord_α⟩
    contrapose! hα
    erw [isOrdinal_ωₘ.not_le_iff ord_α, ← ord_α.mem_iff_lt isOrdinal_ωₘ, ωₘ.spec] at hα
    obtain ⟨n, ⟨_⟩⟩ := eq_natCast_of_memOmega hα
    exact j_natCast _

lemma isOrdinal_crit_iter (n : ℕ) : IsOrdinal (j^[n] (crit j)) := by
  induction n with
  | zero => simp [*]
  | succ n ih => simpa only [iterate_succ_apply', elementary_simps]

lemma crit_iter_mem_succ (n : ℕ) : j^[n] (crit j) ∈ j^[n + 1] (crit j) := by
  induction n with
  | zero => simpa using crit_mem_j_crit
  | succ n ih =>
    conv_lhs => rw [iterate_succ_apply']
    conv_rhs => rw [iterate_succ_apply']
    simpa only [elementary_simps]

lemma crit_iter_lt_succ (n : ℕ) : j^[n] (crit j) < j^[n + 1] (crit j) := by
  rw [← (isOrdinal_crit_iter _).mem_iff_lt (isOrdinal_crit_iter _)]
  exact crit_iter_mem_succ _

lemma isStrongLimit_crit_iter (n : ℕ) : IsStrongLimit (j^[n] (crit j)) := by
  induction n with
  | zero => simpa using isStrongLimit_crit
  | succ n ih => simpa only [iterate_succ_apply', elementary_simps]

variable (j) in
/-- The `hasOmegaOfNontrivialSelfEmbedding` declaration. -/
@[reducible] def hasOmegaOfNontrivialSelfEmbedding : IsVonNeumannWithOmega M := by
  split_vonNeumann hM
  · suffices ω < μ from .vonNeumann μ hμ this rfl
    by_contra! μ_le_omega
    obtain ⟨_⟩ := le_antisymm μ_le_omega (omega0_le_of_isSuccLimit hμ)
    clear μ_le_omega
    apply absurd (crit_exists (j := j))
    simp only [ne_eq, not_exists, not_and, not_not]
    intro α hα
    obtain ⟨n, ⟨_⟩⟩ : ∃ n : ℕ, α = n := eq_natCast_of_memOmega <| by
      simp only [toZFSet_simps, ωₛ] at hα ⊢
      rw [← hα.rank_lt_iff_mem (ZFSet.isOrdinal_toZFSet _), rank_toZFSet,
        ← ZFSet.mem_vonNeumann]
      exact α.2
    exact (j_natCast _)
  · infer_instance

end SetTheory
