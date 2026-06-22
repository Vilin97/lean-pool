/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import LeanPool.SetTheory.ElementaryEmbedding

/-!
# The Kunen inconsistency theorem

This module proves the Kunen inconsistency theorem: there is no nontrivial elementary
embedding of the universe of sets into itself.
-/

noncomputable section

open Function Cardinal

namespace SetTheory

private lemma mk_Iio_ToType_lt {c : Cardinal} (i : c.ord.ToType) : #(Set.Iio i) < c := by
  simpa using mk_Iio_lt i

/-- The `IsOmegaJonssonFunc` declaration. -/
@[realize] def IsOmegaJonssonFunc {M₀} [ZFStructure M₀] [IsVonNeumannWithOmega M₀] (f κ : M₀) :=
  f ∈ Func (Func ωₘ κ) κ ∧ ∀ X ⊆ κ, cardEq X κ → ∀ α ∈ κ, ∃ s ∈ Func ωₘ X, apply f s = α

/-- The `KunenBoundParams` type. -/
class KunenBoundParams where
  /-- The `M` declaration. -/
  M : Type 1
  /-- The `structureM` declaration. -/
  structureM : ZFStructure M
  /-- The `isVonNeumann` declaration. -/
  isVonNeumann : IsVonNeumann M
  /-- The `j` declaration. -/
  j : NontrivialElementaryEmbedding M
  bddAbove_crit_iter : BddAbove (Set.range (j^[·] (crit j)))

namespace KunenBoundParams

variable [KunenBoundParams]

open KunenBoundParams

instance : ZFStructure M := structureM
instance : IsVonNeumannWithOmega M := hasOmegaOfNontrivialSelfEmbedding (hM := isVonNeumann) j

/-- The `κ` declaration. -/
def κ n := j^[n] (crit j)
/-- The `κω` declaration. -/
def κω : M := ⨆ n : ℕ, κ n
/-- The `κωEquinumerousSubsets` declaration. -/
def κωEquinumerousSubsets := {x : M // x ⊆ κω ∧ #x = #κω}
/-- The `ν` declaration. -/
def ν := (#(κω × κωEquinumerousSubsets)).ord
/-- The `γX` declaration. -/
def γX : ν.ToType ≃ κω × κωEquinumerousSubsets := Cardinal.eq.mp (mk_ord_toType _) |>.some
/-- The `γ` declaration. -/
def γ (α : ν.ToType) : M := (γX α).1.1
/-- The `X` declaration. -/
def X (α : ν.ToType) : M := (γX α).2.1

lemma γ_mem_κω (α : ν.ToType) : γ α ∈ κω := (γX α).1.2
lemma X_subset_κω (α : ν.ToType) : X α ⊆ κω := (γX α).2.2.1
lemma card_X_eq_card_κω (α : ν.ToType) : #(X α) = #κω := (γX α).2.2.2

lemma card_ωₘ : #(ωₘ : M) = ℵ₀ := by
  have := (omegaEquiv (M₀ := M)).lift_cardinal_eq
  rwa [mk_nat, Cardinal.lift_id', lift_aleph0] at this

/-- The `injSubset` declaration. -/
def injSubset {A B : M} (hsub : A ⊆ B) : A ↪ B := {
  toFun := fun | ⟨x, hx⟩ => ⟨x, hsub hx⟩,
  inj' := by simp [Injective]
}

lemma card_le_of_sub {A B : M} (hsub : A ⊆ B) : #A ≤ #B :=
  (Cardinal.le_def ..).mpr ⟨injSubset hsub⟩

lemma bddAbove_ordinal_κ :
    BddAbove (Set.range fun n => (⟨κ n, isOrdinal_crit_iter _⟩ : Ordinals M)) := by
  rw [← comOrdinals.bddAbove_iff]
  convert bddAbove_crit_iter using 1
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  rfl

lemma κω_eq_ordinal_sSup : κω = (⨆ n : ℕ, (⟨κ n, isOrdinal_crit_iter _⟩ : Ordinals M)).1 := by
  rw [κω, comOrdinals.map_iSup Subtype.val]
  exact bddAbove_ordinal_κ

lemma κ_mem_κω (n : ℕ) : κ n ∈ κω := by
  erw [show κ n = (⟨κ n, isOrdinal_crit_iter _⟩ : Ordinals M).1 from rfl,
    κω_eq_ordinal_sSup, IsOrdinal.mem_iff_lt (Subtype.property _) (Subtype.property _),
    Subtype.coe_lt_coe, lt_ciSup_iff bddAbove_ordinal_κ]
  refine ⟨n + 1, ?_⟩
  erw [Subtype.mk_lt_mk, ← IsOrdinal.mem_iff_lt (isOrdinal_crit_iter _) (isOrdinal_crit_iter _)]
  exact crit_iter_mem_succ n

lemma κ_le_κω (n : ℕ) : κ n ≤ κω := le_csSup bddAbove_crit_iter ⟨n, rfl⟩

lemma aleph0_le_κω : ℵ₀ ≤ #κω := by
  simpa only [← card_ωₘ, κω] using card_le_of_sub (le_trans ωₘ_le_crit (κ_le_κω 0))

/-- The `i` declaration. -/
def i {n} : (𝓟 (κ n) : M) ↪ κω :=
  Nonempty.some <| show Nonempty ((𝓟 (κ n) : M) ↪ κω) by
    rw [← Cardinal.le_def]
    refine le_of_lt (lt_of_lt_of_le ?_ (card_le_of_sub (κ_le_κω (n + 1))))
    rw [← cardLT_iff]
    exact (isStrongLimit_crit_iter (n + 1)).2 (κ n) (crit_iter_mem_succ _)

@[simp] lemma inter_sub_left {x y : M} : x ∩ y ⊆ x := by simp [Subset]; tauto
@[simp] lemma inter_sub_right {x y : M} : x ∩ y ⊆ y := by simp [Subset]

lemma isOrdinal_κω : IsOrdinal κω := by
  rw [κω_eq_ordinal_sSup]
  exact Subtype.property _

lemma exists_lt_κ {α : M} (hα : α ∈ κω) : ∃ n, α < κ n := by
  have ord_α := isOrdinal_κω.mem hα
  rw [ord_α.mem_iff_lt isOrdinal_κω, κω_eq_ordinal_sSup,
    show α = (⟨α, ord_α⟩ : Ordinals M).1 from rfl, Subtype.coe_lt_coe] at hα
  obtain ⟨_, ⟨⟨n, ⟨_⟩⟩, hn⟩⟩ := exists_lt_of_lt_csSup' hα
  exact ⟨n, hn⟩

lemma card_κωEquinumerousSubsets_le : #κωEquinumerousSubsets ≤ #↥κω ^ ℵ₀ := by
  conv_rhs =>
    rw [← Cardinal.lift_id'.{0, 1} (#_), ← Cardinal.lift_aleph0.{1, 0}, ← mk_nat, ← mk_arrow]
  rw [Cardinal.le_def]
  have hsub : ∀ (X : M) n, X ∩ κ n ∈ (𝓟 (κ n) : M) := fun X n => by
    simp only [powerset.spec, Subset, Inter.inter.spec]; tauto
  refine ⟨⟨fun | ⟨X, hX⟩, n => i (⟨X ∩ κ n, hsub X n⟩ : (𝓟 (κ n) : M)), ?_⟩⟩
  intro ⟨X, hX⟩ ⟨Y, hY⟩ eq
  simp only [funext_iff, EmbeddingLike.apply_eq_iff_eq, Subtype.ext_iff] at eq
  apply Subtype.ext
  refine ext_of_subset hX.1 hY.1 fun x hx => ?_
  obtain ⟨n, hn⟩ := exists_lt_κ hx
  simp only [SetTheory.ext_iff, Inter.inter.spec, and_congr_left_iff] at eq
  erw [← (isOrdinal_κω.mem hx).mem_iff_lt (isOrdinal_crit_iter n)] at hn
  exact eq n _ hn

instance : Nonempty κω := by
  rw [← mk_ne_zero_iff]
  intro eq
  have := aleph0_le_κω
  simp only [eq, nonpos_iff_eq_zero] at this
  exact Cardinal.aleph0_ne_zero this

instance : Nonempty κωEquinumerousSubsets := ⟨κω, subset_refl _, rfl⟩
instance : Nonempty (ν.ToType) := by simp [ν]

/-- The `s` declaration. -/
def s (α : ν.ToType) : ℕ → κω := by
  have s' (β : Set.Iio α) : ℕ → κω := s β.1
  suffices {x : ℕ → κω | (∀ n, ↑(x n) ∈ X α) ∧ ∀ β, s' β ≠ x}.Nonempty from this.some
  convert_to ({x : ℕ → κω | ∀ n, ↑(x n) ∈ X α} \ Set.range s').Nonempty using 1
  · ext x; simp
  · apply sdiff_nonempty_of_mk_lt_mk
    refine lt_of_le_of_lt mk_range_le ?_
    refine lt_of_lt_of_le (mk_Iio_ToType_lt _) ?_
    have equivType : {x : ℕ → κω | ∀ n, ↑(x n) ∈ X α} ≃ (ℕ → X α) := {
      toFun := fun | ⟨x, hx⟩, n => ⟨x n, hx n⟩,
      invFun := fun | x => ⟨fun n => ⟨↑(x n), X_subset_κω _ (x n).2⟩, fun n => (x n).2⟩,
    }
    rw [← mul_def, equivType.cardinal_eq, mk_arrow,
      card_X_eq_card_κω, mk_nat, Cardinal.lift_id', lift_aleph0,
      mul_eq_max_of_aleph0_le_left aleph0_le_κω (mk_ne_zero _),
      sup_le_iff, and_iff_right (self_le_power _ (by simp))]
    exact card_κωEquinumerousSubsets_le
termination_by α
decreasing_by exact β.2

lemma injective_s : Injective s := by
  intro α β s_eq
  wlog lt : α < β
  · by_cases! eq : α = β
    · exact eq
    · exact this s_eq.symm (lt_of_le_of_ne (not_lt.mp lt) eq.symm) |>.symm
  · nth_rw 2 [s] at s_eq
    generalize_proofs hβ at s_eq
    dsimp only at hβ
    exact (hβ.some_mem.2 ⟨_, lt⟩ s_eq).elim

lemma s_mem_X : ∀ α n, (s α n).1 ∈ X α := by
  intro α n
  simp only [s]
  generalize_proofs hα
  exact hα.some_mem.1 n

/-- The `f` declaration. -/
def f (x : ℕ → κω) : κω := ⟨γ (s.invFun x), γ_mem_κω _⟩
/-- The `fSet` declaration. -/
def fSet : M := funcToSet fun x => f (setToFunc x ∘ omegaEquiv.symm)

lemma fSet_mem : fSet ∈ Func (Func ωₘ κω) κω :=
  (funcEquiv.symm fun x => f (funcEquiv x ∘ omegaEquiv.symm)).2

lemma funcToSet_subset {A B C : M} {f : A → B} (hsub : B ⊆ C) :
    funcToSet f = funcToSet (injSubset hsub ∘ f) := by
  ext x
  simp only [funcToSet, mem_separate_iff, Pairs.spec, injSubset, Embedding.coeFn_mk, comp_apply,
    and_congr_left_iff, and_congr_right_iff, forall_exists_index]
  rintro fst_mem f_apply_eq ⟨x, y, ⟨_⟩⟩ -
  revert fst_mem f_apply_eq
  simp only [fst_pair, snd_pair]
  rintro hx (⟨_⟩ : (f ⟨x, hx⟩).1 = y)
  exact ⟨fun _ => hsub (f ⟨x, hx⟩).2, fun _ => (f ⟨x, hx⟩).2⟩

lemma funcToSet_mem_Func_of_subset {A B C : M} {f : A → B} (hsub : B ⊆ C) :
    funcToSet f ∈ Func A C := by
  rw [funcToSet_subset hsub]
  exact funcToSet_mem_Func _

lemma exists_γ_and_X_eq {β H : M} (hβ : β ∈ κω) (hH : H ⊆ κω) (card_eq : #H = #κω) :
    ∃ α, γ α = β ∧ X α = H := by
  use γX.symm (⟨β, hβ⟩, ⟨H, hH, card_eq⟩)
  simp [γ, X]

lemma f_s_eq_γ {α : ν.ToType} : ↑(f (s α)) = γ α := by
  rw [f, s]
  generalize_proofs hne_ν hne_s γ_mem
  dsimp only
  congr 1
  suffices s α = hne_s.some by
    apply_fun s
    · rwa [Function.invFun_eq ⟨_, this⟩, eq_comm]
    · exact injective_s
  rw [s]

lemma is_omega_jonsson_fSet : IsOmegaJonssonFunc fSet κω := by
  refine ⟨fSet_mem, fun H H_sub_κω card_eq α α_lt_κω => ?_⟩
  simp_rw [exists_func, fSet,
    apply_funcToSet _ (funcToSet_mem_Func_of_subset H_sub_κω),
    funcToSet_subset H_sub_κω, setToFunc_funcToSet]
  suffices ∃ g, f ((injSubset H_sub_κω) ∘ g) = α by
    rcases this with ⟨g, hg⟩
    refine ⟨g ∘ omegaEquiv, ?_⟩
    simpa [comp_assoc] using hg
  rw [cardEq_iff] at card_eq
  obtain ⟨α, ⟨_⟩, ⟨_⟩⟩ := exists_γ_and_X_eq α_lt_κω H_sub_κω card_eq
  exact ⟨fun n => ⟨s α n, s_mem_X α n⟩, f_s_eq_γ⟩

/-- The `κFunc` declaration. -/
def κFunc (n : ℕ) : κω := ⟨κ n, κ_mem_κω _⟩
/-- The `κFuncSet` declaration. -/
def κFuncSet := funcToSet (κFunc ∘ omegaEquiv)

lemma iUnion_κ_funcSet_eq : iUnion κFuncSet = κω := by
  simp only [κFuncSet, iUnion_funcToSet, ← Equiv.iSup_comp omegaEquiv.symm, comp_apply,
    Equiv.apply_symm_apply]
  rfl

lemma j_κFuncSet : j κFuncSet = funcToSet (κFunc ∘ Nat.succ ∘ omegaEquiv) := by
  have : IsFunc κFuncSet := ((Func.spec ..).mp (funcToSet_mem_Func _)).1
  apply ext_func (by simpa only [elementary_simps])
    (((Func.spec ..).mp (funcToSet_mem_Func _)).1)
    (by simp [κFuncSet, elementary_simps, ← ωₘ.elementarity])
  intro α hα
  simp only [κFuncSet, elementary_simps, dom_funcToSet, ← ωₘ.elementarity, ωₘ.spec] at hα
  obtain ⟨n, ⟨_⟩⟩ := eq_natCast_of_memOmega hα
  clear hα
  rw [← j_natCast (j := j), apply.elementarity, κFuncSet, apply_funcToSet _ (by simp),
    apply_funcToSet _ (by simp [j_natCast])]
  simp only [comp_apply, κFunc, Nat.succ_eq_add_one, j_natCast]
  erw [omegaEquiv.apply_symm_apply, κ, κ, iterate_succ_apply']

lemma j_κω : j κω = κω := by
  simp only [← iUnion_κ_funcSet_eq, elementary_simps_rev, j_κFuncSet]
  simp only [κFuncSet, iUnion_funcToSet, ← sSup_range]
  convert_to sSup (Set.range (κ ∘ Nat.succ)) = sSup (Set.range κ) using 2
  · ext x
    simp [κFunc, omegaEquiv.exists_congr_left]
  · ext x
    simp [κFunc, omegaEquiv.exists_congr_left]
  · have eq_insert : Set.range κ = Insert.insert (κ 0) (Set.range (κ ∘ Nat.succ)) := by
      ext x
      simpa [eq_comm] using (Nat.or_exists_add_one (p := fun n => κ n = x)).symm
    have bdd_κ_comp_succ : BddAbove (Set.range (κ ∘ Nat.succ)) := by
      refine bddAbove_crit_iter.mono fun | x, ⟨n, hn⟩ => ?_
      simpa using ⟨n + 1, hn⟩
    rw [eq_insert, csSup_insert bdd_κ_comp_succ, right_eq_sup]
    · exact le_trans (le_of_lt (crit_iter_lt_succ 0)) (le_csSup bdd_κ_comp_succ ⟨0, rfl⟩)
    · simp [Set.range_nonempty]

/-- The `H` declaration. -/
def H : M := separate κω (fun x => x ∈ Set.range j)

lemma coeSort_H_iff : (H : Sort _) = j '' (κω : Set M) := by
  congr 1
  ext x
  have hsep : x ∈ H ↔ x ∈ κω ∧ x ∈ Set.range ⇑j := mem_separate_iff x
  rw [Set.mem_image]
  constructor
  · intro hxH
    obtain ⟨hx, y, eq⟩ := hsep.mp hxH
    rw [← eq, ← j_κω, Membership.mem.elementarity] at hx
    exact ⟨y, hx, eq⟩
  · rintro ⟨y, hy, eq⟩
    refine hsep.mpr ⟨?_, y, eq⟩
    rw [← eq, ← j_κω, Membership.mem.elementarity]
    exact hy

lemma crit_in_range_j_f : ∃ x ∈ Func ωₘ H, apply (j fSet) x = κ 0 := by
  have : IsOmegaJonssonFunc (j fSet) (j κω) := by
    simpa only [elementary_simps] using is_omega_jonsson_fSet
  rw [j_κω] at this
  refine this.2 H separate_sub ?_ (κ 0) (κ_mem_κω _)
  rw [cardEq_iff, coeSort_H_iff, mk_image_eq (f := j) j.toElementaryEmbedding.injective]
  rfl

lemma crit_not_in_range_j_f : ∀ x ∈ Func ωₘ H, apply (j fSet) x ≠ κ 0 := by
  rw [forall_func]
  intro f
  have (n : (ωₘ : M)) : ∃ α : κω, j α = f n := by
    have := (mem_separate_iff _).mp (f n).2
    rcases this with ⟨hf, α, hα⟩
    refine ⟨⟨α, ?_⟩, hα⟩
    rwa [← hα, ← j_κω, Membership.mem.elementarity] at hf
  choose g hg using this
  have : funcToSet f = j (funcToSet g) := by
    apply ext_func isFunc_funcToSet
      (by simpa only [elementary_simps] using isFunc_funcToSet)
      (by simp [elementary_simps, ← ωₘ.elementarity])
    intro n hn
    rw [dom_funcToSet] at hn
    rw [apply_funcToSet _ hn]
    conv_rhs => rw [← j_eq_of_mem_ωₛ (j₀ := j) hn, apply.elementarity, apply_funcToSet _ hn]
    exact (hg _).symm
  rw [this, apply.elementarity]
  exact j_ne_crit

theorem kunen_inconsistency : False := by
  apply absurd crit_in_range_j_f
  simpa using crit_not_in_range_j_f

end KunenBoundParams

open FirstOrder Language Order ZFSet

theorem kunen_inconsistency_vonNeumann
    (μ : Ordinal.{0}) [Fact (IsSuccLimit μ)]
    (j : NontrivialElementaryEmbedding (V_ μ)) :
    ⨆ n : ℕ, toOrdinal ⟨j^[n] (crit j), isOrdinal_crit_iter n⟩ = μ := by
  set! κ : ℕ → Ordinals (V_ μ) := fun n => ⟨j^[n] (crit j), isOrdinal_crit_iter n⟩ with hκ
  rw [funext_iff] at hκ
  simp only [← hκ]
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun n => le_of_lt ?_) (fun α hα => ?_)
  · simpa only [maxOrdinal_vonNeumann, WithTop.coe_lt_coe] using toOrdinal_lt (α := κ n)
  · by_contra! h
    letI params : KunenBoundParams := {
      M := V_ μ
      structureM := by infer_instance
      isVonNeumann := by infer_instance
      j := j
      bddAbove_crit_iter := ?_
    }
    · exact params.kunen_inconsistency
    · rw [show (Set.range fun n => (κ n).1) = (·.1) '' Set.range κ by
        rw [← Set.range_comp]; rfl, comOrdinals.bddAbove_iff]
      rw [← WithTop.coe_lt_coe, ← maxOrdinal_vonNeumann (μ := μ)] at hα
      obtain ⟨β, hβ⟩ := exists_toOrdinal_eq hα
      use β
      conv at h => enter [n]; rw [← hβ, toOrdinal.le_iff_le]
      simpa [upperBounds]

theorem kunen_inconsistency_V (j : V ↪ₑ[𝓛ZF] V) : j = .refl .. := by
  by_contra! hj
  let j' : NontrivialElementaryEmbedding V := ⟨j, hj⟩
  set! κ : ℕ → V := fun n => j'^[n] (crit j') with hκ
  rw [funext_iff] at hκ
  letI params : KunenBoundParams := {
    M := V
    structureM := by infer_instance
    isVonNeumann := by infer_instance
    j := j'
    bddAbove_crit_iter := ?_
  }
  · exact params.kunen_inconsistency
  · use ↓(⋃ n : ℕ, ⇓(κ n))
    simpa [upperBounds, toZFSet_simps] using ZFSet.subset_iUnion _

end SetTheory
