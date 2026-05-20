/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import LeanPool.Duality.ExtendedFields
import LeanPool.Duality.FarkasBasic


section notation_EF

/-- `F∞` is sugar for `Extend F`, the type of values in `F ∪ {⊥, ⊤}`. -/
syntax:max ident noWs "∞" : term

macro_rules
| `($F:ident∞) => `(Extend $F)

/-- Pretty-print `Extend F` back as `F∞`. -/
@[app_unexpander Extend]
def unexpandExtend : Lean.PrettyPrinter.Unexpander
| `($(_) $F:ident) => `($F:ident∞)
| _ => throw ()

end notation_EF


section nonnegative_subtype

/-- `NNeg F` is the subtype of nonnegative elements of `F`. -/
abbrev NNeg (F : Type*) [Zero F] [LE F] :=
  { a : F // 0 ≤ a }

/-- `F≥0` is sugar for `NNeg F`, the subtype of nonnegative elements of `F`. -/
syntax:max ident noWs "≥0" : term

macro_rules
| `($F:ident≥0) => `(NNeg $F)

/-- Pretty-print `NNeg F` back as `F≥0`. -/
@[app_unexpander NNeg]
def unexpandNNeg : Lean.PrettyPrinter.Unexpander
| `($(_) $F:ident) => `($F:ident≥0)
| _ => throw ()

end nonnegative_subtype


variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

section extras_EF

/-- Scalar action of a nonnegative scalar on `F∞`: `c • ⊥ = ⊥`, `c • ⊤ = ⊤` when `c > 0`
    (and `c • ⊤ = 0` when `c = 0`), and `c • (f : F) = c * f` on finite values. -/
def EF.smulNN (c : F≥0) : F∞ → F∞
| ⊥ => ⊥
| ⊤ => if c = 0 then 0 else ⊤
| (f : F) => toE (c.val * f)

instance : SMulZeroClass F≥0 F∞ where
  smul := EF.smulNN
  smul_zero (c : F≥0) := EF.coe_eq_coe_iff.← (mul_zero c.val)

omit [IsStrictOrderedRing F] in
lemma EF.pos_smul_top {c : F≥0} (hc : 0 < c) : c • (⊤ : F∞) = ⊤ := by
  change EF.smulNN c ⊤ = ⊤
  change (if c = 0 then (0 : F∞) else ⊤) = ⊤
  exact if_neg hc.ne.symm

lemma EF.smul_top_neq_bot (c : F≥0) : c • (⊤ : F∞) ≠ ⊥ := by
  change EF.smulNN c ⊤ ≠ ⊥
  change (if c = 0 then (0 : F∞) else ⊤) ≠ ⊥
  by_cases hc0 : c = 0
  · simp [hc0]
  · simp [hc0]

omit [IsStrictOrderedRing F] in
lemma EF.smul_coe_neq_bot (c : F≥0) (f : F) : c • toE f ≠ (⊥ : F∞) :=
  EF.coe_neq_bot (c * f)

omit [IsStrictOrderedRing F] in
lemma EF.smul_bot (c : F≥0) : c • (⊥ : F∞) = ⊥ :=
  rfl

lemma EF.smul_nonbot_neq_bot (c : F≥0) {r : F∞} (hr : r ≠ ⊥) : c • r ≠ ⊥ := by
  match r with
  | ⊥ => simp at hr
  | ⊤ => apply EF.smul_top_neq_bot
  | (f : F) => apply EF.smul_coe_neq_bot

omit [IsStrictOrderedRing F] in
lemma EF.zero_smul_nonbot {r : F∞} (hr : r ≠ ⊥) : (0 : F≥0) • r = 0 := by
  change EF.smulNN 0 r = 0
  match r with
  | ⊥ => simp at hr
  | ⊤ => exact if_pos rfl
  | (f : F) => exact congr_arg toE (zero_mul f)

omit [IsStrictOrderedRing F] in
lemma EF.zero_smul_coe (f : F) : (0 : F≥0) • toE f = 0 :=
  EF.zero_smul_nonbot (EF.coe_neq_bot f)

/-- The canonical inclusion `F → F∞` packaged as an additive homomorphism. -/
def EF.AddHom : F →+ F∞ := ⟨⟨toE, EF.coe_zero⟩, EF.coe_add⟩

omit [LinearOrder F] [IsStrictOrderedRing F] in
lemma Finset.sum_toE {ι : Type*} (s : Finset ι) (f : ι → F) :
    toE (s.sum f) = s.sum (fun i : ι => toE (f i)) :=
  map_sum EF.AddHom f s

lemma Multiset.sum_eq_EF_bot_iff (s : Multiset F∞) : s.sum = (⊥ : F∞) ↔ ⊥ ∈ s := by
  constructor <;> intro hs
  · induction s using Multiset.induction with
    | empty =>
      exfalso
      rw [Multiset.sum_zero] at hs
      exact EF.zero_neq_bot hs
    | cons a m ih =>
      rw [Multiset.mem_cons]
      rw [Multiset.sum_cons] at hs
      match a with
      | ⊥ =>
        left
        rfl
      | ⊤ =>
        match hm : m.sum with
        | ⊥ =>
          right
          exact ih hm
        | ⊤ =>
          exfalso
          rw [hm] at hs
          change hs to ⊤ + ⊤ = ⊥
          rw [EF.top_add_top] at hs
          exact top_ne_bot hs
        | (f : F) =>
          exfalso
          rw [hm] at hs
          change hs to ⊤ + toE f = ⊥
          rw [EF.top_add_coe] at hs
          exact top_ne_bot hs
      | (f : F) =>
        match hm : m.sum with
        | ⊥ =>
          right
          exact ih hm
        | ⊤ =>
          exfalso
          rw [hm] at hs
          change hs to toE f + ⊤ = ⊥
          rw [EF.coe_add_top] at hs
          exact top_ne_bot hs
        | (_ : F) =>
          exfalso
          rw [hm] at hs
          exact EF.coe_neq_bot _ hs
  · induction s using Multiset.induction with
    | empty =>
      exfalso
      exact Multiset.notMem_zero ⊥ hs
    | cons a m ih =>
      rw [Multiset.sum_cons]
      rw [Multiset.mem_cons] at hs
      cases hs with
      | inl ha => rw [←ha, EF.bot_add]
      | inr hm => rw [ih hm, EF.add_bot]

lemma Multiset.sum_eq_EF_top {s : Multiset F∞} (htop : ⊤ ∈ s) (hbot : ⊥ ∉ s) :
    s.sum = (⊤ : F∞) := by
  induction s using Multiset.induction with
  | empty =>
    exfalso
    exact Multiset.notMem_zero ⊤ htop
  | cons a m ih =>
    rw [Multiset.sum_cons]
    rw [Multiset.mem_cons] at htop
    cases htop with
    | inl ha =>
      rw [←ha]
      match hm : m.sum with
      | (f : F) => rfl
      | ⊤ => rfl
      | ⊥ =>
        exfalso
        apply hbot
        rw [Multiset.mem_cons]
        right
        rw [←Multiset.sum_eq_EF_bot_iff]
        exact hm
    | inr hm =>
      rw [ih hm ((hbot ∘ Multiset.mem_cons_of_mem) ·)]
      match a with
      | (f : F) => rfl
      | ⊤ => rfl
      | ⊥ => simp at hbot

end extras_EF


open scoped Matrix
variable {I J : Type*} [Fintype I] [Fintype J]


section hetero_matrix_products_defs
variable {α γ : Type*} [AddCommMonoid α] [SMul γ α]
  -- elements come from `α` but weights (coefficients) from `γ`

/-- `dotWeig v w` is the sum of the element-wise products `w i • v i` akin the dot product
    but heterogeneous (mnemonic: "vector times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the
    `SMul` it builds upon. -/
def dotWeig (v : I → α) (w : I → γ) : α := ∑ i : I, w i • v i

@[inherit_doc dotWeig]
infixl:72 " ᵥ⬝ " => dotWeig

/-- `Matrix.mulWeig M w` is the heterogeneous analogue of the matrix-vector product
    `Matrix.mulVec M w` (mnemonic: "matrix times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the
    `SMul` it builds upon. -/
def Matrix.mulWeig (M : Matrix I J α) (w : J → γ) (i : I) : α :=
  M i ᵥ⬝ w

@[inherit_doc Matrix.mulWeig]
infixr:73 " ₘ* " => Matrix.mulWeig

end hetero_matrix_products_defs


section hetero_matrix_products_EF

omit [IsStrictOrderedRing F] in
lemma no_bot_dotWeig_zero {v : I → F∞} (hv : ∀ i, v i ≠ ⊥) :
    v ᵥ⬝ (0 : I → F≥0) = (0 : F∞) :=
  Finset.sum_eq_zero (fun (i : I) _ =>
    match hvi : v i with
    | ⊤ => show EF.smulNN 0 ⊤ = 0 from if_pos rfl
    | ⊥ => (hv i hvi).elim
    | (f : F) => EF.zero_smul_coe f)

lemma has_bot_dotWeig_nneg {v : I → F∞} {i : I} (hvi : v i = ⊥) (w : I → F≥0) :
    v ᵥ⬝ w = (⊥ : F∞) := by
  simp only [dotWeig, Finset.sum, Multiset.sum_eq_EF_bot_iff, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ, true_and]
  use i
  rewrite [hvi]
  rfl

lemma no_bot_dotWeig_nneg {v : I → F∞} (hv : ∀ i, v i ≠ ⊥) (w : I → F≥0) :
    v ᵥ⬝ w ≠ (⊥ : F∞) := by
  simp only [dotWeig, Finset.sum]
  intro contr
  simp only [Multiset.sum_eq_EF_bot_iff, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
    true_and] at contr
  obtain ⟨i, hi⟩ := contr
  exact match hvi : v i with
  | ⊥ => hv i hvi
  | ⊤ => EF.smul_top_neq_bot (w i) ((congr_arg _ hvi.symm).trans hi)
  | (f : F) => EF.smul_coe_neq_bot (w i) f ((congr_arg _ hvi.symm).trans hi)

lemma no_bot_has_top_dotWeig_pos {v : I → F∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    (w : I → F≥0) (hwi : 0 < w i) :
    v ᵥ⬝ w = ⊤ := by
  apply Multiset.sum_eq_EF_top
  · rw [Multiset.mem_map]
    use i
    constructor
    · rw [Finset.mem_val]
      apply Finset.mem_univ
    · rw [hvi]
      exact EF.pos_smul_top hwi
  · intro contr
    rw [Multiset.mem_map] at contr
    obtain ⟨b, -, hb⟩ := contr
    exact EF.smul_nonbot_neq_bot (w b) (hv b) hb

lemma no_bot_has_top_dotWeig_le {v : I → F∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    (w : I → F≥0) {f : F} (hq : v ᵥ⬝ w ≤ f) :
    w i ≤ 0 := by
  by_contra! contr
  rw [no_bot_has_top_dotWeig_pos hv hvi w contr, top_le_iff] at hq
  exact EF.coe_neq_top f hq

lemma no_bot_has_top_dotWeig_nneg_le {v : I → F∞} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
    (w : I → F≥0) {f : F} (hq : v ᵥ⬝ w ≤ f) :
    w i = 0 :=
  le_antisymm (no_bot_has_top_dotWeig_le hv hvi w hq) (w i).property

lemma dotWeig_zero_le_zero (v : I → F∞) :
    v ᵥ⬝ (0 : I → F≥0) ≤ (0 : F∞) := by
  if hv : ∀ i, v i ≠ ⊥ then
    rw [no_bot_dotWeig_zero hv]
  else
    push Not at hv
    rw [has_bot_dotWeig_nneg]
    · apply bot_le
    · exact hv.choose_spec

omit [Fintype I] in
lemma Matrix.mulWeig_zero_le_zero (M : Matrix I J F∞) :
    M ₘ* (0 : J → F≥0) ≤ (0 : I → F∞) := by
  intro i
  apply dotWeig_zero_le_zero

end hetero_matrix_products_EF


section extended_Farkas

/-! The proof of `extendedFarkas` below is split across several private helpers so that no
single proof body exceeds the LeanPool 200-line cap, and so the elaborator does not run out
of heartbeats. -/

private abbrev extendedFarkas.I' (A : Matrix I J F∞) (b : I → F∞) : Type _ :=
  { i : I // b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥ }

private abbrev extendedFarkas.J' (A : Matrix I J F∞) (b : I → F∞) : Type _ :=
  { j : J // ∀ i' : extendedFarkas.I' A b, A i'.val j ≠ ⊤ }

private def extendedFarkas.A' (A : Matrix I J F∞) (b : I → F∞) :
    Matrix (extendedFarkas.I' A b) (extendedFarkas.J' A b) F :=
  Matrix.of (fun i' : extendedFarkas.I' A b => fun j' : extendedFarkas.J' A b =>
    match matcha : A i'.val j'.val with
    | (f : F) => f
    | ⊥ => (i'.property.right j' matcha).elim
    | ⊤ => (j'.property i' matcha).elim)

private def extendedFarkas.b' {A : Matrix I J F∞} {b : I → F∞} (hbot : ¬ ∃ i : I, b i = ⊥) :
    extendedFarkas.I' A b → F :=
  fun i' : extendedFarkas.I' A b =>
    match hbi : b i'.val with
    | (f : F) => f
    | ⊥ => (hbot ⟨i', hbi⟩).elim
    | ⊤ => (i'.property.left hbi).elim

private lemma extendedFarkas.fwd_solution {A : Matrix I J F∞} {b : I → F∞}
    (hbot : ¬ ∃ i : I, b i = ⊥)
    (x : J → F≥0) (ineqalities : A ₘ* x ≤ b) :
    ∃ x' : extendedFarkas.J' A b → F, 0 ≤ x' ∧
      extendedFarkas.A' A b *ᵥ x' ≤ extendedFarkas.b' (A := A) hbot := by
  refine ⟨(x ·.val), (x ·.val |>.property), fun i' : extendedFarkas.I' A b => ?_⟩
  rw [←EF.coe_le_coe_iff]
  convert ineqalities i'.val; swap
  · simp only [extendedFarkas.b']
    split <;> rename_i hbi
    · exact hbi.symm
    · exact (hbot ⟨i', hbi⟩).elim
    · exact (i'.property.left hbi).elim
  simp only [Matrix.mulVec, dotProduct, Matrix.mulWeig, dotWeig]
  rw [Finset.sum_toE, Finset.univ_sum_of_zero_when_not (fun j : J =>
    ∀ i' : extendedFarkas.I' A b, A i'.val j ≠ ⊤)]
  · congr
    ext j'
    rw [mul_comm]
    simp only [extendedFarkas.A', Matrix.of_apply]
    split <;> rename_i hAij
    · exact congr_arg (x j'.val • ·) hAij.symm
    · exact (i'.property.right _ hAij).elim
    · exact (j'.property _ hAij).elim
  · intro j where_top
    push Not at where_top
    obtain ⟨t, ht⟩ := where_top
    have hxj : x j = 0
    · obtain ⟨e, he⟩ : ∃ e : F, b t = e :=
        match hbt : b t.val with
        | (f : F) => ⟨_, rfl⟩
        | ⊥ => (hbot ⟨t, hbt⟩).elim
        | ⊤ => (t.property.left hbt).elim
      exact no_bot_has_top_dotWeig_nneg_le (t.property.right) ht x (he ▸ ineqalities t.val)
    rw [hxj]
    apply EF.zero_smul_nonbot
    apply i'.property.right

private lemma extendedFarkas.bwd_solution {A : Matrix I J F∞} {b : I → F∞}
    (hbot : ¬ ∃ i : I, b i = ⊥)
    (x : extendedFarkas.J' A b → F) (hx : 0 ≤ x)
    (ineqalities : extendedFarkas.A' A b *ᵥ x ≤ extendedFarkas.b' (A := A) hbot) :
    ∃ x' : J → F≥0, A ₘ* x' ≤ b := by
  use (fun j : J => if hj : (∀ i' : extendedFarkas.I' A b, A i'.val j ≠ ⊤) then
    ⟨x ⟨j, hj⟩, hx ⟨j, hj⟩⟩ else 0)
  intro i
  if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then
    convert EF.coe_le_coe_iff.← (ineqalities ⟨i, hi⟩)
    · unfold Matrix.mulVec dotProduct Matrix.mulWeig dotWeig
      simp_rw [dite_smul]
      rw [Finset.sum_dite]
      convert add_zero _
      · apply Finset.sum_eq_zero
        intro j _
        apply EF.zero_smul_nonbot
        exact hi.right j.val
      · erw [←Finset.sum_coe_sort_eq_attach]
        rw [Finset.sum_toE]
        apply Finset.subtype_univ_sum_eq_subtype_univ_sum
        · ext
          simp
        · intro j hj _
          rw [mul_comm]
          simp only [extendedFarkas.A', Matrix.of_apply]
          split <;> rename_i hAij
          · exact hAij ▸ rfl
          · exact (hi.right _ hAij).elim
          · exact (hj ⟨i, hi⟩ hAij).elim
    · simp only [extendedFarkas.b']
      split <;> rename_i hbi
      · exact hbi
      · exact (hbot ⟨i, hbi⟩).elim
      · exact (hi.left hbi).elim
  else
    push Not at hi
    if hbi : b i = ⊤ then
      rw [hbi]
      apply le_top
    else
      obtain ⟨j, hAij⟩ := hi hbi
      convert_to ⊥ ≤ b i
      · apply has_bot_dotWeig_nneg hAij
      apply bot_le

private lemma extendedFarkas.fwd_witness {A : Matrix I J F∞} {b : I → F∞}
    (hbot : ¬ ∃ i : I, b i = ⊥)
    (hAi : ¬ ∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤))
    (hAj : ¬ ∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤))
    (hAb : ¬ ∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤)
    (y : I → F≥0)
    (ineqalities : -Aᵀ ₘ* y ≤ 0) (sharpine : b ᵥ⬝ y < 0) :
    ∃ y' : extendedFarkas.I' A b → F, 0 ≤ y' ∧
      -(extendedFarkas.A' A b)ᵀ *ᵥ y' ≤ 0 ∧ extendedFarkas.b' (A := A) hbot ⬝ᵥ y' < 0 := by
  use (fun i' : extendedFarkas.I' A b => y i'.val)
  constructor
  · intro i'
    exact (y i'.val).property
  have h0 : ∀ i : I, ¬ (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) → y i = 0
  · intro i i_not_I'
    by_contra contr
    have hyi : 0 < y i
    · cases lt_or_eq_of_le (y i).property with
      | inl hpos =>
        exact hpos
      | inr h0 =>
        exfalso
        apply contr
        ext
        exact h0.symm
    if bi_top : b i = ⊤ then
      have impos : b ᵥ⬝ y = ⊤
      · push Not at hbot
        exact no_bot_has_top_dotWeig_pos hbot bi_top y hyi
      rw [impos] at sharpine
      exact not_top_lt sharpine
    else
      push Not at i_not_I'
      obtain ⟨j, Aij_eq_bot⟩ := i_not_I' bi_top
      have htop : ((-Aᵀ) j) ᵥ⬝ y = ⊤
      · refine no_bot_has_top_dotWeig_pos ?_ (by simpa using Aij_eq_bot) y hyi
        intro k hk
        exact hAj ⟨j, ⟨i, Aij_eq_bot⟩, ⟨k, by simpa using hk⟩⟩
      have ineqality : ((-Aᵀ) j) ᵥ⬝ y ≤ 0 := ineqalities j
      rw [htop, top_le_iff] at ineqality
      exact EF.zero_neq_top ineqality
  constructor
  · have hnb : ∀ i : I, ¬ (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) → ∀ j : J, (-Aᵀ) j i ≠ ⊥
    · intro i i_not_I' j contr
      have btop : ∃ j : J, A i j = ⊤
      · use j
        simpa using contr
      refine hAi ⟨i, ?_, btop⟩
      push Not at i_not_I'
      apply i_not_I'
      intro bi_eq_top
      apply hAb
      use i
    intro j'
    have inequality : ∑ i : I, y i • (-Aᵀ) j'.val i ≤ 0 := ineqalities j'
    rw [Finset.univ_sum_of_zero_when_not
      (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at inequality
    · rw [←EF.coe_le_coe_iff]
      convert inequality
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_toE]
      congr
      ext i'
      simp only [extendedFarkas.A', Matrix.neg_apply, Matrix.transpose_apply, Matrix.of_apply]
      split <;> rename_i hAij
      · rewrite [hAij, mul_comm]
        rfl
      · exfalso
        apply i'.property.right
        exact hAij
      · exfalso
        apply j'.property
        exact hAij
    · intro i hi
      rw [h0 i hi]
      apply EF.zero_smul_nonbot
      apply hnb
      exact hi
  · unfold dotWeig at sharpine
    rw [Finset.univ_sum_of_zero_when_not
      (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at sharpine
    · unfold dotProduct
      rw [←EF.coe_lt_coe_iff, Finset.sum_toE]
      convert sharpine with i'
      simp only [extendedFarkas.b']
      split <;> rename_i hbi
      · rewrite [hbi, mul_comm]
        rfl
      · exfalso
        apply hbot
        use i'
        exact hbi
      · exfalso
        apply i'.property.left
        exact hbi
    · intro i hi
      rw [h0 i hi]
      apply EF.zero_smul_nonbot
      intro contr
      exact hbot ⟨i, contr⟩

private lemma extendedFarkas.bwd_witness {A : Matrix I J F∞} {b : I → F∞}
    (hbot : ¬ ∃ i : I, b i = ⊥)
    (y : extendedFarkas.I' A b → F) (hy : 0 ≤ y)
    (ineqalities : -(extendedFarkas.A' A b)ᵀ *ᵥ y ≤ 0)
    (sharpine : extendedFarkas.b' (A := A) hbot ⬝ᵥ y < 0) :
    ∃ y' : I → F≥0, -Aᵀ ₘ* y' ≤ 0 ∧ b ᵥ⬝ y' < 0 := by
  use (fun i : I => if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then ⟨y ⟨i, hi⟩, hy ⟨i, hi⟩⟩ else 0)
  constructor
  · intro j
    if hj : (∀ i : I, A i j ≠ ⊤) then
      convert EF.coe_le_coe_iff.← (ineqalities ⟨j, (hj ·.val)⟩)
      simp only [Matrix.mulWeig]
      simp only [dotWeig, dite_smul]
      rw [Finset.sum_dite]
      convert add_zero _
      · apply Finset.sum_eq_zero
        intro i _
        apply EF.zero_smul_nonbot
        intro contr
        rw [Matrix.neg_apply, EF.neg_eq_bot_iff] at contr
        exact hj i contr
      · simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.transpose_apply]
        rw [Finset.sum_toE]
        apply Finset.subtype_univ_sum_eq_subtype_univ_sum
        · ext
          simp
        · intro i hi hif
          rw [mul_comm]
          simp only [extendedFarkas.A', Matrix.of_apply]
          split <;> rename_i hAij
          · exact hAij ▸ rfl
          · exact (hi.right _ hAij).elim
          · exact (hj _ hAij).elim
    else
      push Not at hj
      obtain ⟨i, Aij_eq_top⟩ := hj
      unfold Matrix.mulWeig
      rw [has_bot_dotWeig_nneg]
      · apply bot_le
      · rwa [Matrix.neg_apply, Matrix.transpose_apply, EF.neg_eq_bot_iff]
  · convert EF.coe_lt_coe_iff.← sharpine
    unfold dotProduct dotWeig
    simp_rw [dite_smul]
    rw [Finset.sum_dite]
    convert add_zero _
    · apply Finset.sum_eq_zero
      intro j _
      apply EF.zero_smul_nonbot
      exact (hbot ⟨j.val, ·⟩)
    · erw [←Finset.sum_coe_sort_eq_attach]
      rw [Finset.sum_toE]
      apply Finset.subtype_univ_sum_eq_subtype_univ_sum
      · ext
        simp
      · intro i hi _
        rw [mul_comm]
        simp only [extendedFarkas.b']
        split <;> rename_i hbi
        · simp_rw [hbi]; exact rfl
        · exact (hbot ⟨i, hbi⟩).elim
        · exact (hi.left hbi).elim

/-- Just like `inequalityFarkas_neg` but for `A` and `b` over `F∞`. -/
theorem extendedFarkas
    -- The matrix (LHS)
    (A : Matrix I J F∞)
    -- The upper-bounding vector (RHS)
    (b : I → F∞)
    -- `A` must not have both `⊥` and `⊤` in the same row
    (hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤))
    -- `A` must not have both `⊥` and `⊤` in the same column
    (hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤))
    -- `A` must not have `⊤` on any row where `b` has `⊤`
    (hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤)
    -- `A` must not have `⊥` on any row where `b` has `⊥`
    (hbA : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥) :
    (∃ x : J → F≥0, A ₘ* x ≤ b) ≠ (∃ y : I → F≥0, -Aᵀ ₘ* y ≤ 0 ∧ b ᵥ⬝ y < 0) := by
  classical
  if hbot : ∃ i : I, b i = ⊥ then
    obtain ⟨i, hi⟩ := hbot
    if hi' : (∀ j : J, A i j ≠ ⊥) then
      convert false_ne_true
      · rw [iff_false, not_exists]
        intro x hAxb
        specialize hAxb i
        rw [hi, le_bot_iff] at hAxb
        exact no_bot_dotWeig_nneg hi' x hAxb
      · rw [iff_true]
        use 0
        constructor
        · apply Matrix.mulWeig_zero_le_zero
        · rw [has_bot_dotWeig_nneg hi]
          exact EF.bot_lt_zero
    else
      push Not at hi'
      exfalso
      apply hbA
      exact ⟨i, hi', hi⟩
  else
    convert inequalityFarkas_neg (extendedFarkas.A' A b) (extendedFarkas.b' (A := A) hbot)
    · constructor
      · intro ⟨x, ineqalities⟩
        exact extendedFarkas.fwd_solution hbot x ineqalities
      · intro ⟨x, hx, ineqalities⟩
        exact extendedFarkas.bwd_solution hbot x hx ineqalities
    · constructor
      · intro ⟨y, ineqalities, sharpine⟩
        exact extendedFarkas.fwd_witness hbot hAi hAj hAb y ineqalities sharpine
      · intro ⟨y, hy, ineqalities, sharpine⟩
        exact extendedFarkas.bwd_witness hbot y hy ineqalities sharpine

end extended_Farkas
