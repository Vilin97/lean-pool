/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Tactic.Linarith
import LeanPool.Duality.FarkasSpecial


/-- Linear program over `F∞` in the standard form (i.e.,
    a system of linear inequalities with nonnegative variables).
    Variables are of type `J`. Conditions are indexed by type `I`.
    The objective function is intended to be minimized. -/
@[ext]
structure ExtendedLP (I J F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] where
  /-- The left-hand-side matrix. -/
  A : Matrix I J F∞
  /-- The right-hand-side vector. -/
  b : I → F∞
  /-- The objective function coefficients. -/
  c : J → F∞

/-- Extended linear program with properties that are needed for duality theorems. -/
structure ValidELP (I J F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    extends ExtendedLP I J F where
  /-- No `⊥` and `⊤` in the same row. -/
  hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤)
  /-- No `⊥` and `⊤` in the same column. -/
  hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤)
  /-- No `⊥` in the row where the right-hand-side vector has `⊥`. -/
  hbA : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥
  /-- No `⊤` in the column where the objective function has `⊥`. -/
  hcA : ¬∃ j : J, (∃ i : I, A i j = ⊤) ∧ c j = ⊥
  /-- No `⊤` in the row where the right-hand-side vector has `⊤`. -/
  hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤
  /-- No `⊥` in the column where the objective function has `⊤`. -/
  hAc : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ c j = ⊤

open scoped Matrix

variable {I J F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

section extended_LP_definitions

/-- A nonnegative vector `x` is a solution to a linear program `P` iff
    its multiplication by matrix `A` from the left yields a vector whose
    all entries are less or equal to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution [Fintype J] (P : ExtendedLP I J F) (x : J → F≥0) : Prop :=
  P.A ₘ* x ≤ P.b

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. -/
def ExtendedLP.Reaches [Fintype J] (P : ExtendedLP I J F) (r : F∞) : Prop :=
  ∃ x : J → F≥0, P.IsSolution x ∧ P.c ᵥ⬝ x = r

/-- Linear program `P` is feasible iff `P` reaches a value that is not `⊤`. -/
def ExtendedLP.IsFeasible [Fintype J] (P : ExtendedLP I J F) : Prop :=
  ∃ p : F∞, P.Reaches p ∧ p ≠ ⊤

/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded by `r` from below). -/
def ExtendedLP.IsBoundedBy [Fintype J] (P : ExtendedLP I J F) (r : F) : Prop :=
  ∀ p : F∞, P.Reaches p → r ≤ p

/-- Linear program `P` is unbounded iff values reached by `P` have no finite lower bound. -/
def ExtendedLP.IsUnbounded [Fintype J] (P : ExtendedLP I J F) : Prop :=
  ¬∃ r : F, P.IsBoundedBy r

open scoped Classical in
/-- Extended notion of "optimum" of "minimization LP" (the less the better). -/
noncomputable def ExtendedLP.optimum [Fintype J] (P : ExtendedLP I J F) : Option F∞ :=
  if ¬P.IsFeasible then
    some ⊤ -- infeasible means that the minimum is `⊤`
  else
    if P.IsUnbounded then
      some ⊥ -- unbounded means that the minimum is `⊥`
    else
      if hr : ∃ r : F, P.Reaches (toE r) ∧ P.IsBoundedBy r then
        some (toE hr.choose) -- the minimum is finite
      else
        none -- invalid finite value (infimum is not attained)

/-- `OppositesOpt p q` essentially says `none ≠ p = -q`. -/
def OppositesOpt : Option F∞ → Option F∞ → Prop
| (p : F∞), (q : F∞) => p = -q  -- opposite values; includes `⊥ = -⊤` and `⊤ = -⊥`
| _       , _        => False   -- namely `OppositesOpt none none` is `False`

/-- Dualize an extended linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function.
    Both linear programs are intended to be minimized. -/
abbrev ExtendedLP.dualize (P : ExtendedLP I J F) : ExtendedLP J I F :=
  ⟨-P.Aᵀ, P.c, P.b⟩

/-- Dualize a valid extended linear program. -/
def ValidELP.dualize (P : ValidELP I J F) : ValidELP J I F where
  toExtendedLP := P.toExtendedLP.dualize
  hAi := by aeply P.hAj
  hAj := by aeply P.hAi
  hbA := by aeply P.hcA
  hcA := by aeply P.hbA
  hAb := by aeply P.hAc
  hAc := by aeply P.hAb

end extended_LP_definitions


section weak_duality

lemma EF.one_smul (r : F∞) : (1 : F≥0) • r = r :=
  match r with
  | ⊥ => rfl
  | ⊤ => EF.pos_smul_top one_pos
  | (q : F) => congr_arg toE (one_mul q)

lemma EF.sub_nonpos_iff (r s : F∞) : r + (-s) ≤ 0 ↔ r ≤ s := by simp [←EF.coe_neg, ←EF.coe_add]

lemma EF.vec_sub_nonpos_iff (u v : I → F∞) : u + (-v) ≤ 0 ↔ u ≤ v := by
  constructor <;> intro huv i <;> simpa [EF.sub_nonpos_iff] using huv i

omit [IsStrictOrderedRing F] in
lemma sumElim_dotWeig_sumElim [Fintype I] [Fintype J] (u : I → F∞) (v : J → F∞)
    (x : I → F≥0) (y : J → F≥0) :
    Sum.elim u v ᵥ⬝ Sum.elim x y = u ᵥ⬝ x + v ᵥ⬝ y := by
  simp [dotWeig]

omit [IsStrictOrderedRing F] in
lemma Matrix.fromRows_mulWeig [Fintype J] {I₁ I₂ : Type*} (M₁ : Matrix I₁ J F∞)
    (M₂ : Matrix I₂ J F∞) (w : J → F≥0) :
    Matrix.fromRows M₁ M₂ ₘ* w = Sum.elim (M₁ ₘ* w) (M₂ ₘ* w) := by
  ext (_|_) <;> rfl

omit [IsStrictOrderedRing F] in
lemma Matrix.fromCols_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (M₁ : Matrix I J₁ F∞) (M₂ : Matrix I J₂ F∞) (w₁ : J₁ → F≥0) (w₂ : J₂ → F≥0) :
    Matrix.fromCols M₁ M₂ ₘ* Sum.elim w₁ w₂ = M₁ ₘ* w₁ + M₂ ₘ* w₂ := by
  ext
  simp [Matrix.fromCols, Matrix.mulWeig, dotWeig]

lemma dotWeig_eq_bot [Fintype J] {v : J → F∞} {w : J → F≥0} :
    (∃ j : J, v j = ⊥) ↔ v ᵥ⬝ w = ⊥ :=
  ⟨fun ⟨j, hvj⟩ => has_bot_dotWeig_nneg hvj w, fun hvw => by_contra (no_bot_dotWeig_nneg · w hvw)⟩

lemma ValidELP.weakDuality_of_no_bot [Fintype I] [Fintype J]
    (P : ValidELP I J F) (hb : ¬∃ i : I, P.b i = ⊥) (hc : ¬∃ j : J, P.c j = ⊥)
    {p : F∞} (hP : P.Reaches p) {q : F∞} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  classical
  obtain ⟨x, hx, rfl⟩ := hP
  obtain ⟨y, hy, rfl⟩ := hQ
  by_contra contr
  apply
    not_and_of_neq
      (extendedFarkas
        (Matrix.fromRows P.A (Matrix.replicateRow Unit P.c))
        (Sum.elim P.b ↓(P.c ᵥ⬝ x))
        (by
          intro ⟨i, ⟨s, his⟩, ⟨t, hit⟩⟩
          cases i with
          | inl i' => exact P.hAi ⟨i', ⟨s, his⟩, ⟨t, hit⟩⟩
          | inr => exact hc ⟨s, his⟩
        )
        (by
          intro ⟨j, ⟨s, hjs⟩, ⟨t, hjt⟩⟩
          cases s with
          | inl iₛ =>
            cases t with
            | inl iₜ => exact P.hAj ⟨j, ⟨iₛ, hjs⟩, ⟨iₜ, hjt⟩⟩
            | inr => exact P.hAc ⟨j, ⟨iₛ, hjs⟩, hjt⟩
          | inr =>
            cases t with
            | inl iₜ => exact P.hcA ⟨j, ⟨iₜ, hjt⟩, hjs⟩
            | inr => simp_all
        )
        (by
          intro ⟨i, ⟨j, hij⟩, hi⟩
          cases i with
          | inl i' => exact P.hAb ⟨i', ⟨j, hij⟩, hi⟩
          | inr =>
            rw [Sum.elim_inr] at hi
            push Not at contr
            rw [hi] at contr
            match hby : P.b ᵥ⬝ y with
            | ⊥ => exact hb (dotWeig_eq_bot.← hby)
            | ⊤ | (_ : F) => simp [hby, ValidELP.dualize] at contr
        )
        (by
          intro ⟨i, ⟨j, hij⟩, hi⟩
          cases i with
          | inl i' => exact P.hbA ⟨i', ⟨j, hij⟩, hi⟩
          | inr => exact hc ⟨j, hij⟩
        )
      )
  refine ⟨⟨x, Matrix.fromRows_mulWeig .. ▸ Sum.elim_le_elim_iff.mpr ⟨hx, by rfl⟩⟩, Sum.elim y 1, ?_, ?_⟩
    · rw [Matrix.transpose_fromRows, Matrix.fromCols_neg, Matrix.fromCols_mulWeig_sumElim]
      convert (show (-P.Aᵀ) ₘ* y + (-P.c) ≤ 0 from by rwa [EF.vec_sub_nonpos_iff])
      ext
      simp [Matrix.mulWeig, dotWeig, EF.one_smul]
    · simp only [sumElim_dotWeig_sumElim, dotWeig, EF.one_smul]
      push Not at contr
      rwa [add_comm] at contr

lemma ValidELP.no_bot_of_reaches [Fintype J] (P : ValidELP I J F) {p : F∞} (hP : P.Reaches p)
    (i : I) : P.b i ≠ ⊥ := fun contr =>
  P.hbA ⟨i, dotWeig_eq_bot.← (le_bot_iff.mp (contr ▸ hP.choose_spec.1 i)), contr⟩

theorem ValidELP.weakDuality [Fintype I] [Fintype J]
    (P : ValidELP I J F)
    {p : F∞} (hP : P.Reaches p) {q : F∞} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  by_cases hb : ∃ i : I, P.b i = ⊥
  · exact absurd hb.choose_spec (P.no_bot_of_reaches hP hb.choose)
  by_cases hc : ∃ j : J, P.c j = ⊥
  · exact absurd hc.choose_spec (P.dualize.no_bot_of_reaches hQ hc.choose)
  exact P.weakDuality_of_no_bot hb hc hP hQ

end weak_duality


section strong_duality

section nneg_vs_zero

omit [IsStrictOrderedRing F] in
lemma eq_zero_of_zero_eq_val {k : F≥0} (hk : 0 = k.val) :
    k = 0 :=
  Subtype.ext hk.symm

omit [IsStrictOrderedRing F] in
lemma pos_of_NN_not_zero {k : F≥0} (hk : ¬(k = 0)) :
    0 < k :=
  lt_of_le_of_ne k.property (hk ∘ eq_zero_of_zero_eq_val)

end nneg_vs_zero

section misc_EF_properties

lemma EF.smul_nonpos {r : F∞} (hr : r ≤ 0) (k : F≥0) :
    k • r ≤ 0 :=
  match r with
  | ⊥ => bot_le
  | ⊤ => absurd hr (not_le.mpr EF.zero_lt_top)
  | (f : F) => EF.coe_le_coe_iff.← (mul_nonpos_of_nonneg_of_nonpos k.property (EF.coe_nonpos.→ hr))

lemma EF.smul_lt_smul_left {k : F≥0} (hk : 0 < k) (r s : F∞) :
    k • r < k • s ↔ r < s := by
  match r, s with
  | _, ⊥ => simp
  | ⊥, ⊤ => simp [EF.pos_smul_top hk]
  | ⊤, ⊤ => simp
  | (_ : F), ⊤ => simp [EF.pos_smul_top hk]
  | ⊥, (_ : F) => simp
  | ⊤, (_ : F) => simp [EF.pos_smul_top hk]
  | (p : F), (q : F) => simp [EF.coe_lt_coe_iff, mul_lt_mul_iff_right₀ hk]

lemma EF.smul_le_smul_left {k : F≥0} (hk : 0 < k) (r s : F∞) :
    k • r ≤ k • s ↔ r ≤ s := by
  convert neg_iff_neg (EF.smul_lt_smul_left hk s r) <;> exact Iff.symm not_lt

lemma EF.smul_neg {k : F≥0} {r : F∞} (hkr : k = 0 → r ≠ ⊥ ∧ r ≠ ⊤) :
    k • (-r) = -(k • r) :=
  match r with
  | ⊥ => if hk : 0 < k then EF.pos_smul_top hk ▸ rfl else by simp_all [EF.neg_bot]
  | ⊤ => if hk : 0 < k then by simp [EF.pos_smul_top hk, EF.neg_top] else by simp_all [EF.neg_top]
  | (f : F) => by simp [EF.coe_neg, mul_neg]

lemma EF.pos_smul_neg {k : F≥0} (hk : 0 < k) (r : F∞) :
    k • (-r) = -(k • r) :=
  EF.smul_neg (fun h0 => absurd (h0 ▸ hk) (lt_irrefl 0))

lemma EF.smul_smul {k : F≥0} (hk : 0 < k) (l : F≥0) (r : F∞) :
    l • (k • r) = k • (l • r) := by
  match r with
  | ⊥ => simp [EF.smul_bot]
  | ⊤ =>
    rw [EF.pos_smul_top hk]
    by_cases hl : l = 0 <;> simp_all [EF.zero_smul_nonbot, EF.pos_smul_top, pos_of_NN_not_zero]
  | (f : F) => exact EF.coe_eq_coe_iff.← (mul_left_comm l.val k.val f)

lemma EF.add_smul (k l : F≥0) (r : F∞) :
    (k + l) • r = k • r + l • r := by
  match r with
  | ⊥ => simp [EF.smul_bot]
  | ⊤ => by_cases hk : k = 0 <;> by_cases hl : l = 0 <;>
      simp_all [EF.zero_smul_nonbot, EF.pos_smul_top, pos_of_NN_not_zero]
  | (f : F) => simp [←EF.coe_add, add_mul]

omit [IsStrictOrderedRing F] in
lemma EF.smul_add {k : F≥0} (hk : 0 < k) (r s : F∞) :
    k • (r + s) = k • r + k • s := by
  match r, s with
  | ⊥, _ => simp [EF.smul_bot]
  | _, ⊥ => simp [EF.smul_bot]
  | (p : F), (q : F) => simp [←EF.coe_add, mul_add]
  | (p : F), ⊤ => simp [EF.pos_smul_top hk, EF.coe_add_top]
  | ⊤, (q : F) => simp [EF.pos_smul_top hk, EF.top_add_coe]
  | ⊤, ⊤ => simp [EF.pos_smul_top hk]

lemma EF.mul_smul (k l : F≥0) (r : F∞) :
    (k * l) • r = k • (l • r) := by
  match r with
  | ⊥ => simp [EF.smul_bot]
  | ⊤ => by_cases hl : l = 0 <;> by_cases hk : k = 0 <;>
      simp_all [EF.zero_smul_nonbot, EF.pos_smul_top, pos_of_NN_not_zero]
  | (f : F) => simp [←EF.coe_eq_coe_iff, mul_assoc]

lemma EF.one_smul_vec (v : J → F∞) :
    (1 : F≥0) • v = v :=
  funext (fun i => EF.one_smul _)

omit [IsStrictOrderedRing F] in
lemma EF.smul_add_vec {k : F≥0} (hk : 0 < k) (v w : J → F∞) :
    k • (v + w) = k • v + k • w :=
  funext (fun i => EF.smul_add hk _ _)

lemma EF.mul_smul_vec (k l : F≥0) (v : J → F∞) :
    (k * l) • v = k • (l • v) :=
  funext (fun i => EF.mul_smul _ _ _)

lemma EF.vec_smul_le_smul_left {k : F≥0} (hk : 0 < k) (u v : I → F∞) :
    k • u ≤ k • v ↔ u ≤ v := by
  simp [Pi.le_def, EF.smul_le_smul_left, hk]

lemma Multiset.sum_neq_EF_top {s : Multiset F∞} (hs : ⊤ ∉ s) :
    s.sum ≠ ⊤ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    match a with
    | ⊥ => simp
    | ⊤ => simp at hs
    | (_ : F) => match hm : m.sum with
      | ⊥ => simp
      | ⊤ => exact (ih (by simpa using hs) hm).elim
      | (_ : F) => simp [←EF.coe_add]

omit [IsStrictOrderedRing F] in
lemma Multiset.smul_EF_sum {k : F≥0} (hk : 0 < k) (s : Multiset F∞) :
    (s.map (k • ·)).sum = k • s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [EF.smul_add hk, ←ih]

omit [IsStrictOrderedRing F] in
lemma Finset.smul_EF_sum [Fintype J] {k : F≥0} (hk : 0 < k) (v : J → F∞) :
    ∑ j : J, k • v j = k • ∑ j : J, v j := by
  simp only [←Multiset.smul_EF_sum hk, Finset.sum, Multiset.map_map, Function.comp_def]

end misc_EF_properties

section dotWeig_EF_properties

omit [IsStrictOrderedRing F] in
lemma zero_dotWeig [Fintype J] (w : J → F≥0) : (0 : J → F∞) ᵥ⬝ w = 0 := by simp [dotWeig]

lemma dotWeig_add [Fintype J] (x : J → F∞) (v w : J → F≥0) :
    x ᵥ⬝ (v + w) = x ᵥ⬝ v + x ᵥ⬝ w := by
  simp [dotWeig, EF.add_smul, Finset.sum_add_distrib]

lemma dotWeig_smul [Fintype J] {k : F≥0} (hk : 0 < k) (x : J → F∞) (v : J → F≥0) :
    x ᵥ⬝ (k • v) = k • (x ᵥ⬝ v) := by
  simp [dotWeig, EF.mul_smul, ←Finset.smul_EF_sum hk]

lemma no_top_dotWeig_nneg [Fintype J] {v : J → F∞} (hv : ∀ j, v j ≠ ⊤) (w : J → F≥0) :
    v ᵥ⬝ w ≠ (⊤ : F∞) :=
  Multiset.sum_neq_EF_top (by
    rw [Multiset.mem_map]
    rintro ⟨i, -, hi⟩
    exact match hvi : v i with
    | ⊥ => bot_ne_top (hvi ▸ hi)
    | ⊤ => false_of_ne (hvi ▸ hv i)
    | (_ : F) => EF.coe_neq_top _ (hvi ▸ hi))

end dotWeig_EF_properties

section matrix_EF_properties

omit [IsStrictOrderedRing F] in
lemma Matrix.EF_neg_zero : -(0 : Matrix I J F∞) = 0 := by simp

omit [IsStrictOrderedRing F] in
lemma Matrix.EF_neg_neg (M : Matrix I J F∞) : -(-M) = M := by simp

omit [IsStrictOrderedRing F] in
lemma Matrix.zero_mulWeig [Fintype J] (v : J → F≥0) : (0 : Matrix I J F∞) ₘ* v = 0 := by
  simp [Matrix.mulWeig, dotWeig]

lemma Matrix.mulWeig_add [Fintype J] (M : Matrix I J F∞) (v w : J → F≥0) :
    M ₘ* (v + w) = M ₘ* v + M ₘ* w :=
  funext (fun i => dotWeig_add _ _ _)

lemma Matrix.mulWeig_smul [Fintype J] {k : F≥0} (hk : 0 < k) (M : Matrix I J F∞) (v : J → F≥0) :
    M ₘ* (k • v) = k • (M ₘ* v) :=
  funext (fun i => dotWeig_smul hk _ _)

end matrix_EF_properties

section extended_LP_properties

lemma ValidELP.dualize_dualize (P : ValidELP I J F) : P = P.dualize.dualize := by
  simp [ValidELP.dualize, ValidELP.ext_iff]

lemma ValidELP.no_bot_of_feasible [Fintype J] (P : ValidELP I J F) (hP : P.IsFeasible) (i : I) :
    P.b i ≠ ⊥ :=
  P.no_bot_of_reaches hP.choose_spec.left i

variable [Fintype J]

lemma ValidELP.isUnbounded_iff (P : ValidELP I J F) :
    P.IsUnbounded ↔ ∀ r : F, ∃ p : F∞, P.Reaches p ∧ p < r := by
  simp [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy]

lemma ValidELP.unbounded_of_reaches_le (P : ValidELP I J F)
    (hP : ∀ r : F, ∃ p : F∞, P.Reaches p ∧ p ≤ r) :
    P.IsUnbounded :=
  ValidELP.isUnbounded_iff.mpr fun r =>
    let ⟨p, hPp, hpr⟩ := hP (r-1)
    ⟨p, hPp, hpr.trans_lt (EF.coe_lt_coe_iff.← (sub_one_lt r))⟩

lemma ValidELP.unbounded_of_feasible_of_neg (P : ValidELP I J F) (hP : P.IsFeasible)
    {x₀ : J → F≥0} (hx₀ : P.c ᵥ⬝ x₀ < 0) (hAx₀ : P.A ₘ* x₀ + (0 : F≥0) • (-P.b) ≤ 0) :
    P.IsUnbounded := by
  obtain ⟨e, ⟨xₚ, hxₚ, hce⟩, he⟩ := hP
  apply P.unbounded_of_reaches_le
  intro s
  if hs : e ≤ s then
    exact ⟨e, ⟨xₚ, hxₚ, hce⟩, by simpa using hs⟩
  else
    push Not at hs
    match e with
    | ⊥ => simp at hs
    | ⊤ => simp at he
    | (e : F) =>
      clear he
      match hcx₀ : P.c ᵥ⬝ x₀ with
      | ⊥ => exact ⟨⊥, ⟨xₚ, hxₚ, dotWeig_eq_bot.← hcx₀⟩, bot_le⟩
      | ⊤ => simp [hcx₀] at hx₀
      | (d : F) =>
        rw [hcx₀] at hx₀
        have coef_pos : 0 < (s - e) / d :=
          div_pos_of_neg_of_neg (by rwa [sub_neg, ←EF.coe_lt_coe_iff]) (by rwa [←EF.coe_neg'])
        let k : F≥0 := ⟨((s - e) / d), coef_pos.le⟩
        refine ⟨s, ⟨xₚ + k • x₀, ?_, ?_⟩, by rfl⟩
        · intro i
          match hi : P.b i with
          | ⊥ => exact absurd hi (P.no_bot_of_feasible hP i)
          | ⊤ => exact le_top
          | (bᵢ : F) =>
            specialize hAx₀ i
            simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hi, ←EF.coe_neg,
              EF.zero_smul_coe, add_zero] at hAx₀
            rw [Matrix.mulWeig_add, Matrix.mulWeig_smul coef_pos, Pi.add_apply]
            exact add_le_of_le_of_nonpos (hi ▸ hxₚ i) (EF.smul_nonpos hAx₀ k)
        · rw [dotWeig_add, hce, dotWeig_smul coef_pos, hcx₀, EF.coe_eq_coe_iff, div_mul_cancel_of_imp,
            add_sub_cancel]
          exact fun d_eq_0 => absurd (d_eq_0 ▸ hx₀) (lt_irrefl _)

variable [Fintype I]

lemma ValidELP.unbounded_of_feasible_of_infeasible (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : ¬P.dualize.IsFeasible) :
    P.IsUnbounded := by
  let I' : Type _ := { i : I // P.b i ≠ ⊤ }
  let A' : Matrix I' J F∞ := Matrix.of (fun i' : I' => P.A i'.val)
  let b' : I' → F∞ := (fun i' : I' => P.b i'.val)
  cases or_of_neq (extendedFarkas (-A'ᵀ) P.c
      (by aeply P.hAj) (by aeply P.hAi) (by aeply P.hAc) (by aeply P.hcA)) with
  | inl ⟨y, hy⟩ =>
    match hby : b' ᵥ⬝ y with
    | ⊥ => exact no_bot_dotWeig_nneg (P.no_bot_of_feasible hP ·.val ·) y hby
    | ⊤ => exact no_top_dotWeig_nneg (·.property) y hby
    | (q : F) =>
      apply hQ
      refine ⟨toE q, ⟨fun i : I => if hi : (P.b i ≠ ⊤) then y ⟨i, hi⟩ else 0, ?_, ?_⟩,
        EF.coe_neq_top q⟩
      · simp only [ValidELP.dualize, ExtendedLP.IsSolution, Matrix.mulWeig, dotWeig, dite_not,
          dite_smul, Finset.sum_dite]
        convert zero_add _ using 1
        apply congr_arg₂
        · exact Finset.sum_eq_zero (fun i _ => EF.zero_smul_nonbot
            (fun contr => P.hAb ⟨i.val, by aesop, by aesop⟩))
        · erw [←Finset.sum_coe_sort_eq_attach]
          apply Finset.subtype_univ_sum_eq_subtype_univ_sum <;> simp_all
      · simp only [dotWeig, dite_not, dite_smul, Finset.sum_dite]
        convert zero_add _
        · exact Finset.sum_eq_zero (fun i _ => EF.zero_smul_nonbot (P.no_bot_of_feasible hP i.val))
        · erw [←Finset.sum_coe_sort_eq_attach, ←hby]
          apply Finset.subtype_univ_sum_eq_subtype_univ_sum <;> simp_all
  | inr ⟨x, hAx, hcx⟩ =>
    apply P.unbounded_of_feasible_of_neg hP hcx
    rw [Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.EF_neg_neg] at hAx
    intro i
    match hbi : P.b i with
    | ⊥ => exact absurd hbi (P.no_bot_of_feasible hP i)
    | ⊤ => simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi]
    | (f : F) =>
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi,
        EF.zero_smul_nonbot (EF.coe_neq_bot _), add_zero]
      exact hAx ⟨i, hbi ▸ EF.coe_neq_top f⟩

lemma ValidELP.infeasible_of_unbounded (P : ValidELP I J F) (hP : P.IsUnbounded) :
    ¬P.dualize.IsFeasible := by
  intro ⟨q, hPq, hq⟩
  rw [ValidELP.isUnbounded_iff] at hP
  match q with
  | ⊥ => simpa using P.weakDuality (hP 0).choose_spec.1 hPq
  | ⊤ => exact hq rfl
  | (f : F) =>
    obtain ⟨p, hp, hpq⟩ := hP (-f)
    match p with
    | ⊥ => simp at (P.weakDuality hp hPq)
    | ⊤ => simp at hpq
    | (_ : F) =>
      linarith [EF.coe_le_coe_iff.mp (P.weakDuality hp hPq), EF.coe_lt_coe_iff.mp hpq]

/-! The strong duality auxiliary proof is split because the original single proof exceeded the
LeanPool 200-line cap. We dispatch on the two cases coming from `extendedFarkas` and finish
each in its own helper. -/

private lemma ValidELP.strongDuality_aux_caseX (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible)
    {X : J ⊕ I → F≥0}
    (hX :
      Matrix.fromRows
        (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
        (Matrix.replicateRow Unit (Sum.elim P.c P.b)) ₘ* X ≤
      Sum.elim (Sum.elim P.b P.c) 0) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
  rw [
    Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
    ←Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff,
    ←Sum.elim_comp_inl_inr X, Matrix.fromCols_mulWeig_sumElim, Matrix.fromCols_mulWeig_sumElim,
    Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add
  ] at hX
  set x := X ∘ Sum.inl
  set y := X ∘ Sum.inr
  obtain ⟨⟨hx, hy⟩, hxy⟩ := hX
  have hxy := sumElim_dotWeig_sumElim P.c P.b x y ▸ hxy 0
  match hcx : P.c ᵥ⬝ x with
  | ⊥ =>
    exact P.dualize.no_bot_of_feasible hQ (dotWeig_eq_bot.← hcx).choose (dotWeig_eq_bot.← hcx).choose_spec
  | ⊤ =>
    match hby : P.b ᵥ⬝ y with
    | ⊥ => exact P.no_bot_of_feasible hP (dotWeig_eq_bot.← hby).choose (dotWeig_eq_bot.← hby).choose_spec
    | ⊤ | (_ : F) => simp [hcx, hby] at hxy
  | (p : F) =>
    match hby : P.b ᵥ⬝ y with
    | ⊥ => exact P.no_bot_of_feasible hP (dotWeig_eq_bot.← hby).choose (dotWeig_eq_bot.← hby).choose_spec
    | ⊤ => simp [hcx, hby] at hxy
    | (q : F) =>
      exact ⟨p, q, ⟨x, hx, hcx⟩, ⟨y, hy, hby⟩, EF.coe_le_coe_iff.← (hcx ▸ hby ▸ hxy)⟩

private lemma ValidELP.strongDuality_aux_caseY (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible)
    {Y : (I ⊕ J) ⊕ Unit → F≥0}
    (hAY :
      -(Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.replicateRow Unit (Sum.elim P.c P.b)))ᵀ ₘ* Y ≤ 0)
    (hbc : Sum.elim (Sum.elim P.b P.c) 0 ᵥ⬝ Y < 0) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
  rw [
    Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_zero, Matrix.transpose_neg, Matrix.transpose_transpose,
    Matrix.transpose_replicateRow, Matrix.fromCols_neg,
    ←Sum.elim_comp_inl_inr Y, Matrix.fromCols_mulWeig_sumElim,
    Matrix.fromBlocks_neg, Matrix.EF_neg_neg, Matrix.EF_neg_zero, Matrix.EF_neg_zero,
    ←Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromRows_mulWeig,
    ←Sum.elim_comp_inl_inr (Y ∘ Sum.inl), Matrix.fromCols_mulWeig_sumElim,
    Matrix.fromCols_mulWeig_sumElim,
    Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add,
  ] at hAY
  rw [←Sum.elim_comp_inl_inr Y, ←Sum.elim_comp_inl_inr (Y ∘ Sum.inl)] at hbc
  set x := (Y ∘ Sum.inl) ∘ Sum.inr
  set y := (Y ∘ Sum.inl) ∘ Sum.inl
  set z := (Y ∘ Sum.inr) 0
  have hAyx' :
      Sum.elim (-P.Aᵀ ₘ* y) (P.A ₘ* x) + Sum.elim (z • (-P.c)) (z • (-P.b)) ≤ 0
  · convert hAY
    ext
    aesop [Matrix.replicateCol, Matrix.mulWeig, dotWeig, z]
  clear hAY
  rw [←Sum.elim_add_add, Sum.elim_nonpos_iff] at hAyx'
  obtain ⟨hy, hx⟩ := hAyx'
  rw [sumElim_dotWeig_sumElim, zero_dotWeig, add_zero, sumElim_dotWeig_sumElim] at hbc
  have z_pos : 0 < z
  · by_contra contr
    simp only [le_antisymm (not_lt.mp contr) z.property, zero_smul] at hx hy
    if hxc : P.c ᵥ⬝ x < 0 then
      exact P.infeasible_of_unbounded (P.unbounded_of_feasible_of_neg hP hxc hx) hQ
    else
      exact P.dualize.infeasible_of_unbounded
        (P.dualize.unbounded_of_feasible_of_neg hQ
          (lt_of_not_le (fun contr => (hbc.trans_le (add_nonneg contr (not_lt.mp hxc))).false)) hy)
        (P.dualize_dualize ▸ hP)
  match hcx : P.c ᵥ⬝ x with
  | ⊥ =>
    exact P.dualize.no_bot_of_feasible hQ (dotWeig_eq_bot.← hcx).choose (dotWeig_eq_bot.← hcx).choose_spec
  | ⊤ =>
    match hby : P.b ᵥ⬝ y with
    | ⊥ => exact P.no_bot_of_feasible hP (dotWeig_eq_bot.← hby).choose (dotWeig_eq_bot.← hby).choose_spec
    | ⊤ | (_ : F) => simp [hcx, hby] at hbc
  | (p : F) =>
    match hby : P.b ᵥ⬝ y with
    | ⊥ => exact P.no_bot_of_feasible hP (dotWeig_eq_bot.← hby).choose (dotWeig_eq_bot.← hby).choose_spec
    | ⊤ => simp [hcx, hby] at hbc
    | (q : F) =>
      have z_inv_pos : 0 < z⁻¹ := inv_pos_of_pos z_pos
      refine ⟨z⁻¹ * p, z⁻¹ * q, ⟨z⁻¹ • x, ?_, ?_⟩, ⟨z⁻¹ • y, ?_, ?_⟩, ?_⟩
      · rwa [
          ←EF.vec_smul_le_smul_left z_inv_pos, smul_zero,
          EF.smul_add_vec z_inv_pos, ←Matrix.mulWeig_smul z_inv_pos, ←EF.mul_smul_vec,
          inv_mul_cancel₀ (ne_of_lt z_pos).symm, EF.one_smul_vec, EF.vec_sub_nonpos_iff
        ] at hx
      · simp only [dotWeig_smul z_inv_pos, hcx]
      · rwa [
          ←EF.vec_smul_le_smul_left z_inv_pos, smul_zero,
          EF.smul_add_vec z_inv_pos, ←Matrix.mulWeig_smul z_inv_pos, ←EF.mul_smul_vec,
          inv_mul_cancel₀ (ne_of_lt z_pos).symm, EF.one_smul_vec, EF.vec_sub_nonpos_iff
        ] at hy
      · simp only [ValidELP.dualize, dotWeig_smul z_inv_pos, hby]
      rw [hcx, hby, ←mul_add] at hbc ⊢
      exact mul_nonpos_of_nonneg_of_nonpos z_inv_pos.le
        (le_of_lt (by rwa [←EF.coe_lt_coe_iff, add_comm] at hbc))

lemma ValidELP.strongDuality_aux (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
  cases
    or_of_neq
      (extendedFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.replicateRow Unit (Sum.elim P.c P.b)))
        (Sum.elim (Sum.elim P.b P.c) 0)
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ =>
                cases t with
                | inl jₜ =>
                  exact P.hAi
                    ⟨i, ⟨⟨jₛ, by simpa using hks⟩, ⟨jₜ, by simpa using hkt⟩⟩⟩
                | inr iₜ => simp at hkt
              | inr iₛ => simp at hks
            | inr j =>
              cases t with
              | inl jₜ => simp at hkt
              | inr iₜ =>
                cases s with
                | inl jₛ => simp at hks
                | inr iₛ =>
                  exact P.hAj
                    ⟨j, ⟨iₜ, by simpa using hkt⟩, ⟨iₛ, by simpa using hks⟩⟩
          | inr =>
            cases s with
            | inl jₛ => exact P.dualize.no_bot_of_feasible hQ jₛ hks
            | inr iₛ => exact P.no_bot_of_feasible hP iₛ hks
        )
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl j =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => exact P.hAj ⟨j, ⟨⟨iₛ, hks⟩, ⟨iₜ, hkt⟩⟩⟩
                  | inr jₜ => simp at hkt
                | inr => exact P.hAc ⟨j, ⟨iₛ, hks⟩, hkt⟩
              | inr jₛ => simp at hks
            | inr => exact P.dualize.no_bot_of_feasible hQ j hks
          | inr i =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ => simp at hks
              | inr jₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => simp at hkt
                  | inr jₜ =>
                    exact P.hAi
                      ⟨i, ⟨jₜ, by simpa using hkt⟩, ⟨jₛ, by simpa using hks⟩⟩
                | inr => exact P.hAb ⟨i, ⟨jₛ, by simpa using hks⟩, hkt⟩
            | inr => exact P.no_bot_of_feasible hP i hks
        )
        (by
          intro ⟨k, ⟨t, hkt⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases t with
              | inl jₜ => exact P.hAb ⟨i, ⟨jₜ, hkt⟩, hk⟩
              | inr iₜ => simp at hkt
            | inr j =>
              cases t with
              | inl jₜ => simp at hkt
              | inr iₜ => exact P.hAc ⟨j, ⟨iₜ, by simpa using hkt⟩, hk⟩
          | inr => simp at hk
        )
        (by
          intro ⟨k, ⟨s, hks⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ => exact P.no_bot_of_feasible hP i hk
              | inr iₛ => simp at hks
            | inr j =>
              cases s with
              | inl jₛ => simp at hks
              | inr iₛ => exact P.dualize.no_bot_of_feasible hQ j hk
          | inr => simp at hk
        )
      ) with
  | inl ⟨X, hX⟩ => exact P.strongDuality_aux_caseX hP hQ hX
  | inr ⟨Y, hAY, hbc⟩ => exact P.strongDuality_aux_caseY hP hQ hAY hbc

lemma ValidELP.strongDuality_of_both_feasible (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : F, P.Reaches (toE (-r)) ∧ P.dualize.Reaches (toE r) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := P.strongDuality_aux hP hQ
  exact ⟨q, (neg_eq_iff_add_eq_zero.mpr (add_comm q p ▸ le_antisymm hpq
    (EF.coe_le_coe_iff.← (EF.coe_add p q ▸ P.weakDuality hp hq)))) ▸ hp, hq⟩

end extended_LP_properties

section extended_LP_optima

lemma ExtendedLP.optimum_unique [Fintype J] {P : ExtendedLP I J F} {r s : F}
    (hPr : P.Reaches (toE r) ∧ P.IsBoundedBy r) (hPs : P.Reaches (toE s) ∧ P.IsBoundedBy s) :
    r = s :=
  EF.coe_eq_coe_iff.← (le_antisymm (hPr.right _ hPs.left) (hPs.right _ hPr.left))

lemma ExtendedLP.optimum_eq_of_reaches_bounded [Fintype J] {P : ExtendedLP I J F} {r : F}
    (reaches : P.Reaches (toE r)) (bounded : P.IsBoundedBy r) :
    P.optimum = some r := by
  have hP : P.IsFeasible := ⟨toE r, ⟨reaches.choose, reaches.choose_spec.1, reaches.choose_spec.2⟩, EF.coe_neq_top r⟩
  have hPb : ¬P.IsUnbounded := (· ⟨r, bounded⟩)
  unfold ExtendedLP.optimum
  rw [if_neg (not_not.mpr hP), if_neg hPb, dif_pos ⟨r, reaches, bounded⟩]
  exact congr_arg (some ∘ toE) (ExtendedLP.optimum_unique (Exists.choose_spec _) ⟨reaches, bounded⟩)

omit [IsStrictOrderedRing F] in
lemma oppositesOpt_comm (p q : Option F∞) : OppositesOpt p q ↔ OppositesOpt q p := by
  simp [OppositesOpt, neg_eq_iff_eq_neg]

variable [Fintype I] [Fintype J]

lemma ValidELP.strongDuality_of_prim_feasible (P : ValidELP I J F) (hP : P.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  if hQ : P.dualize.IsFeasible then
    obtain ⟨r, hPr, hQr⟩ := P.strongDuality_of_both_feasible hP hQ
    rw [ExtendedLP.optimum_eq_of_reaches_bounded hPr
      (fun p hPp =>
        match p with
        | ⊥ => by simp at (P.weakDuality hPp hQr)
        | ⊤ => le_top
        | (_ : F) => by
          have Pwd := P.weakDuality hPp hQr
          simp only [←EF.coe_add, ←EF.coe_zero, EF.coe_le_coe_iff] at Pwd ⊢
          linarith),
      ExtendedLP.optimum_eq_of_reaches_bounded hQr
      (fun q hQq =>
        match q with
        | ⊥ => by simp at (P.weakDuality hPr hQq)
        | ⊤ => le_top
        | (_ : F) => by
          have Qwd := P.weakDuality hPr hQq
          simp only [←EF.coe_add, ←EF.coe_zero, EF.coe_le_coe_iff] at Qwd ⊢
          linarith)]
    rfl
  else
    simp only [ExtendedLP.optimum, P.unbounded_of_feasible_of_infeasible hP hQ, hP, hQ,
      not_false_eq_true, ite_true, ite_false, OppositesOpt, EF.neg_top]

omit [Fintype I] in
theorem ValidELP.optimum_neq_none [Finite I] (P : ValidELP I J F) : P.optimum ≠ none := by
  letI : Fintype I := Fintype.ofFinite I
  if hP : P.IsFeasible then
    intro contr
    simpa [contr, OppositesOpt] using P.strongDuality_of_prim_feasible hP
  else
    simp [ExtendedLP.optimum, hP]

lemma ValidELP.strongDuality_of_dual_feasible (P : ValidELP I J F) (hP : P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  rw [oppositesOpt_comm]
  nth_rw 2 [P.dualize_dualize]
  exact P.dualize.strongDuality_of_prim_feasible hP

theorem ValidELP.strongDuality (P : ValidELP I J F) (hP : P.IsFeasible ∨ P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum :=
  hP.casesOn
    (P.strongDuality_of_prim_feasible ·)
    (P.strongDuality_of_dual_feasible ·)

end extended_LP_optima

end strong_duality
