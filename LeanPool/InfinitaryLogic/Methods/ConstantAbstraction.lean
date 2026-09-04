/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# Constant abstraction and reinterpretation surgery (issue #8 kernel steps 3–5)

The genuinely uncertain freshness mechanism of the Craig interpolation arc
(`docs/craig-audit.md` §6a). Over a constant expansion `L[[ℕ]]` with a fixed base `L`-structure
on `M`:

* `BoundedFormulaω.realize_congr_instances` — realization depends only on the interpretation of
  the symbols (two `L`-structure instances agreeing on all `funMap`/`RelMap` values realize
  identically). Used for the ambient bridge.
* `wc base h` — the `L[[ℕ]]`-structure with base reduct `base` and constants interpreted by
  `h : ℕ → M`; `ambient_realize_iff_wc` bridges an arbitrary ambient `L[[ℕ]]`-structure to this
  controlled form.
* `realize_congr_const` — realization is unchanged by altering the constant interpretation off
  the formula's constant support (`sentenceJConsts`); the invariance-outside-support engine
  (Claim A of the acceptance argument).
* `BoundedFormulaω.abstractConst j` — withdraw the constant `c_j` into the free variable `0`
  (`Empty`-based `→` `Fin 1`-based), with the occurrence-deletion lemma.
* `realize_abstractConst` — the reinterpretation engine (Claim B): realizing the abstracted
  formula at a witness `a` equals realizing the original with `c_j` reinterpreted to `a`.

Pure realization surgery: no `InsepAt`, no interpolation-specific commitments.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {M : Type} {α β : Type}

/-! ## Two-instance realization congruence -/

/-- Term realization depends only on the `funMap` values: two `L`-structure instances agreeing
on every `funMap` realize every term identically. -/
private theorem Term.realize_congr_instances (S S' : L.Structure M)
    (hf : ∀ {l} (f : L.Functions l) (x : Fin l → M),
      @Structure.funMap L M S l f x = @Structure.funMap L M S' l f x)
    (v : α → M) (t : L.Term α) :
    @Term.realize L M S α v t = @Term.realize L M S' α v t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    show @Structure.funMap L M S _ f _ = @Structure.funMap L M S' _ f _
    rw [hf]
    exact congrArg _ (funext ih)

/-- Realization depends only on the `funMap`/`RelMap` values: two `L`-structure instances
agreeing on all interpretations realize every formula identically. -/
private theorem BoundedFormulaω.realize_congr_instances (S S' : L.Structure M)
    (hf : ∀ {l} (f : L.Functions l) (x : Fin l → M),
      @Structure.funMap L M S l f x = @Structure.funMap L M S' l f x)
    (hr : ∀ {l} (R : L.Relations l) (x : Fin l → M),
      @Structure.RelMap L M S l R x ↔ @Structure.RelMap L M S' l R x) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M),
      @BoundedFormulaω.Realize L M S α n φ v xs ↔ @BoundedFormulaω.Realize L M S' α n φ v xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; exact Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    show @Term.realize L M S _ _ t₁ = @Term.realize L M S _ _ t₂
      ↔ @Term.realize L M S' _ _ t₁ = @Term.realize L M S' _ _ t₂
    rw [Term.realize_congr_instances S S' hf, Term.realize_congr_instances S S' hf]
  | rel R ts =>
    intro v xs
    show @Structure.RelMap L M S _ R _ ↔ @Structure.RelMap L M S' _ R _
    rw [show (fun i => @Term.realize L M S _ _ (ts i)) = (fun i => @Term.realize L M S' _ _ (ts i))
        from funext fun i => Term.realize_congr_instances S S' hf _ _]
    exact hr R _
  | imp φ ψ ihφ ihψ =>
    intro v xs
    show (_ → _) ↔ (_ → _)
    -- apply the induction hypotheses rather than rewriting: they are stated through the reducible
    -- `BoundedFormulaω.Realize` alias, which `rw` cannot key against the unfolded goal
    exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    exact forall_congr' fun x => ih v (Fin.snoc xs x)
  | iSup φs ih =>
    intro v xs
    exact exists_congr fun i => ih i v xs
  | iInf φs ih =>
    intro v xs
    exact forall_congr' fun i => ih i v xs

/-! ## The controlled single-layer structure `wc base h` -/

/-- The `L[[ℕ]]`-structure on `M` with base reduct `base` and constants interpreted by `h`. -/
@[reducible] def wc (base : L.Structure M) (h : ℕ → M) : L[[ℕ]].Structure M :=
  @Language.withConstantsStructure L M base ℕ (constantsOn.structure h)

@[simp] theorem wc_funMap_inl (base : L.Structure M) (h : ℕ → M) {l : ℕ}
    (f : L.Functions l) (x : Fin l → M) :
    @Structure.funMap L[[ℕ]] M (wc base h) l (Sum.inl f) x = @Structure.funMap L M base l f x :=
  rfl

@[simp] theorem wc_funMap_inr (base : L.Structure M) (h : ℕ → M) (k : ℕ) (x : Fin 0 → M) :
    @Structure.funMap L[[ℕ]] M (wc base h) 0 (Sum.inr k) x = h k :=
  rfl



/-- The interpretation of the constant `c_k` by an ambient `L[[ℕ]]`-structure. -/
def ambientConstMap (M : Type) [S : L[[ℕ]].Structure M] (k : ℕ) : M :=
  @Structure.funMap L[[ℕ]] M S 0 (Sum.inr k) Fin.elim0

/-- **The ambient bridge**: any ambient `L[[ℕ]]`-structure realizes exactly as the controlled
structure built from its base reduct and its constant interpretation. -/
theorem ambient_realize_iff_wc [S : L[[ℕ]].Structure M] {n : ℕ}
    (φ : L[[ℕ]].BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    @BoundedFormulaω.Realize L[[ℕ]] M S α n φ v xs ↔
      @BoundedFormulaω.Realize L[[ℕ]] M
        (wc ((L.lhomWithConstants ℕ).reduct M) (ambientConstMap (L := L) M)) α n φ v xs := by
  refine BoundedFormulaω.realize_congr_instances S _ ?_ ?_ φ v xs
  · intro l f x
    rcases f with f | k
    · rfl
    · match l, k with
      | 0, k =>
        show @Structure.funMap L[[ℕ]] M S 0 (Sum.inr k) x = ambientConstMap M k
        simp only [ambientConstMap]
        exact congrArg _ (Subsingleton.elim _ _)
      | (l + 1), k => exact isEmptyElim k
  · intro l R x
    rcases R with R | e
    · exact Iff.rfl
    · exact isEmptyElim e

/-! ## Invariance outside the constant support -/

/-- Two constant maps agreeing on a term's constant support give the term the same value. -/
theorem Term.realize_congr_const (base : L.Structure M) {h h' : ℕ → M} {n : ℕ}
    (t : L[[ℕ]].Term (α ⊕ Fin n))
    (hagree : ∀ k, (⟨0, (Sum.inr k : L[[ℕ]].Functions 0)⟩ : Σ l, L[[ℕ]].Functions l) ∈
      Term.functionsIn t → h k = h' k) (w : (α ⊕ Fin n) → M) :
    @Term.realize L[[ℕ]] M (wc base h) _ w t = @Term.realize L[[ℕ]] M (wc base h') _ w t := by
  induction t with
  | var x => rfl
  | @func l f ts ih =>
    have hmem : ∀ (i : Fin l) (s : Σ l, L[[ℕ]].Functions l),
        s ∈ Term.functionsIn (ts i) → s ∈ Term.functionsIn (Term.func f ts) := fun i s hs => by
      simp only [Term.functionsIn]
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_iUnion.mpr ⟨i, hs⟩))
    have hargs : ∀ i, @Term.realize L[[ℕ]] M (wc base h) _ w (ts i)
        = @Term.realize L[[ℕ]] M (wc base h') _ w (ts i) :=
      fun i => ih i fun k hk => hagree k (hmem i _ hk)
    rcases f with f | k
    · show @Structure.funMap L[[ℕ]] M (wc base h) _ (Sum.inl f) _
        = @Structure.funMap L[[ℕ]] M (wc base h') _ (Sum.inl f) _
      simp only [wc_funMap_inl]
      exact congrArg _ (funext hargs)
    · match l, k with
      | 0, k =>
        show @Structure.funMap L[[ℕ]] M (wc base h) 0 (Sum.inr k) _
          = @Structure.funMap L[[ℕ]] M (wc base h') 0 (Sum.inr k) _
        exact hagree k (by simp only [Term.functionsIn]; exact Set.mem_insert _ _)
      | (l + 1), k => exact isEmptyElim k

/-- **Invariance outside the constant support** (Claim A): altering the constant interpretation
off a formula's constant support does not change its realization. -/
theorem BoundedFormulaω.realize_congr_const (base : L.Structure M) {h h' : ℕ → M} :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω α n)
      (_ : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) φ, h k = h' k)
      (v : α → M) (xs : Fin n → M),
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) α n φ v xs
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h') α n φ v xs := by
  intro n φ
  induction φ with
  | falsum => intro _ v xs; exact Iff.rfl
  | equal t₁ t₂ =>
    intro hagree v xs
    show @Term.realize L[[ℕ]] M (wc base h) _ _ t₁ = @Term.realize L[[ℕ]] M (wc base h) _ _ t₂
      ↔ @Term.realize L[[ℕ]] M (wc base h') _ _ t₁ = @Term.realize L[[ℕ]] M (wc base h') _ _ t₂
    rw [Term.realize_congr_const base t₁
        (fun k hk => hagree k (Set.mem_union_left _ hk)),
      Term.realize_congr_const base t₂
        (fun k hk => hagree k (Set.mem_union_right _ hk))]
  | rel R ts =>
    intro hagree v xs
    show @Structure.RelMap L[[ℕ]] M (wc base h) _ R _ ↔ @Structure.RelMap L[[ℕ]] M (wc base h') _ R _
    rw [show (fun i => @Term.realize L[[ℕ]] M (wc base h) _ (Sum.elim v xs) (ts i))
          = (fun i => @Term.realize L[[ℕ]] M (wc base h') _ (Sum.elim v xs) (ts i))
        from funext fun i => Term.realize_congr_const base (ts i)
          (fun k hk => hagree k (Set.mem_iUnion.mpr ⟨i, hk⟩)) _]
    rcases R with R | e
    · exact Iff.rfl
    · exact isEmptyElim e
  | imp φ ψ ihφ ihψ =>
    intro hagree v xs
    show (_ → _) ↔ (_ → _)
    exact imp_congr (ihφ (fun k hk => hagree k (sentenceJConsts_imp_left _ _ hk)) v xs)
      (ihψ (fun k hk => hagree k (sentenceJConsts_imp_right _ _ hk)) v xs)
  | all φ ih =>
    intro hagree v xs
    exact forall_congr' fun x => ih hagree v (Fin.snoc xs x)
  | iSup φs ih =>
    intro hagree v xs
    exact exists_congr fun i => ih i (fun k hk => hagree k (sentenceJConsts_component_iSup _ i hk)) v xs
  | iInf φs ih =>
    intro hagree v xs
    exact forall_congr' fun i => ih i (fun k hk => hagree k (sentenceJConsts_component_iInf _ i hk)) v xs

/-! ## Constant abstraction -/

open Classical in
/-- Withdraw the constant `c_j` from a term into the fresh free variable `0 : Fin 1`. The
free-variable side moves `Empty → Fin 1`; the bound side is unchanged. (Uses classical
decidability on the constant index; only ever run in proofs.) -/
noncomputable def Term.abstractConst (j : ℕ) {n : ℕ} :
    L[[ℕ]].Term (Empty ⊕ Fin n) → L[[ℕ]].Term (Fin 1 ⊕ Fin n)
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr i) => .var (Sum.inr i)
  | .func (Sum.inl f) ts => .func (Sum.inl f) fun i => (ts i).abstractConst j
  | @Term.func _ _ 0 (Sum.inr k) _ =>
    if (k : ℕ) = j then .var (Sum.inl 0) else .func (Sum.inr k) Fin.elim0
  | @Term.func _ _ (_ + 1) (Sum.inr k) _ => nomatch k

/-- Withdraw the constant `c_j` from a formula into the fresh free variable `0 : Fin 1`. -/
noncomputable def BoundedFormulaω.abstractConst (j : ℕ) :
    ∀ {n : ℕ}, L[[ℕ]].BoundedFormulaω Empty n → L[[ℕ]].BoundedFormulaω (Fin 1) n
  | _, .falsum => .falsum
  | _, .equal t u => .equal (t.abstractConst j) (u.abstractConst j)
  | _, .rel R ts => .rel R fun i => (ts i).abstractConst j
  | _, .imp φ ψ => .imp (φ.abstractConst j) (ψ.abstractConst j)
  | _, .all φ => .all (φ.abstractConst j)
  | _, .iSup φs => .iSup fun i => (φs i).abstractConst j
  | _, .iInf φs => .iInf fun i => (φs i).abstractConst j

/-! ## The reinterpretation engine (Claim B) -/

/-- Term reinterpretation: the abstracted term evaluated with the free variable at `a` equals
the original term with `c_j` reinterpreted to `a`. -/
theorem Term.realize_abstractConst (base : L.Structure M) (h : ℕ → M) (j : ℕ) (a : M) {n : ℕ}
    (xs : Fin n → M) (t : L[[ℕ]].Term (Empty ⊕ Fin n)) :
    @Term.realize L[[ℕ]] M (wc base h) _ (Sum.elim (fun _ => a) xs) (t.abstractConst j)
      = @Term.realize L[[ℕ]] M (wc base (Function.update h j a)) _
          (Sum.elim Empty.elim xs) t := by
  induction t with
  | var x =>
    rcases x with e | i
    · exact e.elim
    · rfl
  | @func l f ts ih =>
    rcases f with f | k
    · show @Structure.funMap L[[ℕ]] M (wc base h) _ (Sum.inl f) _
        = @Structure.funMap L[[ℕ]] M (wc base (Function.update h j a)) _ (Sum.inl f) _
      simp only [wc_funMap_inl]
      exact congrArg _ (funext ih)
    · match l, k with
      | 0, k =>
        have : DecidableEq ((constantsOn ℕ).Functions 0) := inferInstanceAs (DecidableEq ℕ)
        show @Term.realize L[[ℕ]] M (wc base h) _ (Sum.elim (fun _ => a) xs)
            (Term.abstractConst j (Term.func (Sum.inr k) Fin.elim0))
          = @Structure.funMap L[[ℕ]] M (wc base (Function.update h j a)) 0 (Sum.inr k) _
        by_cases hk : (k : ℕ) = j
        · have habs : Term.abstractConst j (Term.func (Sum.inr k) Fin.elim0)
              = (Term.var (Sum.inl 0) : L[[ℕ]].Term (Fin 1 ⊕ Fin n)) := by
            simp only [Term.abstractConst]; rw [ite_eq_left hk]
          rw [habs]
          show (Sum.elim (fun _ => a) xs) (Sum.inl (0 : Fin 1)) = Function.update h j a (k : ℕ)
          rw [Sum.elim_inl, hk, Function.update_self]
        · have habs : Term.abstractConst j (Term.func (Sum.inr k) Fin.elim0)
              = (Term.func (Sum.inr k) Fin.elim0 : L[[ℕ]].Term (Fin 1 ⊕ Fin n)) := by
            simp only [Term.abstractConst]; rw [ite_eq_right hk]
          rw [habs]
          show h k = Function.update h j a (k : ℕ)
          have key : Function.update h j a (k : ℕ) = h (k : ℕ) :=
            Function.update_of_ne (α := ℕ) (a := (k : ℕ)) (a' := j) (fun heq => hk heq) a h
          exact key.symm
      | (l + 1), k => exact nomatch k

/-- **The reinterpretation engine** (Claim B): realizing the abstracted formula at a witness `a`
equals realizing the original with `c_j` reinterpreted to `a`. -/
theorem BoundedFormulaω.realize_abstractConst (base : L.Structure M) (h : ℕ → M) (j : ℕ) (a : M) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) (xs : Fin n → M),
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) (Fin 1) n (φ.abstractConst j)
          (fun _ => a) xs
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j a)) Empty n φ
            Empty.elim xs := by
  intro n φ
  induction φ with
  | falsum => intro xs; exact Iff.rfl
  | equal t u =>
    intro xs
    show @Term.realize L[[ℕ]] M (wc base h) _ _ (t.abstractConst j)
        = @Term.realize L[[ℕ]] M (wc base h) _ _ (u.abstractConst j)
      ↔ @Term.realize L[[ℕ]] M (wc base (Function.update h j a)) _ _ t
        = @Term.realize L[[ℕ]] M (wc base (Function.update h j a)) _ _ u
    rw [Term.realize_abstractConst base h j a xs t, Term.realize_abstractConst base h j a xs u]
  | rel R ts =>
    intro xs
    show @Structure.RelMap L[[ℕ]] M (wc base h) _ R _
      ↔ @Structure.RelMap L[[ℕ]] M (wc base (Function.update h j a)) _ R _
    rw [show (fun i => @Term.realize L[[ℕ]] M (wc base h) _
            (Sum.elim (fun _ => a) xs) ((ts i).abstractConst j))
          = (fun i => @Term.realize L[[ℕ]] M (wc base (Function.update h j a)) _
            (Sum.elim Empty.elim xs) (ts i))
        from funext fun i => Term.realize_abstractConst base h j a xs (ts i)]
    rcases R with R | e
    · exact Iff.rfl
    · exact isEmptyElim e
  | imp φ ψ ihφ ihψ =>
    intro xs
    show (_ → _) ↔ (_ → _)
    exact imp_congr (ihφ xs) (ihψ xs)
  | all φ ih =>
    intro xs
    exact forall_congr' fun x => ih (Fin.snoc xs x)
  | iSup φs ih =>
    intro xs
    exact exists_congr fun i => ih i xs
  | iInf φs ih =>
    intro xs
    exact forall_congr' fun i => ih i xs

/-! ## Occurrence deletion: abstraction removes `c_j` and adds no new constants -/

/-- Abstraction adds no new function symbols to a term. -/
theorem Term.functionsIn_abstractConst_subset (j : ℕ) {n : ℕ} :
    ∀ (t : L[[ℕ]].Term (Empty ⊕ Fin n)),
      (t.abstractConst j).functionsIn ⊆ t.functionsIn := by
  intro t
  induction t with
  | var x =>
    rcases x with e | i
    · exact e.elim
    · intro s hs; exact absurd hs (Set.notMem_empty s)
  | @func l f ts ih =>
    rcases f with f | k
    · intro s hs
      simp only [Term.abstractConst, Term.functionsIn] at hs ⊢
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact Set.mem_insert _ _
      · obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
        exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨i, ih i hmem⟩)
    · match l, k with
      | 0, k =>
        by_cases hk : (k : ℕ) = j
        · have hred : (Term.func (Sum.inr k) ts).abstractConst j
              = (Term.var (Sum.inl 0) : L[[ℕ]].Term (Fin 1 ⊕ Fin n)) := by
            simp only [Term.abstractConst]; rw [ite_eq_left hk]
          rw [hred]; intro s hs; exact absurd hs (Set.notMem_empty s)
        · have hred : (Term.func (Sum.inr k) ts).abstractConst j
              = (Term.func (Sum.inr k) Fin.elim0 : L[[ℕ]].Term (Fin 1 ⊕ Fin n)) := by
            simp only [Term.abstractConst]; rw [ite_eq_right hk]
          rw [hred]; intro s hs
          simp only [Term.functionsIn, Set.iUnion_of_empty,
            Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hs ⊢
          exact hs
      | (l + 1), k => exact nomatch k

/-- The constant `c_j` does not occur in the abstracted term. -/
private theorem Term.notMem_functionsIn_abstractConst (j : ℕ) {n : ℕ} :
    ∀ (t : L[[ℕ]].Term (Empty ⊕ Fin n)),
      (⟨0, (Sum.inr j : L[[ℕ]].Functions 0)⟩ : Σ l, L[[ℕ]].Functions l)
        ∉ (t.abstractConst j).functionsIn := by
  intro t
  induction t with
  | var x =>
    rcases x with e | i
    · exact e.elim
    · exact Set.notMem_empty _
  | @func l f ts ih =>
    rcases f with f | k
    · intro hs
      simp only [Term.abstractConst, Term.functionsIn] at hs
      rcases Set.mem_insert_iff.mp hs with heq | hs
      · cases heq
      · obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
        exact ih i hmem
    · match l, k with
      | 0, k =>
        by_cases hk : (k : ℕ) = j
        · have hred : (Term.func (Sum.inr k) ts).abstractConst j
              = (Term.var (Sum.inl 0) : L[[ℕ]].Term (Fin 1 ⊕ Fin n)) := by
            simp only [Term.abstractConst]; rw [ite_eq_left hk]
          rw [hred]; exact Set.notMem_empty _
        · have hred : (Term.func (Sum.inr k) ts).abstractConst j
              = (Term.func (Sum.inr k) Fin.elim0 : L[[ℕ]].Term (Fin 1 ⊕ Fin n)) := by
            simp only [Term.abstractConst]; rw [ite_eq_right hk]
          rw [hred]; intro hs
          simp only [Term.functionsIn, Set.iUnion_of_empty,
            Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hs
          exact hk (Sum.inr.inj (eq_of_heq (Sigma.mk.inj_iff.mp hs).2)).symm
      | (l + 1), k => exact nomatch k

/-- Abstraction adds no new function symbols to a formula. -/
theorem BoundedFormulaω.functionsIn_abstractConst_subset (j : ℕ) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
      (φ.abstractConst j).functionsIn ⊆ φ.functionsIn := by
  intro n φ
  induction φ with
  | falsum => exact subset_rfl
  | equal t u =>
    exact Set.union_subset_union (Term.functionsIn_abstractConst_subset j t)
      (Term.functionsIn_abstractConst_subset j u)
  | rel R ts => exact Set.iUnion_mono fun i => Term.functionsIn_abstractConst_subset j (ts i)
  | imp φ ψ ihφ ihψ => exact Set.union_subset_union ihφ ihψ
  | all φ ih => exact ih
  | iSup φs ih => exact Set.iUnion_mono ih
  | iInf φs ih => exact Set.iUnion_mono ih

/-- The constant `c_j` does not occur in the abstracted formula. -/
private theorem BoundedFormulaω.notMem_functionsIn_abstractConst (j : ℕ) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
      (⟨0, (Sum.inr j : L[[ℕ]].Functions 0)⟩ : Σ l, L[[ℕ]].Functions l)
        ∉ (φ.abstractConst j).functionsIn := by
  intro n φ
  induction φ with
  | falsum => exact Set.notMem_empty _
  | equal t u =>
    intro hs
    rcases hs with hs | hs
    · exact Term.notMem_functionsIn_abstractConst j t hs
    · exact Term.notMem_functionsIn_abstractConst j u hs
  | rel R ts =>
    intro hs
    obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
    exact Term.notMem_functionsIn_abstractConst j (ts i) hmem
  | imp φ ψ ihφ ihψ =>
    intro hs
    rcases hs with hs | hs
    · exact ihφ hs
    · exact ihψ hs
  | all φ ih => exact ih
  | iSup φs ih =>
    intro hs
    obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
    exact ih i hmem
  | iInf φs ih =>
    intro hs
    obtain ⟨_, ⟨i, rfl⟩, hmem⟩ := hs
    exact ih i hmem

/-- Abstraction preserves the relation symbols exactly. -/
theorem BoundedFormulaω.relationsIn_abstractConst (j : ℕ) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
      (φ.abstractConst j).relationsIn = φ.relationsIn := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t u => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaω.abstractConst, BoundedFormulaω.relationsIn, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.abstractConst, BoundedFormulaω.relationsIn, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.abstractConst, BoundedFormulaω.relationsIn]
    exact congrArg _ (funext ih)
  | iInf φs ih =>
    simp only [BoundedFormulaω.abstractConst, BoundedFormulaω.relationsIn]
    exact congrArg _ (funext ih)

/-- `c_j` is not in the constant support of the abstracted formula. -/
theorem BoundedFormulaω.notMem_sentenceJConsts_abstractConst (j : ℕ) {n : ℕ}
    (φ : L[[ℕ]].BoundedFormulaω Empty n) :
    j ∉ sentenceJConsts (L' := L) (J := ℕ) (φ.abstractConst j) :=
  BoundedFormulaω.notMem_functionsIn_abstractConst j φ



end FirstOrder.Language

