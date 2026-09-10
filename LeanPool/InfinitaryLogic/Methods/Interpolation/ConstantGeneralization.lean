/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.ConstantElimination
import LeanPool.InfinitaryLogic.Lomega1omega.QuantifierClass
import LeanPool.InfinitaryLogic.Lomega1omega.QuantifierOccurrence
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
/-!
# Constant generalization: the `∀`-twin of `genEx`, and countable-conjunction bounds

Neutral companion to `ConstantElimination.lean`.  Where `genEx j ρ` existentially generalizes the
constant `c_j` out of a sentence, `genAll j ρ` generalizes it **universally**, with the matching
realization lemma, occurrence calculus, and the two entailment-acceptance sequents:

* `entails_genAll_of_entails` (side 1): `Γ ⊨ σ(c) ⟹ Γ ⊨ ∀x σ(x)`, `c` fresh for `Γ`.  Unlike
  `genEx`'s side-1 sequent this genuinely **needs** freshness — `∀`-introduction is not weakening;
* `entails_not_genAll_of_entails_not` (side 2): `Δ, δ(c) ⊨ ¬σ(c) ⟹ Δ, ∃x δ(x) ⊨ ¬∀x σ(x)`,
  `c` fresh for `Δ`.

`genAll` is **class-preserving** for the quantifier hierarchy of `Lomega1omega/QuantifierClass.lean`
(`isUniversal_genAll`), because `all` is admissible at the universal sign and neither constant
abstraction nor `relabel` moves the class; `genEx`, dually, is never universal
(`not_isUniversal_genEx`).  That pair of facts is what makes an asymmetric separator class possible
at all, so both live here rather than inside any one consumer.

The second half collects the class and occurrence bounds for `Theoryω.conjunction`, the
countable conjunction of a theory: existentiality and the three symbol/support bounds descend from
the members.

Nothing here is specific to Malitz interpolation (issue #15) or to end extensions (issue #16); both
consume it.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type}
variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}

/-! ## `genAll`: universal generalization of a fresh constant -/

/-- Universally generalize the constant `c_j` out of a sentence: abstract `c_j` into the free
variable `0`, then universally quantify it.  The `∀`-twin of `genEx`. -/
noncomputable def genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) : L[[ℕ]].Sentenceω :=
  ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all

/-- Realizing the universal generalization is realizing the original at every reinterpretation of
`c_j`. -/
private theorem realize_genAll (base : L.Structure M) (h : ℕ → M) (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genAll j ρ) Empty.elim Fin.elim0
      ↔ ∀ x, @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 ρ
          Empty.elim Fin.elim0 := by
  let : L[[ℕ]].Structure M := wc base h
  have hval : ∀ x : M, (Fin.snoc Fin.elim0 x : Fin 1 → M) = (fun _ => x) := by
    intro x; funext i; simp [Fin.snoc, Fin.eq_zero i]
  rw [genAll, BoundedFormulaω.realize_all]
  refine forall_congr' fun x => ?_
  rw [BoundedFormulaω.realize_relabel_sumInr_zero (ρ.abstractConst j) (Fin.snoc Fin.elim0 x),
    hval x]
  exact BoundedFormulaω.realize_abstractConst base h j x ρ Fin.elim0

/-- `c_j` is not in the constant support of its own universal generalization. -/
theorem notMem_sentenceJConsts_genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    j ∉ sentenceJConsts (L' := L) (J := ℕ) (genAll j ρ) := by
  rw [genAll]
  intro hmem
  have h2 : sentenceJConsts (L' := L) (J := ℕ)
      (((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all)
      = sentenceJConsts (L' := L) (J := ℕ) (ρ.abstractConst j) := by
    unfold sentenceJConsts
    rw [show ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all.functionsIn
      = ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).functionsIn from rfl,
      BoundedFormulaω.functionsIn_relabel]
  rw [h2] at hmem
  exact BoundedFormulaω.notMem_sentenceJConsts_abstractConst j ρ hmem

/-! ### Occurrence facts for `genAll` -/

private theorem functionsIn_genAll_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).functionsIn ⊆ ρ.functionsIn := by
  rw [genAll,
    show (((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all).functionsIn
      = ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).functionsIn from rfl,
    BoundedFormulaω.functionsIn_relabel]
  exact BoundedFormulaω.functionsIn_abstractConst_subset j ρ

theorem baseFunctionsIn_genAll_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).baseFunctionsIn ⊆ ρ.baseFunctionsIn :=
  fun _ hs => functionsIn_genAll_subset j ρ hs

private theorem relationsIn_genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).relationsIn = ρ.relationsIn := by
  rw [genAll,
    show (((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all).relationsIn
      = ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).relationsIn from rfl,
    BoundedFormulaω.relationsIn_relabel, BoundedFormulaω.relationsIn_abstractConst]

theorem baseRelationsIn_genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).baseRelationsIn = ρ.baseRelationsIn := by
  unfold BoundedFormulaω.baseRelationsIn
  rw [relationsIn_genAll]

theorem sentenceJConsts_genAll_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    sentenceJConsts (L' := L) (J := ℕ) (genAll j ρ) ⊆ sentenceJConsts (L' := L) (J := ℕ) ρ :=
  fun _ hs => functionsIn_genAll_subset j ρ hs

/-! ### The quantifier class of `genAll` (and the `genEx` non-fact) -/

/-- Constant abstraction does not move the quantifier class. -/
private theorem BoundedFormulaω.universalSigned_abstractConst (j : ℕ) (s : Bool) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
      universalSigned s (BoundedFormulaω.abstractConst j φ) ↔ universalSigned s φ := by
  intro n φ
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal t u => exact Iff.rfl
  | rel R ts => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    -- induction-bound receivers carry the inductive type, so they need the qualified name
    change universalSigned (!s) (BoundedFormulaω.abstractConst j φ) ∧
        universalSigned s (BoundedFormulaω.abstractConst j ψ) ↔ _
    exact and_congr (ihφ (!s)) (ihψ s)
  | all φ ih =>
    change s = true ∧ universalSigned s (BoundedFormulaω.abstractConst j φ) ↔ _
    exact and_congr_right fun _ => ih s
  | iSup φs ih =>
    change (∀ i, universalSigned s (BoundedFormulaω.abstractConst j (φs i))) ↔ _
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    change (∀ i, universalSigned s (BoundedFormulaω.abstractConst j (φs i))) ↔ _
    exact forall_congr' fun i => ih i s

/-- **The exact signed-occurrence equation for `genAll`.**  Universal generalization adds one
positive occurrence and moves nothing else: at sign `true` the right disjunct is absorbed, and at
sign `false` the occurrences are exactly those of `ρ`.

This is what lets a labelled budget absorb a generalization whose universal parent already sits on
the same side. -/
theorem hasQuantSigned_genAll (j : ℕ) (s : Bool) (ρ : L[[ℕ]].Sentenceω) :
    hasQuantSigned s (genAll j ρ) ↔ (s = true ∨ hasQuantSigned s ρ) := by
  rw [genAll, BoundedFormulaω.hasQuantSigned_all, BoundedFormulaω.hasQuantSigned_relabel]
  refine or_congr_right ?_
  have h1 := BoundedFormulaω.universalSigned_iff_not_hasQuantSigned (!s) (ρ.abstractConst j)
  have h2 := BoundedFormulaω.universalSigned_iff_not_hasQuantSigned (!s) ρ
  rw [Bool.not_not] at h1 h2
  rw [← not_iff_not, ← h1, ← h2, BoundedFormulaω.universalSigned_abstractConst]

/-- **The exact signed-occurrence equation for `genEx`**, the dual of `hasQuantSigned_genAll`:
existential generalization adds one negative occurrence and moves nothing else. -/
theorem hasQuantSigned_genEx (j : ℕ) (s : Bool) (ρ : L[[ℕ]].Sentenceω) :
    hasQuantSigned s (genEx j ρ) ↔ (s = false ∨ hasQuantSigned s ρ) := by
  rw [genEx, BoundedFormulaω.hasQuantSigned_ex, BoundedFormulaω.hasQuantSigned_relabel]
  refine or_congr_right ?_
  have h1 := BoundedFormulaω.universalSigned_iff_not_hasQuantSigned (!s) (ρ.abstractConst j)
  have h2 := BoundedFormulaω.universalSigned_iff_not_hasQuantSigned (!s) ρ
  rw [Bool.not_not] at h1 h2
  rw [← not_iff_not, ← h1, ← h2, BoundedFormulaω.universalSigned_abstractConst]

/-! ### The `genAll` acceptance sequents -/

variable {j : ℕ} {φc σc : L[[ℕ]].Sentenceω} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- **Acceptance, `Γ` side**: `Γ ⊨ σ(c)` upgrades to `Γ ⊨ ∀x σ(x)` when `c_j` is fresh for `Γ`.
Unlike `genEx`'s `Γ`-side sequent this genuinely needs freshness — `∀`-introduction is not
weakening. -/
theorem entails_genAll_of_entails
    (hfresh : ∀ γ ∈ Γ, j ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hyp : Theoryω.Entails Γ σc) : Theoryω.Entails Γ (genAll j σc) := by
  intro M instM neM hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  refine (bridge _).mpr ((realize_genAll base h j σc).mpr fun x => ?_)
  have hΓ : ∀ γ ∈ Γ,
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 γ
        Empty.elim Fin.elim0 := by
    intro γ hγ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 γ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ hγ)
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ, h k = Function.update h j x k := by
      intro k hk
      have hkj : (k : ℕ) ≠ j := fun heq => hfresh γ hγ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkj x h).symm
    rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
  exact @hyp M (wc base (Function.update h j x)) neM hΓ

/-- **Negative acceptance without freshness.**  If `Δ` already refutes `σ(c)`, it refutes
`∀x σ(x)` outright: the universal is instantiated at `c`'s *own* interpretation, so nothing has to
be fresh for `Δ` and no witness is consumed.

This is the shape a labelled pair needs when the separator is abstracted on the side that does not
own `c`; `entails_not_genAll_of_entails_not` is the different, witness-passing sequent. -/
theorem entails_not_genAll_of_entails_not_self
    (hyp : Theoryω.Entails Δ σc.not) :
    Theoryω.Entails Δ (genAll j σc).not := by
  intro M instM neM hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  change @Sentenceω.Realize L[[ℕ]] (genAll j σc).not M instM
  -- Apply the negation lemma before crossing to bounded-formula realization.
  refine (BoundedFormulaω.realize_not _).mpr ?_
  intro hcon
  have hcon' : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genAll j σc)
      Empty.elim Fin.elim0 := (bridge _).mp hcon
  -- instantiate the generalization at `c`'s own value: `Function.update h j (h j) = h`
  have hinst := (realize_genAll base h j σc).mp hcon' (h j)
  rw [Function.update_eq_self] at hinst
  have hΔ : ∀ δ ∈ Δ,
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 δ Empty.elim Fin.elim0 :=
    fun δ hδ => (bridge _).mp (hmodel _ hδ)
  exact (@hyp M (wc base h) neM hΔ) hinst

end FirstOrder.Language
