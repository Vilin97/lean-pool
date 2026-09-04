/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.ConstantAbstraction
import LeanPool.InfinitaryLogic.Lomega1omega.Entailment
/-!
# Constant elimination: the C7 acceptance lemmas (issue #8 kernel step 5)

The fresh-constant elimination sequents of the Craig arc (`docs/craig-audit.md` §6a, correction
3). `genEx j ρ` existentially generalizes the constant `c_j` out of a sentence `ρ`; the two
acceptance lemmas transport an entailment from a `c_j`-mentioning form to its generalization,
under freshness of `c_j` for the fixed side:

* `entails_genEx_of_entails` (side 1): `Γ, φ(c) ⊨ σ(c) ⟹ Γ, ∃x φ(x) ⊨ ∃x σ(x)`, `c` fresh for `Γ`;
* `entails_not_genEx_of_entails_not` (side 2): `Δ ⊨ ¬σ(c) ⟹ Δ ⊨ ¬∃x σ(x)`, `c` fresh for `Δ`.

Both are proved by the reinterpretation engine (`realize_abstractConst`) plus the
invariance-outside-support congruence (`realize_congr_const`), bridged to arbitrary ambient
`L[[ℕ]]`-structures by `ambient_realize_iff_wc`. Together they show that abstraction transports a
separator from constant support `insert c A` back to `A` (the InsepAt C7 step).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {M : Type}

/-- Existentially generalize the constant `c_j` out of a sentence: abstract `c_j` into the free
variable `0`, then existentially quantify it. -/
noncomputable def genEx (j : ℕ) (ρ : L[[ℕ]].Sentenceω) : L[[ℕ]].Sentenceω :=
  ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex

/-- Realizing the generalization is existentially witnessing the original with `c_j`
reinterpreted to the witness. -/
theorem realize_genEx (base : L.Structure M) (h : ℕ → M) (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genEx j ρ) Empty.elim Fin.elim0
      ↔ ∃ x, @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 ρ
          Empty.elim Fin.elim0 := by
  let : L[[ℕ]].Structure M := wc base h
  have hval : ∀ x : M, (Fin.snoc Fin.elim0 x : Fin 1 → M) = (fun _ => x) := by
    intro x; funext i; simp [Fin.snoc, Fin.eq_zero i]
  rw [genEx, BoundedFormulaω.realize_ex]
  refine exists_congr fun x => ?_
  rw [BoundedFormulaω.realize_relabel_sumInr_zero (ρ.abstractConst j) (Fin.snoc Fin.elim0 x),
    hval x]
  exact BoundedFormulaω.realize_abstractConst base h j x ρ Fin.elim0

/-- `c_j` is not in the constant support of its own generalization. -/
theorem notMem_sentenceJConsts_genEx (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    j ∉ sentenceJConsts (L' := L) (J := ℕ) (genEx j ρ) := by
  rw [genEx]
  intro hmem
  rw [sentenceJConsts_ex] at hmem
  have h2 : sentenceJConsts (L' := L) (J := ℕ)
      ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1))
      = sentenceJConsts (L' := L) (J := ℕ) (ρ.abstractConst j) := by
    unfold sentenceJConsts
    rw [BoundedFormulaω.functionsIn_relabel]
  rw [h2] at hmem
  exact BoundedFormulaω.notMem_sentenceJConsts_abstractConst j ρ hmem

/-! ## Occurrence facts for `genEx` -/

/-- `genEx` preserves the relation symbols. -/
private theorem relationsIn_genEx (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genEx j ρ).relationsIn = ρ.relationsIn := by
  rw [genEx, BoundedFormulaω.relationsIn_ex, BoundedFormulaω.relationsIn_relabel,
    BoundedFormulaω.relationsIn_abstractConst]

/-- `genEx` adds no function symbols. -/
private theorem functionsIn_genEx_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genEx j ρ).functionsIn ⊆ ρ.functionsIn := by
  rw [genEx, BoundedFormulaω.functionsIn_ex, BoundedFormulaω.functionsIn_relabel]
  exact BoundedFormulaω.functionsIn_abstractConst_subset j ρ

/-- `genEx` adds no base function symbols. -/
theorem baseFunctionsIn_genEx_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genEx j ρ).baseFunctionsIn ⊆ ρ.baseFunctionsIn :=
  fun _ hs => functionsIn_genEx_subset j ρ hs

/-- `genEx` preserves the base relation symbols. -/
theorem baseRelationsIn_genEx (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genEx j ρ).baseRelationsIn = ρ.baseRelationsIn := by
  unfold BoundedFormulaω.baseRelationsIn
  rw [relationsIn_genEx]

/-- `genEx` adds no constants. -/
theorem sentenceJConsts_genEx_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    sentenceJConsts (L' := L) (J := ℕ) (genEx j ρ) ⊆ sentenceJConsts (L' := L) (J := ℕ) ρ :=
  fun _ hs => functionsIn_genEx_subset j ρ hs

/-! ## The acceptance lemmas -/

variable {j : ℕ} {φc σc : L[[ℕ]].Sentenceω} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- Plain `Γ`-side abstraction (**freshness-free**: `∃`-introduction is weakening). `Γ ⊨ σ`
upgrades to `Γ ⊨ ∃x σ(x)`; the witness is the constant's own interpretation. -/
theorem entails_genEx_of_entails_plain (j : ℕ) (σc : L[[ℕ]].Sentenceω)
    (hyp : Theoryω.Entails Γ σc) : Theoryω.Entails Γ (genEx j σc) := by
  intro M instM _ hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  have hσ : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 σc Empty.elim Fin.elim0 :=
    (bridge _).mp (hyp M hmodel)
  refine (bridge _).mpr ((realize_genEx base h j σc).mpr ⟨h j, ?_⟩)
  rw [Function.update_eq_self]; exact hσ

/-- **Acceptance, side 1**: `Γ, φ(c) ⊨ σ(c)` upgrades to `Γ, ∃x φ(x) ⊨ ∃x σ(x)` when `c_j` is
fresh for `Γ`. -/
theorem entails_genEx_of_entails
    (hfresh : ∀ γ ∈ Γ, j ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hyp : Theoryω.Entails (insert φc Γ) σc) :
    Theoryω.Entails (insert (genEx j φc) Γ) (genEx j σc) := by
  intro M instM neM hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  -- Bridge each sentence's ambient realization to the controlled `wc base h`.
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  -- Witness from `∃x φ(x)`.
  have hφ :
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genEx j φc)
        Empty.elim Fin.elim0 :=
    (bridge _).mp (hmodel _ (Set.mem_insert _ _))
  obtain ⟨x, hx⟩ := (realize_genEx base h j φc).mp hφ
  -- The `Γ`-part survives reinterpretation off `j`.
  have hΓ : ∀ γ ∈ Γ,
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 γ
        Empty.elim Fin.elim0 := by
    intro γ hγ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 γ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ (Set.mem_insert_of_mem _ hγ))
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ, h k = Function.update h j x k := by
      intro k hk
      have hkj : (k : ℕ) ≠ j := fun heq => hfresh γ hγ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkj x h).symm
    rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
  -- Apply the hypothesis in the reinterpreted structure.
  have hσ : @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 σc
      Empty.elim Fin.elim0 :=
    @hyp M (wc base (Function.update h j x)) neM (fun ψ hψ => by
      rcases Set.mem_insert_iff.mp hψ with rfl | hψ
      · exact hx
      · exact hΓ ψ hψ)
  -- Conclude `∃x σ(x)`.
  exact (bridge _).mpr ((realize_genEx base h j σc).mpr ⟨x, hσ⟩)

/-- **Acceptance, side 2**: `Δ ⊨ ¬σ(c)` upgrades to `Δ ⊨ ¬∃x σ(x)` when `c_j` is fresh for
`Δ`. -/
theorem entails_not_genEx_of_entails_not
    (hfresh : ∀ δ ∈ Δ, j ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (hyp : Theoryω.Entails Δ σc.not) :
    Theoryω.Entails Δ (genEx j σc).not := by
  intro M instM neM hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  -- Goal: `¬ ∃x σ(x)`.
  change @Sentenceω.Realize L[[ℕ]] (genEx j σc).not M instM
  -- apply the negation lemma rather than unfolding `Sentenceω.Realize` first: unfolding leaves the
  -- goal in `SentenceInf.Realize`, which `rw` cannot key the alias-stated lemma against
  refine (BoundedFormulaω.realize_not (genEx j σc)).mpr ?_
  intro hcon
  have hcon' : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genEx j σc)
      Empty.elim Fin.elim0 := (bridge _).mp hcon
  obtain ⟨x, hx⟩ := (realize_genEx base h j σc).mp hcon'
  -- `Δ` survives reinterpretation off `j`.
  have hΔ : ∀ δ ∈ Δ,
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 δ
        Empty.elim Fin.elim0 := by
    intro δ hδ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 δ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ hδ)
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) δ, h k = Function.update h j x k := by
      intro k hk
      have hkj : (k : ℕ) ≠ j := fun heq => hfresh δ hδ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkj x h).symm
    rwa [BoundedFormulaω.realize_congr_const base δ hcongr Empty.elim Fin.elim0] at hg
  -- The hypothesis says `¬σ(c)` in the reinterpreted structure.
  have hnot : @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 σc.not
      Empty.elim Fin.elim0 := @hyp M (wc base (Function.update h j x)) neM hΔ
  exact hnot hx

end FirstOrder.Language
