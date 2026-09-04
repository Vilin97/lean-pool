/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.Inseparability
import LeanPool.InfinitaryLogic.Methods.Henkin.Construction
import LeanPool.InfinitaryLogic.Methods.ConstantInstances
/-!
# The quantifier round-trip and the arbitrary-syntax C7 consumers (issue #8 tranche 1.5)

The Henkin truth lemma will meet an arbitrary existential `ψ.ex` (or negated universal
`(ψ.all).not`) and construct its constant instance, not a sentence literally of the form
`genEx c φ`. This file bridges the gap:

* `instConst c ψ := (ψ.openBounds).subst (fun _ => constTerm c)` — the constant instance `ψ(c)`;
* `realize_genEx_instConst` — the substitution round-trip: `genEx c (instConst c ψ)` is
  realization-equivalent to `ψ.ex` under freshness of `c` for `ψ`;
* `insepAt_instConst_of_insepAt_ex` / `insepAt_not_instConst_of_insepAt_not_all` — the actual
  C7 consumers for arbitrary existential / negated-universal parents.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {M : Type}

/-- The constant `c_c` realizes to its interpretation `h c`. -/
private theorem realize_constTerm (base : L.Structure M) (h : ℕ → M) (c : ℕ) (v : Empty → M) :
    @Term.realize L[[ℕ]] M (wc base h) Empty v (constTerm c) = h c := by
  show @Structure.funMap L[[ℕ]] M (wc base h) 0 (Sum.inr c) _ = h c
  rw [wc_funMap_inr]

/-- Realizing the constant instance `ψ(c)` is realizing `ψ` at the constant's interpretation. -/
theorem realize_instConst (base : L.Structure M) (h : ℕ → M) (c : ℕ)
    (ψ : L[[ℕ]].BoundedFormulaω Empty 1) :
    @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (instConst c ψ) Empty.elim Fin.elim0
      ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 1 ψ Empty.elim (fun _ => h c) := by
  let : L[[ℕ]].Structure M := wc base h
  rw [instConst, BoundedFormulaω.realize_subst]
  rw [show (fun a : Fin 1 => (constTerm c).realize (Empty.elim : Empty → M))
        = (fun _ : Fin 1 => h c) from funext fun _ => realize_constTerm base h c Empty.elim]
  exact realize_openBounds ψ (fun _ => h c)

/-- **The substitution round-trip**: for `c` fresh for `ψ`, `genEx c (instConst c ψ)` realizes
exactly as `ψ.ex`. -/
private theorem realize_genEx_instConst (base : L.Structure M) (h : ℕ → M) (c : ℕ)
    (ψ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hfresh : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ) :
    @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genEx c (instConst c ψ))
        Empty.elim Fin.elim0
      ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ.ex Empty.elim Fin.elim0 := by
  let : L[[ℕ]].Structure M := wc base h
  rw [realize_genEx base h c (instConst c ψ), BoundedFormulaω.realize_ex]
  refine exists_congr fun x => ?_
  have hsnoc : (Fin.snoc Fin.elim0 x : Fin 1 → M) = (fun _ => x) := by
    funext i; simp [Fin.snoc, Fin.eq_zero i]
  have hupd : (fun _ : Fin 1 => Function.update h c x c) = (fun _ : Fin 1 => x) :=
    funext fun _ => Function.update_self c x h
  rw [realize_instConst base (Function.update h c x) c ψ, hupd, hsnoc]
  -- reinterpretation off `c` does not change `ψ` (freshness)
  refine BoundedFormulaω.realize_congr_const base ψ (fun k hk => ?_) Empty.elim (fun _ => x)
  have hkc : k ≠ c := fun (heq : k = c) => hfresh (heq ▸ hk)
  exact Function.update_of_ne (α := ℕ) hkc x h

/-! ## Ambient semantic equivalence and premise congruence -/

/-- The round-trip as a semantic equivalence over arbitrary ambient structures. -/
theorem realize_genEx_instConst_iff_ex (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hfresh : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ)
    (M : Type) [S : L[[ℕ]].Structure M] :
    @Sentenceω.Realize L[[ℕ]] (genEx c (instConst c ψ)) M S
      ↔ @Sentenceω.Realize L[[ℕ]] ψ.ex M S := by
  show @BoundedFormulaω.Realize L[[ℕ]] M S Empty 0 (genEx c (instConst c ψ)) Empty.elim Fin.elim0
    ↔ @BoundedFormulaω.Realize L[[ℕ]] M S Empty 0 ψ.ex Empty.elim Fin.elim0
  rw [ambient_realize_iff_wc (S := S) (genEx c (instConst c ψ)) Empty.elim Fin.elim0,
    ambient_realize_iff_wc (S := S) ψ.ex Empty.elim Fin.elim0]
  exact realize_genEx_instConst _ _ c ψ hfresh

variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
  {A : Finset ℕ} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- Entailment is invariant under replacing an inserted premise by a semantically equivalent
sentence. -/
theorem entails_insert_congr {σ₁ σ₂ τ : L[[ℕ]].Sentenceω}
    (hequiv : ∀ (M : Type) [L[[ℕ]].Structure M] [Nonempty M],
      Sentenceω.Realize σ₁ M ↔ Sentenceω.Realize σ₂ M) :
    Theoryω.Entails (insert σ₁ Γ) τ ↔ Theoryω.Entails (insert σ₂ Γ) τ := by
  constructor <;> intro hE M _ _ hmodel <;> apply hE <;> intro ψ hψ <;>
    rcases Set.mem_insert_iff.mp hψ with rfl | hψ
  · exact (hequiv M).mpr (hmodel _ (Set.mem_insert _ _))
  · exact hmodel _ (Set.mem_insert_of_mem _ hψ)
  · exact (hequiv M).mp (hmodel _ (Set.mem_insert _ _))
  · exact hmodel _ (Set.mem_insert_of_mem _ hψ)

/-- `InsepAt` is invariant under replacing an inserted premise by a semantically equivalent
sentence. -/
private theorem insepAt_insert_congr {σ₁ σ₂ : L[[ℕ]].Sentenceω}
    (hequiv : ∀ (M : Type) [L[[ℕ]].Structure M] [Nonempty M],
      Sentenceω.Realize σ₁ M ↔ Sentenceω.Realize σ₂ M) :
    InsepAt F R A (insert σ₁ Γ) Δ ↔ InsepAt F R A (insert σ₂ Γ) Δ := by
  unfold InsepAt
  constructor <;> intro h ⟨σ, hbf, hbr, hsupp, hΓσ, hΔσ⟩ <;> apply h
  · exact ⟨σ, hbf, hbr, hsupp, (entails_insert_congr hequiv).mpr hΓσ, hΔσ⟩
  · exact ⟨σ, hbf, hbr, hsupp, (entails_insert_congr hequiv).mp hΓσ, hΔσ⟩

/-! ## The arbitrary-syntax C7 consumers -/

/-- **C7 consumer (existential)**: if the existential pair is inseparable at support `A`, then
the constant-instance pair is inseparable at support `insert c A`, for `c` fresh for `ψ`, `Γ`,
`Δ`. -/
private theorem insepAt_instConst_of_insepAt_ex (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hcψ : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : InsepAt F R A (insert ψ.ex Γ) Δ) :
    InsepAt F R (insert c A) (insert (instConst c ψ) Γ) Δ := by
  have h' : InsepAt F R A (insert (genEx c (instConst c ψ)) Γ) Δ :=
    (insepAt_insert_congr (fun M _ _ => realize_genEx_instConst_iff_ex c ψ hcψ M)).mpr h
  exact insepAt_witness_of_insepAt_genEx c (instConst c ψ) hcΓ hcΔ h'

/-- **C7 consumer (negated universal)**: `¬∀x ψ` is `∃x ¬ψ`; the witness is `¬ψ(c)`. -/
theorem insepAt_not_instConst_of_insepAt_not_all (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hcψ : c ∉ sentenceJConsts (L' := L) (J := ℕ) ψ.not)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : InsepAt F R A (insert (ψ.all).not Γ) Δ) :
    InsepAt F R (insert c A) (insert (instConst c ψ.not) Γ) Δ := by
  -- `(ψ.all).not` is semantically `(ψ.not).ex`, so reuse the existential consumer with `ψ.not`.
  have hequiv : ∀ (N : Type) [L[[ℕ]].Structure N] [Nonempty N],
      Sentenceω.Realize (ψ.all).not N ↔ Sentenceω.Realize (ψ.not).ex N := by
    intro N _ _
    simp only [Sentenceω.realize_def, BoundedFormulaω.realize_not, BoundedFormulaω.realize_all,
      BoundedFormulaω.realize_ex, not_forall]
  have h' : InsepAt F R A (insert (ψ.not).ex Γ) Δ :=
    (insepAt_insert_congr (fun N _ _ => hequiv N)).mp h
  exact insepAt_instConst_of_insepAt_ex c ψ.not hcψ hcΓ hcΔ h'

end FirstOrder.Language
