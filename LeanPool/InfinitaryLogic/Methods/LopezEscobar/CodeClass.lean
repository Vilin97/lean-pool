/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.StandardModel
import LeanPool.InfinitaryLogic.Descriptive.CodeTransport
import LeanPool.InfinitaryLogic.Descriptive.LopezEscobarEasy
/-!
# Reconstruction and the code-class equality (issue #10, Unit 3b)

The converse of Unit 3a: reconstruct the functional `KLang`-structure from a model of the PC
sentence, read a branch off it, and land the base reduct back in `B` — **the only place**
`IsomorphismInvariant` is consumed.  The endpoints:

* `pcClass_subset` (needs invariance) — `codeReduct '' ModelsOf (pcSentence side T) ⊆ B`;
* `subset_pcClass` (Unit 3a, no invariance) — `B ⊆ codeReduct '' ModelsOf (pcSentence side T)`;
* `pcClass_eq` (needs invariance) — the code-class equality
  `codeReduct '' ModelsOf (pcSentence side T) = B`.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

instance instCountableFunctionsOfRelational : Countable (Σ n, L.Functions n) := by
  have : IsEmpty (Σ n, L.Functions n) := ⟨fun p => (‹L.IsRelational› p.1).false p.2⟩
  infer_instance

/-- **Converse gate, through an invariant envelope**: the base reducts of the PC class lie in any
isomorphism-invariant `W ⊇ B`.  This is the sole consumer of `IsomorphismInvariant`.

`B` itself need **not** be invariant, which is what makes this usable for an arbitrary analytic
family: a sentence-defined reduct class is always invariant, so `codeReduct '' ModelsOf Θ = B` is
unachievable for non-invariant `B`, but the sandwich

```
B ⊆ codeReduct '' ModelsOf Θ ⊆ W
```

is available for every invariant `W ⊇ B` and is what boundedness arguments actually consume.
`pcClass_subset` is the specialization `W := B`. -/
private theorem pcClass_subset_of_invariant_superset {B W : Set (StructureSpace L)} (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hT : ∀ c : StructureSpace L, c ∈ B ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T n)
    (hBW : B ⊆ W) (hWinv : IsomorphismInvariant W) :
    codeReduct '' ModelsOf (pcSentence L side T) ⊆ W := by
  rintro _ ⟨d, hd, rfl⟩
  -- the decoded graph-language model and its two conjuncts
  let Nstar : (graphLanguage (KLang L)).Structure ℕ := d.toStructure
  obtain ⟨hAx, hrel⟩ := (realize_pcSentence_iff side T).mp hd
  -- reconstruct the functional structures
  let Kstar : (KLang L).Structure ℕ := reconstructStructure (sideFunsSet L side) hAx
  let Mstar : (MidLang L).Structure ℕ := (sideEmb L side).reduct ℕ
  have hM : @Sentenceω.Realize (MidLang L) (functionalTheta L T) ℕ Mstar := by
    have h1 := reconstruct_realizes_functionalPCSentence side T hAx hrel
    rw [functionalPCSentence] at h1
    exact (BoundedFormulaω.realize_mapLanguage (sideEmb L side) (functionalTheta L T)
      (Empty.elim : Empty → ℕ) Fin.elim0).mp h1
  obtain ⟨homega, hbitR, hcode, hdef, htreeR, hpathR⟩ := (realize_functionalTheta T).mp hM
  have hbit := (realize_bitAxiom (L := L)).mp hbitR
  have htree := (realize_treeDiagram (L := L) T).mp htreeR
  have hpath := (realize_pathAxiom (L := L)).mp hpathR
  -- the numeral bijection and the read-off branch
  have hν := numMap_bijective homega
  set νEquiv := Equiv.ofBijective (numMap L ℕ) hν with hνEdef
  set ĝ : ℕ → ℕ := fun n => νEquiv.symm (gMap L ℕ (numMap L ℕ n)) with hĝdef
  have hνcoe : ∀ x, νEquiv x = numMap L ℕ x := fun x => Equiv.ofBijective_apply _ _ _
  have hg : ∀ k, numMap L ℕ (ĝ k) = gMap L ℕ (numMap L ℕ k) := fun k => by
    rw [hĝdef, ← hνcoe]; exact νEquiv.apply_symm_apply _
  -- the KEY base-relation identity
  have KEY : ∀ {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ),
      @Structure.RelMap L ℕ (codeReduct d).toStructure l R v ↔
        @Structure.RelMap (MidLang L) ℕ Mstar l (Sum.inl R) v := by
    intro l R v
    have hOnRel : (sideEmb L side).onRelation (Sum.inl R)
        = (Sum.inl R : (KLang L).Relations l) := by cases side <;> rfl
    rw [codeReduct_toStructure]
    change @Structure.RelMap (graphLanguage (KLang L)) ℕ Nstar l (GraphRelation.base (Sum.inl R)) v
      ↔ @Structure.RelMap (KLang L) ℕ Kstar l ((sideEmb L side).onRelation (Sum.inl R)) v
    rw [hOnRel]
    exact (reconstruct_relMap_base hAx (Sum.inl R) v).symm
  -- every prefix of (queryCode (pulledCode), ĝ) is in T
  have hbr : ∀ m, ((fun i : Fin m => queryCode (pulledCode L ℕ) (i : ℕ)),
      (fun i : Fin m => ĝ (i : ℕ))) ∈ T m := by
    intro m
    have hpt : @pathTuple L ℕ Mstar m
        = @treeTuple L ℕ Mstar m (fun i : Fin m => queryCode (pulledCode L ℕ) (i : ℕ))
          (fun i : Fin m => ĝ (i : ℕ)) := by
      funext i
      by_cases hi : (i : ℕ) < m
      · change (if (i : ℕ) < m then @fMap L ℕ Mstar (@numMap L ℕ Mstar (i : ℕ)) else _)
            = (if h : (i : ℕ) < m
              then @numMap L ℕ Mstar (cond ((fun j : Fin m =>
                queryCode (pulledCode L ℕ) (j : ℕ)) ⟨(i : ℕ), h⟩) 1 0) else _)
        rw [ite_eq_left hi, dite_eq_left hi]
        change @fMap L ℕ Mstar (@numMap L ℕ Mstar (i : ℕ))
          = @numMap L ℕ Mstar (cond (queryCode (pulledCode L ℕ) (i : ℕ)) 1 0)
        by_cases hq : queryCode (pulledCode L ℕ) (i : ℕ) = true
        · rw [hq]
          exact (fBit_eq_queryCode homega hcode hdef (i : ℕ)).mpr hq
        · simp only [Bool.not_eq_true] at hq
          rw [hq]
          rcases hbit (@numMap L ℕ Mstar (i : ℕ)) with h0 | h1
          · exact h0
          · exact absurd ((fBit_eq_queryCode homega hcode hdef (i : ℕ)).mp h1)
              (by rw [hq]; simp)
      · change (if (i : ℕ) < m then _
              else @gMap L ℕ Mstar (@numMap L ℕ Mstar ((i : ℕ) - m)))
            = (if h : (i : ℕ) < m then _
              else @numMap L ℕ Mstar ((fun j : Fin m => ĝ (j : ℕ)) ⟨(i : ℕ) - m, by omega⟩))
        rw [ite_eq_right hi, dite_eq_right hi]
        change
          @gMap L ℕ Mstar (@numMap L ℕ Mstar ((i : ℕ) - m)) =
            @numMap L ℕ Mstar (ĝ ((i : ℕ) - m))
        rw [hg]
    have hp := hpath m
    rw [hpt] at hp
    exact (htree m _ _).mp hp
  have hpB : pulledCode L ℕ ∈ B := (hT (pulledCode L ℕ)).mpr ⟨ĝ, hbr⟩
  -- transport back along ν to the reduct code, then invoke invariance
  let : L.Structure ℕ := (codeReduct d).toStructure
  have hcodeeq : StructureSpaceOn.encodeViaEquiv (L := L) (M := ℕ) (α := ℕ) νEquiv.symm
      = pulledCode L ℕ := by
    funext q
    obtain ⟨⟨l, R⟩, v⟩ := q
    -- The `MidLang L`-structure must be pinned to `Mstar`: left to instance synthesis it picks up
    -- the `letI` above and the pattern no longer matches the goal's `pulledCode L ℕ`.
    rw [Bool.eq_iff_iff, pulledCode_eq_true (inst := Mstar) ℕ ⟨⟨l, R⟩, v⟩,
      ← StructureSpaceOn.relMap_toStructure
        (StructureSpaceOn.encodeViaEquiv (L := L) νEquiv.symm) R v,
      StructureSpaceOn.toStructure_encodeViaEquiv_eq, Equiv.inducedStructure_RelMap, KEY]
    rw [show (⇑νEquiv.symm.symm ∘ v) = (fun i => @numMap L ℕ Mstar (v i)) from
      funext fun x => (DFunLike.congr_fun (_root_.Equiv.symm_symm νEquiv) (v x)).trans
        (hνcoe (v x))]
  have hiso := StructureSpaceOn.encodeViaEquiv_iso (L := L) (M := ℕ) νEquiv.symm
  rw [hcodeeq] at hiso
  -- the ONLY step that differs from the `W := B` case: land in `B`, cross to `W`, then transport
  exact (hWinv (codeReduct d) (pulledCode L ℕ) hiso).mpr (hBW hpB)

/-- **Converse gate** (`pcClass_subset`): the base reducts of the PC class lie in `B`, when `B`
itself is invariant.  The `W := B` specialization of
`pcClass_subset_of_invariant_superset`. -/
private theorem pcClass_subset {B : Set (StructureSpace L)} (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hT : ∀ c : StructureSpace L, c ∈ B ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T n)
    (hinv : IsomorphismInvariant B) :
    codeReduct '' ModelsOf (pcSentence L side T) ⊆ B :=
  pcClass_subset_of_invariant_superset side T hT subset_rfl hinv

/-- **The code-class equality** (needs invariance): the base reducts of the PC class are
exactly `B`. -/
theorem pcClass_eq {B : Set (StructureSpace L)} (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hT : ∀ c : StructureSpace L, c ∈ B ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T n)
    (hinv : IsomorphismInvariant B) :
    codeReduct '' ModelsOf (pcSentence L side T) = B :=
  Set.Subset.antisymm (pcClass_subset side T hT hinv) (subset_pcClass side T hT)

end FirstOrder.Language
