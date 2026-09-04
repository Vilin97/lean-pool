/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Fragment
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
/-!
# A-elementarity and the fragment Tarski–Vaught criterion (issue #13 unit 4)

Per the frozen audit (`docs/fragments-audit.md` §4–§5): `AElementary A f` is DIRECT TRUTH
AGREEMENT on the fragment's members, at all semantic tuples, along an embedding — stated as an
iff, since fragments are not assumed closed under formal negation. Basic API: identity,
composition, the two-out-of-three lemma (the form the chain-union development consumes), and
sentence/theory transport. The fragment-relative **Tarski–Vaught criterion**
(`aElementary_of_tarskiVaught`) upgrades witness closure for the fragment-controlled
universals to full A-elementarity — witnesses are ELEMENTS (semantic parameters), so no
syntactic substitution enters the induction.
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M N P : Type w}
  [L.Structure M] [L.Structure N] [L.Structure P]

/-- **A-elementarity**: truth agreement on every fragment member, at every tuple, along an
embedding. -/
def AElementary (A : Fragment L) (f : N ↪[L] M) : Prop :=
  ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet →
    ∀ a : Fin n → N, (φ.Realize Empty.elim (⇑f ∘ a) ↔ φ.Realize Empty.elim a)

namespace AElementary

theorem refl (A : Fragment L) : AElementary A (Embedding.refl L M) := by
  intro n φ _ a
  exact Iff.of_eq (congrArg _ (funext fun i => rfl))

theorem comp {A : Fragment L} {f : N ↪[L] M} {g : P ↪[L] N}
    (hf : AElementary A f) (hg : AElementary A g) : AElementary A (f.comp g) := by
  intro n φ hφ a
  have h1 := hf φ hφ (⇑g ∘ a)
  have h2 := hg φ hφ a
  exact (Iff.of_eq (congrArg (φ.Realize Empty.elim)
    (funext fun i => rfl))).trans (h1.trans h2)

/-- **Two-out-of-three**: if the composite and the outer embedding are A-elementary, so is the
inner one — the form the chain development consumes. -/
theorem of_comp {A : Fragment L} {f : N ↪[L] M} {g : P ↪[L] N}
    (hf : AElementary A f) (hfg : AElementary A (f.comp g)) : AElementary A g := by
  intro n φ hφ a
  have h1 := hf φ hφ (⇑g ∘ a)
  have h2 := hfg φ hφ a
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (h1.symm.trans ((Iff.of_eq (congrArg (φ.Realize Empty.elim)
      (funext fun i => rfl))).symm.trans h2)).mp h
  · exact (h1.symm.trans ((Iff.of_eq (congrArg (φ.Realize Empty.elim)
      (funext fun i => rfl))).symm.trans h2)).mpr h

/-- Sentence transport: for a fragment sentence, truth agrees between the two structures. -/
theorem realize_sentence_iff {A : Fragment L} {f : N ↪[L] M} (h : AElementary A f)
    {φ : L.Sentenceω} (hφ : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    Sentenceω.Realize φ M ↔ Sentenceω.Realize φ N := by
  have := h φ hφ Fin.elim0
  rwa [show (⇑f ∘ Fin.elim0 : Fin 0 → M) = Fin.elim0 from funext fun i => i.elim0] at this

/-- Theory transport: a fragment theory true in the ambient model is true in the A-elementary
substructure, and conversely. -/
theorem theoryModel_iff {A : Fragment L} {f : N ↪[L] M} (h : AElementary A f)
    {T : Set L.Sentenceω}
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    Theoryω.Model T M ↔ Theoryω.Model T N := by
  constructor
  · intro hM
    exact fun φ hφ => (h.realize_sentence_iff (hT φ hφ)).mp (hM φ hφ)
  · intro hN
    exact fun φ hφ => (h.realize_sentence_iff (hT φ hφ)).mpr (hN φ hφ)

end AElementary

/-- **The fragment Tarski–Vaught criterion**: if every fragment-controlled universal admits
element witnesses in `N` for its failures in `M`, then the embedding is A-elementary. -/
theorem aElementary_of_tarskiVaught {A : Fragment L} (f : N ↪[L] M)
    (hTV : ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty (n + 1)),
      (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet → ∀ a : Fin n → N,
      (∃ m : M, ¬φ.Realize Empty.elim (Fin.snoc (⇑f ∘ a) m)) →
      ∃ b : N, ¬φ.Realize Empty.elim (Fin.snoc (⇑f ∘ a) (f b))) :
    AElementary A f := by
  have h_elim : ∀ {m : ℕ} (xs : Fin m → N),
      Sum.elim (Empty.elim : Empty → M) (⇑f ∘ xs) = ⇑f ∘ Sum.elim Empty.elim xs := by
    intro m xs
    funext x
    cases x with
    | inl e => exact e.elim
    | inr i => rfl
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => Iff.rfl
  | equal t u =>
    intro _ a
    show t.realize (Sum.elim Empty.elim (⇑f ∘ a)) = u.realize (Sum.elim Empty.elim (⇑f ∘ a))
      ↔ t.realize (Sum.elim Empty.elim a) = u.realize (Sum.elim Empty.elim a)
    rw [h_elim a, HomClass.realize_term, HomClass.realize_term]
    exact f.injective.eq_iff
  | rel R ts =>
    intro _ a
    have hts : (fun i => (ts i).realize (Sum.elim (Empty.elim : Empty → M) (⇑f ∘ a)))
        = fun i => f ((ts i).realize (Sum.elim Empty.elim a)) := by
      funext i
      rw [h_elim a, HomClass.realize_term]
    show Structure.RelMap R (fun i => (ts i).realize (Sum.elim Empty.elim (⇑f ∘ a)))
      ↔ Structure.RelMap R (fun i => (ts i).realize (Sum.elim Empty.elim a))
    rw [hts]
    exact f.map_rel R _
  | imp φ ψ ihφ ihψ =>
    intro hmem a
    exact imp_congr (ihφ (A.imp_left_mem hmem) a) (ihψ (A.imp_right_mem hmem) a)
  | @all m φ ih =>
    intro hmem a
    have hbody := A.all_mem hmem
    have hsnoc : ∀ b : N, (Fin.snoc (⇑f ∘ a) (f b) : Fin (m + 1) → M) = ⇑f ∘ Fin.snoc a b :=
      fun b => (Fin.comp_snoc ⇑f a b).symm
    constructor
    · intro hM b
      have hMb := hM (f b)
      rw [hsnoc b] at hMb
      -- apply the induction hypothesis rather than rewriting with it: it is stated through the
      -- reducible `BoundedFormulaω.Realize` alias, which `rw` cannot key against a goal in
      -- `BoundedFormulaInf.Realize`
      exact (ih hbody (Fin.snoc a b)).mp hMb
    · intro hN m'
      by_contra hm
      obtain ⟨b, hb⟩ := hTV φ hmem a ⟨m', hm⟩
      refine hb ?_
      rw [hsnoc b]
      exact (ih hbody (Fin.snoc a b)).mpr (hN b)
  | iSup φs ih =>
    intro hmem a
    exact exists_congr fun k => ih k (A.iSup_mem hmem k) a
  | iInf φs ih =>
    intro hmem a
    exact forall_congr' fun k => ih k (A.iInf_mem hmem k) a

end Language

end FirstOrder
