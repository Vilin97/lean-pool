/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
import LeanPool.InfinitaryLogic.Lomega1omega.Entailment
/-!
# Semantic expansion of a two-sorted generated sublanguage (neutral prerequisite)

`GeneratedSublanguage.lean` is purely syntactic; this neutral companion adds the **semantic**
side of the two-sorted symbol-generated sublanguage `symbSublang F R`: the base-language
expansion of a sublanguage structure and its realization/entailment transport.  Kept separate
from `GeneratedSublanguage.lean` (which has no `Structure`/`Realize` dependency) and independent
of any `Conditional` file.

* `expandSymbStructureBase` — from a `(symbSublang F R).Structure M` build an `L.Structure M`
  (symbols outside the generating sets interpreted arbitrarily / as `False`); the base analogue
  of the constants-expanded `expandSymbStructure`.
* `reduct_expandSymbStructureBase` — the reduct along `symbSublangIncl F R` recovers the original
  sublanguage structure.
* `realize_restrictSymbols_expandSymbStructureBase` — realizing `φ.restrictSymbols` in the
  sublanguage structure is realizing `φ` in the expansion (the high-leverage transport lemma).
* `entails_restrictSymbols_singleton` — a base-`L` entailment restricts to the sublanguage,
  via the expansion of an arbitrary sublanguage model.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- A symbol-generated sublanguage of a relational language is relational. -/
instance symbSublang_isRelational [h : L.IsRelational] (F : Set (Σ n, L.Functions n))
    (R : Set (Σ n, L.Relations n)) : (symbSublang (L := L) F R).IsRelational :=
  fun n => ⟨fun f => (h n).false f.1⟩

/-- **Base expansion of a two-sorted sublanguage structure.** Function/relation symbols in the
generating sets are interpreted by the sublanguage structure; the rest are filled in arbitrarily
(functions) / as `False` (relations). -/
@[reducible] noncomputable def expandSymbStructureBase
    (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) {M : Type} [Nonempty M]
    [instM : (symbSublang (L := L) F R).Structure M] : L.Structure M := by
  classical
  exact
    { funMap := fun {m} f xs =>
        if h : (⟨m, f⟩ : Σ n, L.Functions n) ∈ F then
          Structure.funMap (L := symbSublang (L := L) F R)
            (⟨f, h⟩ : (symbSublang (L := L) F R).Functions m) xs
        else Classical.arbitrary M
      RelMap := fun {m} r xs =>
        if h : (⟨m, r⟩ : Σ n, L.Relations n) ∈ R then
          Structure.RelMap (L := symbSublang (L := L) F R)
            (⟨r, h⟩ : (symbSublang (L := L) F R).Relations m) xs
        else False }

/-- The reduct along `symbSublangIncl` recovers the original sublanguage structure. -/
theorem reduct_expandSymbStructureBase
    (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) {M : Type} [Nonempty M]
    [instM : (symbSublang (L := L) F R).Structure M] :
    @LHom.reduct (symbSublang (L := L) F R) L (symbSublangIncl F R) M (expandSymbStructureBase F R)
      = instM := by
  classical
  apply Structure.ext
  · funext m f xs
    change (expandSymbStructureBase F R).funMap ((symbSublangIncl F R).onFunction f) xs = _
    change (if h : (⟨m, f.1⟩ : Σ n, L.Functions n) ∈ F then
        Structure.funMap (L := symbSublang (L := L) F R) (⟨f.1, h⟩ : _) xs
      else Classical.arbitrary M) = Structure.funMap f xs
    exact dite_eq_left f.2
  · funext m r xs
    change (expandSymbStructureBase F R).RelMap ((symbSublangIncl F R).onRelation r) xs = _
    change (if h : (⟨m, r.1⟩ : Σ n, L.Relations n) ∈ R then
        Structure.RelMap (L := symbSublang (L := L) F R) (⟨r.1, h⟩ : _) xs
      else False) = Structure.RelMap r xs
    exact dite_eq_left r.2

/-- **Realization transport**: realizing `φ.restrictSymbols` in the sublanguage structure is
realizing `φ` in the base expansion. -/
theorem realize_restrictSymbols_expandSymbStructureBase
    (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) {M : Type} [Nonempty M]
    [instM : (symbSublang (L := L) F R).Structure M]
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    (v : Empty → M) (xs : Fin n → M) :
    @BoundedFormulaω.Realize (symbSublang (L := L) F R) M instM Empty n
        (φ.restrictSymbols hF hR) v xs
      ↔ @BoundedFormulaω.Realize L M (expandSymbStructureBase F R) Empty n φ v xs := by
  classical
  let : L.Structure M := expandSymbStructureBase F R
  have : (symbSublangIncl F R).IsExpansionOn M := by
    constructor
    · intro m f xs
      change (if h : (⟨m, f.1⟩ : Σ n, L.Functions n) ∈ F then
          Structure.funMap (L := symbSublang (L := L) F R) (⟨f.1, h⟩ : _) xs
        else Classical.arbitrary M) = _
      exact dite_eq_left f.2
    · intro m r xs
      change (if h : (⟨m, r.1⟩ : Σ n, L.Relations n) ∈ R then
          Structure.RelMap (L := symbSublang (L := L) F R) (⟨r.1, h⟩ : _) xs
        else False) = _
      exact dite_eq_left r.2
  have h := BoundedFormulaω.realize_mapLanguage (M := M) (symbSublangIncl F R)
    (φ.restrictSymbols hF hR) v xs
  rw [BoundedFormulaω.mapLanguage_restrictSymbols] at h
  exact h.symm

/-- **Entailment transport (singleton form)**: a base-`L` entailment restricts to the
sublanguage, via the base expansion of any sublanguage model. -/
theorem entails_restrictSymbols_singleton
    (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) (r₁ r₂ : L.Sentenceω)
    (hr₁F : r₁.functionsIn ⊆ F) (hr₁R : r₁.relationsIn ⊆ R)
    (hr₂F : r₂.functionsIn ⊆ F) (hr₂R : r₂.relationsIn ⊆ R)
    (hE : Sentenceω.Entails r₁ r₂) :
    Sentenceω.Entails (r₁.restrictSymbols hr₁F hr₁R) (r₂.restrictSymbols hr₂F hr₂R) := by
  intro N _ neN hmodel
  let : L.Structure N := expandSymbStructureBase F R
  have hr₁N : @Sentenceω.Realize L r₁ N _ :=
    (realize_restrictSymbols_expandSymbStructureBase F R r₁ hr₁F hr₁R Empty.elim Fin.elim0).mp
      (hmodel _ (Set.mem_singleton _))
  have hr₂N : @Sentenceω.Realize L r₂ N _ :=
    hE N (fun ψ hψ => by rw [Set.mem_singleton_iff] at hψ; subst hψ; exact hr₁N)
  exact (realize_restrictSymbols_expandSymbStructureBase F R r₂ hr₂F hr₂R
    Empty.elim Fin.elim0).mpr hr₂N

end FirstOrder.Language
