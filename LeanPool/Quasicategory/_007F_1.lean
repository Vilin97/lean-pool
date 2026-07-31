/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory.Monomorphism

/-!

The first half of the proof of `007F`.

-/

universe w u

namespace SSet

open CategoryTheory Simplicial MonoidalCategory PushoutProduct

variable {n : ℕ} (i : Fin (n + 1))

-- [n] ⟶ [2] by j ↦
-- 0 if j < i
-- 1 if j = i
-- 2 if j > i
def s_aux : Fin (n + 1) →o Fin 3 where
  toFun j := if j < i then 0 else if j = i then 1 else 2
  monotone' j k h := by
    simp
    split
    · omega
    · split
      all_goals
      · split
        · omega
        · split
          all_goals omega

def standard_map : Δ[n] ⟶ Δ[2] :=
  stdSimplex.map (SimplexCategory.mkHom (s_aux i))

-- the above map restricted to the horn
def horn_map : Λ[n, i].toSSet ⟶ Δ[2] :=
  Λ[n, i].ι ≫ (standard_map i)

-- on vertices j maps to
-- (j, 0) if j < i
-- (j, 1) if j = i
-- (j, 2) if j > i
def s : Δ[n] ⟶ Δ[2] ⊗ Δ[n] :=
  FunctorToTypes.prod.lift (standard_map i) (𝟙 _)

def s_restricted :
    Λ[n, i].toSSet ⟶ Δ[2] ⊗ Λ[n, i] :=
  FunctorToTypes.prod.lift (horn_map i) (𝟙 _)

noncomputable
def horn_to_pushout :
    Λ[n, i].toSSet ⟶ (PushoutProduct.pt Λ[2, 1].ι Λ[n, i].ι) :=
  s_restricted i ≫ (Limits.pushout.inl _ _)

lemma leftSqCommAux : s_restricted i ≫ Δ[2] ◁ Λ[n, i].ι = Λ[n, i].ι ≫ s i := rfl

lemma leftSqComm :
    horn_to_pushout i ≫ Λ[2, 1].ι □ Λ[n, i].ι = Λ[n, i].ι ≫ s i := by
  rw [← leftSqCommAux]
  simp [horn_to_pushout, Functor.PushoutObjObj.ι]

def r_aux : Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun := fun ⟨k, j⟩ ↦ if (j < i ∧ k = 0) ∨ (j > i ∧ k = 2) then j else i
  monotone' := by
    intro ⟨k, j⟩ ⟨k', j'⟩ ⟨(hk : k ≤ k'), (hj : j ≤ j')⟩
    dsimp
    split
    all_goals
    · split
      all_goals omega

open stdSimplex SimplexCategory in
def map_mk_from_prod {n m k : ℕ} (f : Fin (n + 1) × Fin (m + 1) →o Fin (k + 1)) : Δ[n] ⊗ Δ[m] ⟶ Δ[k] := by
  refine ⟨fun x ⟨c, d⟩ ↦ ⟨SimplexCategory.mkHom ⟨fun a ↦ f ((stdSimplex.asOrderHom c) a, (stdSimplex.asOrderHom d) a), ?_⟩⟩, ?_⟩
  · intro j k hjk
    exact f.monotone ⟨(stdSimplex.asOrderHom c).monotone hjk, (stdSimplex.asOrderHom d).monotone hjk⟩
  · aesop

-- on vertices j k map to
-- j if (j < i) ∧ (k = 0)
-- j if (j > i) ∧ (k = 2)
-- i if (j = i) ∨ (k = 1)
def r : Δ[2] ⊗ Δ[n] ⟶ Δ[n] := map_mk_from_prod (r_aux i)

variable (h0 : 0 < i) (hn : i < Fin.last n)

-- r restricted along Λ[2, 1]
noncomputable
def r_restrict_horn_2 : (Λ[2, 1] : SSet) ⊗ Δ[n] ⟶ Λ[n, i] where
  app k := by
    intro ⟨⟨x, hx⟩, y⟩
    refine ⟨(((horn 2 1).ι) ▷ Δ[n] ≫ r i).app k ⟨⟨x, hx⟩, y⟩, ?_⟩
    rw [mem_horn_iff, Set.ne_univ_iff_exists_not_mem] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    fin_cases a
    · simp at ha ⊢
      use 0
      refine ⟨Fin.ne_of_lt h0, fun j h ↦ ?_⟩
      change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at h
      split at h
      all_goals aesop
    · aesop
    · simp at ha ⊢
      use Fin.last n
      refine ⟨Fin.ne_of_gt hn, fun j h ↦ ?_⟩
      change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at h
      split at h
      · next h' =>
        simp_all
        omega
      · omega

-- r restricted along Λ[n, i].toSSet
noncomputable
def r_restrict_horn_n : Δ[2] ⊗ Λ[n, i] ⟶ Λ[n, i] where
  app k := by
    intro ⟨x, ⟨y, hy⟩⟩
    refine ⟨(Δ[2] ◁ Λ[n, i].ι ≫ r i).app k ⟨x, ⟨y, hy⟩⟩, ?_⟩
    rw [mem_horn_iff, Set.ne_univ_iff_exists_not_mem] at hy ⊢
    obtain ⟨a, ha⟩ := hy
    use a
    intro h
    simp at h ha
    obtain ⟨ha₁, ha₂⟩ := ha
    cases h
    · omega
    · next h =>
      obtain ⟨j, hj⟩ := h
      apply ha₂ j
      change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at hj
      aesop

open stdSimplex SimplexCategory in
noncomputable
def pushout_to_horn : (PushoutProduct.pt Λ[2, 1].ι Λ[n, i].ι) ⟶ Λ[n, i] :=
  Limits.pushout.desc (r_restrict_horn_n i) (r_restrict_horn_2 i h0 hn) rfl

lemma rightSqComm : pushout_to_horn i h0 hn ≫ (Λ[n, i]).ι = (Λ[2, 1].ι □ Λ[n, i].ι) ≫ r i := by
  dsimp [pushout_to_horn]
  apply Limits.pushout.hom_ext; all_goals dsimp [Functor.PushoutObjObj.ι]; aesop

lemma r_aux_comp_s_aux_prod_id :
    OrderHom.comp (r_aux i) ((s_aux i).prod (OrderHom.id)) = OrderHom.id := by
  ext
  simp [s_aux, r_aux]
  split
  · aesop
  · split
    · aesop
    · split
      · aesop
      · exfalso
        omega

lemma r_comp_s : s i ≫ r i = 𝟙 Δ[n] := by
  change stdSimplex.map (SimplexCategory.mkHom (OrderHom.comp (r_aux i) ((s_aux i).prod (OrderHom.id)))) = _
  rw [r_aux_comp_s_aux_prod_id]
  simp

lemma restricted_r_comp_s : horn_to_pushout i ≫ pushout_to_horn i h0 hn = 𝟙 Λ[n, i].toSSet := by
  dsimp [horn_to_pushout, pushout_to_horn]
  rw [Category.assoc, Limits.pushout.inl_desc]
  ext k ⟨x, hx⟩
  change (r_restrict_horn_n i).app k ((horn_map i).app k ⟨x, hx⟩, ⟨x, hx⟩) = ⟨x, hx⟩
  simp [r_restrict_horn_n]
  have := congr_fun (congr_app (r_comp_s i) k) x
  aesop

noncomputable
instance hornRetract : RetractArrow Λ[n, i].ι (Λ[2, 1].ι □ Λ[n, i].ι) where
  i := {
    left := horn_to_pushout i
    right := s i
    w := leftSqComm i
  }
  r := {
    left := pushout_to_horn i h0 hn
    right := r i
    w := rightSqComm i h0 hn
  }
  retract := Arrow.hom_ext _ _ (restricted_r_comp_s i h0 hn) (r_comp_s i)
