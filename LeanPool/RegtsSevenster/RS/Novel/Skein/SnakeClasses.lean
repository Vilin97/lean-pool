/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.RigidityClasses
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTensor

/-!
# The snake identities on Hom classes

The two snake composites of the skein category are the identity
class.  Both composites are concrete fragments built from strands
by tensor and composition, and the entire gluing stack reduces
definitionally on concrete data, so the fragment equivalences are
established by `decide` over the two surviving flags, with the
inverse flag map given canonically by the boundary-flag function.
-/

@[expose] public section

namespace RS

/-- The left snake fragment `(coev ⊗ id) ∘ (id ⊗ ev)`. -/
noncomputable def snakeFragL : Fragment (Fin (1 + 1)) :=
  (tensorFragment coevFrag (strandBundle 1)).compose
    (tensorFragment (strandBundle 1) evFrag)

/-- The right snake fragment `(id ⊗ coev) ∘ (ev ⊗ id)`. -/
noncomputable def snakeFragR : Fragment (Fin (1 + 1)) :=
  (tensorFragment (strandBundle 1) coevFrag).compose
    (tensorFragment evFrag (strandBundle 1))

private instance : IsEmpty (strandBundle 1).Vertex :=
  inferInstanceAs (IsEmpty Empty)

private instance : Fintype (strandBundle 1).Flag :=
  inferInstanceAs (Fintype (Fin 1 × Bool))

private instance : DecidableEq (strandBundle 1).Flag :=
  inferInstanceAs (DecidableEq (Fin 1 × Bool))

private instance : IsEmpty snakeFragL.Vertex :=
  inferInstanceAs (IsEmpty ((Empty ⊕ Empty) ⊕ (Empty ⊕ Empty)))

private instance : IsEmpty snakeFragR.Vertex :=
  inferInstanceAs (IsEmpty ((Empty ⊕ Empty) ⊕ (Empty ⊕ Empty)))

private instance : DecidableEq snakeFragL.Vertex :=
  fun a _ => isEmptyElim a

private instance : DecidableEq snakeFragR.Vertex :=
  fun a _ => isEmptyElim a

private noncomputable instance : DecidableEq snakeFragL.Flag :=
  snakeFragL.flagDecEq

private noncomputable instance : DecidableEq snakeFragR.Flag :=
  snakeFragR.flagDecEq

private noncomputable instance : Fintype snakeFragL.Flag :=
  snakeFragL.flagFintype

private noncomputable instance : Fintype snakeFragR.Flag :=
  snakeFragR.flagFintype

/-- The left snake fragment is the identity strand. -/
noncomputable def snakeFragLEquiv :
    (strandBundle 1).Equiv snakeFragL where
  flagEquiv := _root_.Equiv.ofBijective
    (fun g : Fin 1 × Bool =>
      snakeFragL.boundaryFlag (if g.2 then 1 else 0))
    (by exact (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨by
        intro a b h
        obtain ⟨i, ba⟩ := a
        obtain ⟨j, bb⟩ := b
        have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
          have := i.isLt
          omega)
        have hj : j = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
          have := j.isLt
          omega)
        subst hi
        subst hj
        cases ba <;> cases bb
        · rfl
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rfl,
        by decide⟩)
  vertexEquiv := @_root_.Equiv.equivOfIsEmpty _ _ (by infer_instance) (by infer_instance)
  attach_comm := fun g => by
    obtain ⟨i, b⟩ := g
    have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
      have := i.isLt
      omega)
    subst hi
    cases b <;> decide
  pairing_comm := fun g => by
    obtain ⟨i, b⟩ := g
    have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
      have := i.isLt
      omega)
    subst hi
    cases b <;> decide
  circles_eq := by decide

/-- The right snake fragment is the identity strand. -/
noncomputable def snakeFragREquiv :
    (strandBundle 1).Equiv snakeFragR where
  flagEquiv := _root_.Equiv.ofBijective
    (fun g : Fin 1 × Bool =>
      snakeFragR.boundaryFlag (if g.2 then 1 else 0))
    (by exact (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨by
        intro a b h
        obtain ⟨i, ba⟩ := a
        obtain ⟨j, bb⟩ := b
        have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
          have := i.isLt
          omega)
        have hj : j = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
          have := j.isLt
          omega)
        subst hi
        subst hj
        cases ba <;> cases bb
        · rfl
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rfl,
        by decide⟩)
  vertexEquiv := @_root_.Equiv.equivOfIsEmpty _ _ (by infer_instance) (by infer_instance)
  attach_comm := fun g => by
    obtain ⟨i, b⟩ := g
    have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
      have := i.isLt
      omega)
    subst hi
    cases b <;> decide
  pairing_comm := fun g => by
    obtain ⟨i, b⟩ := g
    have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by
      have := i.isLt
      omega)
    subst hi
    cases b <;> decide
  circles_eq := by decide

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The identity class on one strand. -/
noncomputable def idClass : HomSpace f.val (1 + 1) :=
  HomSpace.ofFragment f.val (strandBundle 1)

/-- **The left snake identity** on Hom classes. -/
theorem snake_left :
    HomSpace.comp f 1 3 1
      (HomSpace.tensor f 0 2 1 1 (coevClass f) (idClass f))
      (HomSpace.tensor f 1 1 2 0 (idClass f) (evClass f)) =
    idClass f := by
  rw [coevClass, evClass, idClass,
    HomSpace.tensor_ofFragment, HomSpace.tensor_ofFragment,
    HomSpace.comp_ofFragment]
  exact (HomSpace.ofFragment_congr f (snakeFragLEquiv).symm)

/-- **The right snake identity** on Hom classes. -/
theorem snake_right :
    HomSpace.comp f 1 3 1
      (HomSpace.tensor f 1 1 0 2 (idClass f) (coevClass f))
      (HomSpace.tensor f 2 0 1 1 (evClass f) (idClass f)) =
    idClass f := by
  rw [coevClass, evClass, idClass,
    HomSpace.tensor_ofFragment, HomSpace.tensor_ofFragment,
    HomSpace.comp_ofFragment]
  exact (HomSpace.ofFragment_congr f (snakeFragREquiv).symm)

end RS
