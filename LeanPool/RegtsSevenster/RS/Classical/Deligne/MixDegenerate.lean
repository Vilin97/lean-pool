/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixSumPow

/-!
# Mixed sums with degenerate counts

The nonvanishing half of Deligne 1.9 was established for mixed
sums `L.mix (p + 1) (q + 1)` with both counts strictly positive.
Nothing in the argument needs that.  The letter framework of
`MixedLetters` is stated at an arbitrary finite label type, the
super-trace computation behind `not_schurKilled_stdSuper` holds at
every pair of dimensions, and the only trace of positivity in the
existing chain is the shape of the objects carrying the letter
systems: an iterated binary sum `sumPow X k` has `k + 1` summands,
and the standard super object was equipped with letters only in
the form `stdSuper (p + 1) (q + 1)`.

Both are avoidable.  Here the ambient letter system is read off
directly from the indexed biproduct defining `L.mix r s`, whose
label type `Fin r ⊕ Fin s` is allowed to be empty, and the
`SuperVect` letter system is rebuilt on `stdSuper r s` at
arbitrary dimensions.  The two sides are joined exactly as before,
giving the nonvanishing statement for all counts `r s : ℕ`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

/-- The parity of a mixed letter label at arbitrary counts: even
on the unit summands, odd on the line summands. -/
abbrev mixParity (r s : ℕ) : Fin r ⊕ Fin s → Bool :=
  fun k => Sum.rec (fun _ => false) (fun _ => true) k

/-! ## The letter system of a mixed sum -/

section AmbientLetters

variable {D : Type u}

/-- **The letter system of a mixed sum**, read off from the
indexed biproduct: the inclusions and projections of the summands,
with the unit summands even and the line summands odd.  No
positivity of the counts is involved. -/
noncomputable def OddLine.mixLetters
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] [SymmetricCategory D]
    (L : OddLine D) (r s : ℕ) :
    MixedLetters (Fin r ⊕ Fin s) (mixParity r s) L.obj
      (L.mix r s) where
  ins k :=
    Sum.rec (fun i => biproduct.ι (L.mixFun r s) (Sum.inl i))
      (fun j => biproduct.ι (L.mixFun r s) (Sum.inr j)) k
  prj k :=
    Sum.rec (fun i => biproduct.π (L.mixFun r s) (Sum.inl i))
      (fun j => biproduct.π (L.mixFun r s) (Sum.inr j)) k
  ins_prj k := by
    cases k with
    | inl i => exact biproduct.ι_π_self (L.mixFun r s) (Sum.inl i)
    | inr j => exact biproduct.ι_π_self (L.mixFun r s) (Sum.inr j)
  ins_prj_ne {k k'} hkk' := by
    cases k with
    | inl i =>
      cases k' with
      | inl i' =>
        exact biproduct.ι_π_ne (L.mixFun r s)
          (fun h => hkk' (congrArg Sum.inl (Sum.inl.inj h)))
      | inr j' =>
        exact biproduct.ι_π_ne (L.mixFun r s) (by simp)
    | inr j =>
      cases k' with
      | inl i' =>
        exact biproduct.ι_π_ne (L.mixFun r s) (by simp)
      | inr j' =>
        exact biproduct.ι_π_ne (L.mixFun r s)
          (fun h => hkk' (congrArg Sum.inr (Sum.inr.inj h)))
  total := by
    refine Eq.trans ?_ (biproduct.total (f := L.mixFun r s))
    refine Finset.sum_congr rfl fun k _ => ?_
    cases k with
    | inl i => rfl
    | inr j => rfl

end AmbientLetters

/-! ## The letter system of the standard super object

The same letters on `stdSuper r s`, at arbitrary dimensions: unit
letters along the even coordinates, odd-line letters along the odd
coordinates. -/

section SuperLetters

open scoped TensorProduct

/-- The even component, as an additive map of homs. -/
private def evenAdd (V W : SuperVect) :
    (V ⟶ W) →+ (V.even →ₗ[ℂ] W.even) where
  toFun f := SuperVect.Hom.evenMap f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The odd component, as an additive map of homs. -/
private def oddAdd (V W : SuperVect) :
    (V ⟶ W) →+ (V.odd →ₗ[ℂ] W.odd) where
  toFun f := SuperVect.Hom.oddMap f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion of an even coordinate line. -/
noncomputable def evenIn (r s : ℕ) (i : Fin r) :
    𝟙_ SuperVect ⟶ stdSuper r s where
  evenMap := LinearMap.single ℂ (fun _ => ℂ) i
  oddMap := 0

/-- The projection onto an even coordinate line. -/
noncomputable def evenOut (r s : ℕ) (i : Fin r) :
    stdSuper r s ⟶ 𝟙_ SuperVect where
  evenMap := LinearMap.proj i
  oddMap := 0

/-- The inclusion of an odd coordinate line. -/
noncomputable def oddInto (r s : ℕ) (j : Fin s) :
    stdSuper 0 1 ⟶ stdSuper r s where
  evenMap := 0
  oddMap :=
    (LinearMap.single ℂ (fun _ => ℂ) j).comp
      (LinearMap.proj (0 : Fin 1))

/-- The projection onto an odd coordinate line. -/
noncomputable def oddOut (r s : ℕ) (j : Fin s) :
    stdSuper r s ⟶ stdSuper 0 1 where
  evenMap := 0
  oddMap := LinearMap.pi fun _ : Fin 1 => LinearMap.proj j

/-- The letter inclusions of the standard super object. -/
noncomputable def superIns (r s : ℕ) (k : Fin r ⊕ Fin s) :
    letterObj (stdSuper 0 1) (mixParity r s) k ⟶ stdSuper r s :=
  Sum.rec (fun i => evenIn r s i) (fun j => oddInto r s j) k

/-- The letter projections of the standard super object. -/
noncomputable def superPrj (r s : ℕ) (k : Fin r ⊕ Fin s) :
    stdSuper r s ⟶ letterObj (stdSuper 0 1) (mixParity r s) k :=
  Sum.rec (fun i => evenOut r s i) (fun j => oddOut r s j) k

/-- The letter decomposition of the identity of the standard super
object, at arbitrary dimensions. -/
private theorem superSum_total (r s : ℕ) :
    (∑ k : Fin r ⊕ Fin s,
      (superPrj r s k ≫ superIns r s k :
        stdSuper r s ⟶ stdSuper r s)) = 𝟙 (stdSuper r s) := by
  apply SuperVect.hom_ext
  · have h1 : SuperVect.Hom.evenMap
        ((∑ k : Fin r ⊕ Fin s, superPrj r s k ≫ superIns r s k :
            stdSuper r s ⟶ stdSuper r s)) =
        ∑ k : Fin r ⊕ Fin s,
          SuperVect.Hom.evenMap (superPrj r s k ≫ superIns r s k)
      := map_sum (evenAdd _ _) _ _
    rw [h1, Fintype.sum_sum_type]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.sum_apply]
    have hA : ∀ i : Fin r, SuperVect.Hom.evenMap
        (superPrj r s (Sum.inl i) ≫ superIns r s (Sum.inl i)) v =
        Pi.single i (v i) := fun i => rfl
    have hB : ∀ j : Fin s, SuperVect.Hom.evenMap
        (superPrj r s (Sum.inr j) ≫ superIns r s (Sum.inr j)) v = 0
      := fun j => rfl
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hA i,
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hB j,
      Finset.sum_const, smul_zero, add_zero]
    exact Finset.univ_sum_single v
  · have h1 : SuperVect.Hom.oddMap
        ((∑ k : Fin r ⊕ Fin s, superPrj r s k ≫ superIns r s k :
            stdSuper r s ⟶ stdSuper r s)) =
        ∑ k : Fin r ⊕ Fin s,
          SuperVect.Hom.oddMap (superPrj r s k ≫ superIns r s k)
      := map_sum (oddAdd _ _) _ _
    rw [h1, Fintype.sum_sum_type]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.sum_apply]
    have hA : ∀ i : Fin r, SuperVect.Hom.oddMap
        (superPrj r s (Sum.inl i) ≫ superIns r s (Sum.inl i)) v = 0
      := fun i => rfl
    have hB : ∀ j : Fin s, SuperVect.Hom.oddMap
        (superPrj r s (Sum.inr j) ≫ superIns r s (Sum.inr j)) v =
        Pi.single j (v j) := fun j => rfl
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hA i,
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hB j,
      Finset.sum_const, smul_zero, zero_add]
    exact Finset.univ_sum_single v

/-- **The letter system of the standard super object** at
arbitrary dimensions. -/
noncomputable def superLetters (r s : ℕ) :
    MixedLetters (Fin r ⊕ Fin s) (mixParity r s)
      (stdSuper 0 1) (stdSuper r s) where
  ins := superIns r s
  prj := superPrj r s
  ins_prj k := by
    cases k with
    | inl i =>
      apply SuperVect.hom_ext
      · change (LinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ)
            i).comp (LinearMap.single ℂ (fun _ => ℂ) i) =
          LinearMap.id
        refine LinearMap.ext fun z => ?_
        change Pi.single (M := fun _ : Fin r => ℂ) i z i = z
        rw [Pi.single_eq_same]
      · refine LinearMap.ext fun z => ?_
        exact Subsingleton.elim (α := PUnit) _ _
    | inr j =>
      apply SuperVect.hom_ext
      · refine LinearMap.ext fun z => ?_
        exact Subsingleton.elim (α := Fin 0 → ℂ) _ _
      · change (LinearMap.pi fun _ : Fin 1 =>
            LinearMap.proj (R := ℂ)
              (φ := fun _ : Fin s => ℂ) j).comp
          ((LinearMap.single ℂ (fun _ => ℂ) j).comp
            (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0))
          = LinearMap.id
        refine LinearMap.ext fun v => ?_
        funext i
        change Pi.single (M := fun _ : Fin s => ℂ) j (v 0) j = v i
        rw [Pi.single_eq_same, Subsingleton.elim i 0]
  ins_prj_ne {k k'} hkk' := by
    cases k with
    | inl i =>
      cases k' with
      | inl i' =>
        apply SuperVect.hom_ext
        · change (LinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ)
              i').comp (LinearMap.single ℂ (fun _ => ℂ) i) = 0
          refine LinearMap.ext fun z => ?_
          change Pi.single (M := fun _ : Fin r => ℂ) i z i' = 0
          exact Pi.single_eq_of_ne (M := fun _ : Fin r => ℂ)
            (fun h => hkk' (congrArg Sum.inl h.symm)) z
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := PUnit) _ _
      | inr j' =>
        apply SuperVect.hom_ext
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := Fin 0 → ℂ) _ _
        · refine LinearMap.ext fun z => ?_
          change (LinearMap.pi fun _ : Fin 1 =>
              LinearMap.proj (R := ℂ)
                (φ := fun _ : Fin s => ℂ) j')
            ((0 : PUnit →ₗ[ℂ] (Fin s → ℂ)) z) = 0
          rw [LinearMap.zero_apply, map_zero]
    | inr j =>
      cases k' with
      | inl i' =>
        apply SuperVect.hom_ext
        · refine LinearMap.ext fun z => ?_
          change (LinearMap.proj (R := ℂ)
              (φ := fun _ : Fin r => ℂ) i')
            ((0 : (Fin 0 → ℂ) →ₗ[ℂ] (Fin r → ℂ)) z) = 0
          rfl
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := PUnit) _ _
      | inr j' =>
        apply SuperVect.hom_ext
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := Fin 0 → ℂ) _ _
        · change (LinearMap.pi fun _ : Fin 1 =>
              LinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ)
                j').comp
            ((LinearMap.single ℂ (fun _ => ℂ) j).comp
              (LinearMap.proj (R := ℂ)
                (φ := fun _ : Fin 1 => ℂ) 0)) = 0
          refine LinearMap.ext fun v => ?_
          funext i
          change Pi.single (M := fun _ : Fin s => ℂ) j (v 0) j' = 0
          exact Pi.single_eq_of_ne (M := fun _ : Fin s => ℂ)
            (fun h => hkk' (congrArg Sum.inr h.symm)) (v 0)
  total := superSum_total r s

end SuperLetters

end RS
