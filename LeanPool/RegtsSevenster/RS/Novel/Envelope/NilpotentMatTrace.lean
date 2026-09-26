/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatSemisimple

/-!
# The nilpotent leg of the matrix-envelope trace

Nilpotent endomorphisms of matrix-envelope objects have vanishing
diagonal trace.  The argument stays inside the original
endomorphism algebra: the atomic idempotent decompositions of each
entry algebra split the trace into atom-level diagonal entries;
the scalar matrix extracted through chosen iso-class
representatives multiplies like the endomorphism (idempotent
insertion), is supported on class blocks (the dichotomy), and
inherits nilpotency — so each class block has vanishing complex
trace, and the diagonal trace is the class-weighted sum of those.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Idempotents

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Trace splitting along a complete orthogonal family -/

/-- The trace splits along a complete orthogonal idempotent
family: `tr x = ∑ₐ tr (eₐ x eₐ)`. -/
theorem karoubiTrace_split {X : Karoubi (SkeinObj f)}
    {ι : Type} [Fintype ι] (e : ι → End X)
    (hco : CompleteOrthogonalIdempotents e) (x : End X) :
    HomSpace.traceMap f.val X.X.arity x.f =
      ∑ a : ι, HomSpace.traceMap f.val X.X.arity
        ((e a).f ≫ x.f ≫ (e a).f) := by
  have h1 : x.f = (∑ a : ι, (e a).f) ≫ x.f := by
    rw [show (∑ a : ι, (e a).f) = X.p from by
      calc ∑ a : ι, (e a).f
          = ((∑ a : ι, e a : End X)).f :=
            (map_sum (karoubiHomAddHom X X) _ _).symm
        _ = ((1 : End X)).f := by rw [hco.complete]
        _ = X.p := rfl]
    rw [Karoubi.p_comp]
  conv_lhs => rw [h1,
    show (∑ a : ι, (e a).f) ≫ x.f =
      ∑ a : ι, (e a).f ≫ x.f from
        Preadditive.sum_comp _ _ _]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : (e a).f ≫ x.f = (e a).f ≫ ((e a).f ≫ x.f) := by
    rw [show (e a).f ≫ (e a).f ≫ x.f =
      ((e a).f ≫ (e a).f) ≫ x.f from by
        simp only [Category.assoc]]
    rw [show ((e a).f ≫ (e a).f : X.X ⟶ X.X) =
      (e a * e a).f from rfl]
    rw [(hco.idem a : e a * e a = e a)]
  rw [h2]
  exact (HomSpace.traceMap_comp_comm f ((e a).f)
      ((e a).f ≫ x.f)).trans
    (congrArg (HomSpace.traceMap f.val X.X.arity)
      (by
        change ((e a).f ≫ x.f) ≫ (e a).f =
          (e a).f ≫ x.f ≫ (e a).f
        exact Category.assoc _ _ _))

/-! ### Atom resolutions -/

/-- A choice of atomic idempotent decompositions for every entry
of a matrix-envelope object. -/
structure AtomResolution (M : Mat_ (Karoubi (SkeinObj f))) where
  /-- The atom index of each entry. -/
  idx : M.ι → Type
  /-- Finiteness. -/
  fin : ∀ i, Fintype (idx i)
  /-- The idempotent families. -/
  e : ∀ i, idx i → End (M.X i)
  /-- Complete orthogonality. -/
  complete : ∀ i, CompleteOrthogonalIdempotents (e i)
  /-- Atomicity. -/
  atomic : ∀ i a, IsAtomicIdempotent (e i a)

/-- Atom resolutions exist. -/
noncomputable def atomResolution
    (M : Mat_ (Karoubi (SkeinObj f))) : AtomResolution f M := by
  have h : ∀ i : M.ι, ∃ (ι : Type) (_ : Fintype ι)
      (e : ι → End (M.X i)),
      CompleteOrthogonalIdempotents e ∧
        ∀ a, IsAtomicIdempotent (e a) := fun i => by
    have := karoubiEndFinite f (M.X i)
    have := karoubiEnd_isSemisimpleRing f (M.X i)
    exact exists_completeOrthogonal_atomic
  choose idx fin e hco hatom using h
  exact ⟨idx, fin, e, hco, hatom⟩

attribute [instance] AtomResolution.fin

/-- The diagonal trace refined along an atom resolution. -/
theorem matTrace_resolution
    {M : Mat_ (Karoubi (SkeinObj f))}
    (A : AtomResolution f M) (φ : End M) :
    matTrace f M φ = ∑ i : M.ι, ∑ a : A.idx i,
      HomSpace.traceMap f.val (M.X i).X.arity
        ((A.e i a).f ≫ (φ i i).f ≫ (A.e i a).f) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact karoubiTrace_split f (A.e i) (A.complete i) (φ i i)

/-! ### The atoms of a resolution -/

variable {f} {M : Mat_ (Karoubi (SkeinObj f))}

/-- The total atom index. -/
@[reducible] def AtomResolution.κ (A : AtomResolution f M) :=
  Σ i : M.ι, A.idx i

/-- The atom at a total index. -/
@[reducible] noncomputable def AtomResolution.S
    (A : AtomResolution f M) (p : A.κ) :
    Karoubi (SkeinObj f) :=
  cutBy (f := f) (M.X p.1) (A.atomic p.1 p.2).idem

/-- The atoms are atoms. -/
theorem AtomResolution.isAtom_S (A : AtomResolution f M)
    (p : A.κ) : IsAtom f (A.S p) :=
  isAtom_cutBy (f := f) (M.X p.1) (A.atomic p.1 p.2)

/-! ### Scalar extraction on atoms -/

/-- The scalar of an atom endomorphism. -/
noncomputable def atomScalar {S : Karoubi (SkeinObj f)}
    (hS : IsAtom f S) (x : End S) : ℂ :=
  Classical.choose (hS.scalar x)

/-- The extracted scalar does what it says: the endomorphism is
that multiple of the identity. -/
theorem atomScalar_spec {S : Karoubi (SkeinObj f)}
    (hS : IsAtom f S) (x : End S) :
    x = atomScalar hS x • 𝟙 S :=
  Classical.choose_spec (hS.scalar x)

/-- The scalar is unique — an atom's identity is nonzero. -/
theorem atomScalar_unique {S : Karoubi (SkeinObj f)}
    (hS : IsAtom f S) {x : End S} {c : ℂ}
    (h : x = c • 𝟙 S) : atomScalar hS x = c := by
  by_contra hne
  have hsub : (c - atomScalar hS x) • 𝟙 S = 0 := by
    rw [sub_smul, ← h, ← atomScalar_spec hS x, sub_self]
  rcases smul_eq_zero.mp hsub with hc | hid
  · exact hne (sub_eq_zero.mp hc).symm
  · exact hS.id_ne_zero hid

/-- Extraction is additive. -/
theorem atomScalar_add {S : Karoubi (SkeinObj f)}
    (hS : IsAtom f S) (x y : End S) :
    atomScalar hS (x + y) =
      atomScalar hS x + atomScalar hS y := by
  refine atomScalar_unique hS ?_
  rw [add_smul, ← atomScalar_spec, ← atomScalar_spec]

/-- Extraction is multiplicative: composition of atom
endomorphisms is multiplication of scalars.  This is what lets the
scalar matrix inherit nilpotency. -/
theorem atomScalar_comp {S : Karoubi (SkeinObj f)}
    (hS : IsAtom f S) (x y : End S) :
    atomScalar hS ((x ≫ y : End S)) =
      atomScalar hS x * atomScalar hS y := by
  refine atomScalar_unique hS ?_
  rw [show (x ≫ y : End S) =
    (atomScalar hS x • 𝟙 S) ≫ (atomScalar hS y • 𝟙 S)
    from by rw [← atomScalar_spec, ← atomScalar_spec]]
  rw [CategoryTheory.Linear.smul_comp,
    CategoryTheory.Linear.comp_smul, Category.id_comp,
    smul_smul]

/-! ### The class structure -/

open scoped Classical in
/-- Atoms are related when isomorphic. -/
noncomputable def AtomResolution.rel (A : AtomResolution f M)
    (p q : A.κ) : Prop :=
  Nonempty (A.S p ≅ A.S q)

/-- Isomorphism of atoms is reflexive. -/
theorem AtomResolution.rel_refl (A : AtomResolution f M)
    (p : A.κ) : A.rel p p := ⟨Iso.refl _⟩

/-- It is symmetric. -/
theorem AtomResolution.rel_symm (A : AtomResolution f M)
    {p q : A.κ} (h : A.rel p q) : A.rel q p :=
  ⟨h.some.symm⟩

/-- It is transitive. -/
theorem AtomResolution.rel_trans (A : AtomResolution f M)
    {p q r : A.κ} (h : A.rel p q) (h' : A.rel q r) :
    A.rel p r := ⟨h.some.trans h'.some⟩

/-- A fixed decidability instance, so all filters elaborate
uniformly. -/
noncomputable instance AtomResolution.relDec
    (A : AtomResolution f M) (p q : A.κ) :
    Decidable (A.rel p q) := Classical.dec _

/-! ### Representatives and chosen isomorphisms -/

/-- The class representative: the enumeration-minimal related
index. -/
noncomputable def AtomResolution.rep (A : AtomResolution f M)
    (p : A.κ) : A.κ :=
  (Fintype.equivFin A.κ).symm
    (((Finset.univ.filter (fun q => A.rel p q)).image
      (Fintype.equivFin A.κ)).min' (by
        refine Finset.image_nonempty.mpr ⟨p, ?_⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ p, A.rel_refl p⟩))

/-- An atom is isomorphic to its class representative. -/
theorem AtomResolution.rel_rep (A : AtomResolution f M)
    (p : A.κ) : A.rel p (A.rep p) := by
  have hmem := Finset.min'_mem
    (((Finset.univ.filter (fun q => A.rel p q)).image
      (Fintype.equivFin A.κ))) (by
        refine Finset.image_nonempty.mpr ⟨p, ?_⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ p, A.rel_refl p⟩)
  obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_filter] at hq
  unfold AtomResolution.rep
  rw [show ((Finset.univ.filter (fun q => A.rel p q)).image
      (Fintype.equivFin A.κ)).min' _ =
    (Fintype.equivFin A.κ) q from hqe.symm]
  rw [Equiv.symm_apply_apply]
  exact hq.2

/-- Isomorphic atoms have the same representative. -/
theorem AtomResolution.rep_eq_of_rel (A : AtomResolution f M)
    {p q : A.κ} (h : A.rel p q) : A.rep p = A.rep q := by
  have hset : (Finset.univ.filter (fun r => A.rel p r)) =
      (Finset.univ.filter (fun r => A.rel q r)) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · exact fun ⟨hu, hr⟩ =>
        ⟨hu, A.rel_trans (A.rel_symm h) hr⟩
    · exact fun ⟨hu, hr⟩ => ⟨hu, A.rel_trans h hr⟩
  unfold AtomResolution.rep
  simp only [hset]

/-- The chosen isomorphism from the representative atom. -/
noncomputable def AtomResolution.w (A : AtomResolution f M)
    (p : A.κ) : A.S (A.rep p) ≅ A.S p :=
  (A.rel_symm (A.rel_rep p)).some

/-! ### The matrix elements -/

/-- The matrix element of an endomorphism at a pair of atoms. -/
noncomputable def AtomResolution.t (A : AtomResolution f M)
    (φ : End M) (p q : A.κ) : A.S p ⟶ A.S q :=
  ⟨(A.e p.1 p.2).f ≫ (φ p.1 q.1).f ≫ (A.e q.1 q.2).f, by
    change (A.e p.1 p.2).f ≫ ((A.e p.1 p.2).f ≫
        (φ p.1 q.1).f ≫ (A.e q.1 q.2).f) ≫
      (A.e q.1 q.2).f = _
    rw [show (A.e p.1 p.2).f ≫ ((A.e p.1 p.2).f ≫
        (φ p.1 q.1).f ≫ (A.e q.1 q.2).f) ≫
        (A.e q.1 q.2).f =
      ((A.e p.1 p.2).f ≫ (A.e p.1 p.2).f) ≫
        (φ p.1 q.1).f ≫
        ((A.e q.1 q.2).f ≫ (A.e q.1 q.2).f) from by
        simp only [Category.assoc]]
    rw [show ((A.e p.1 p.2).f ≫ (A.e p.1 p.2).f :
        (M.X p.1).X ⟶ (M.X p.1).X) =
      (A.e p.1 p.2 * A.e p.1 p.2).f from rfl]
    rw [show ((A.e q.1 q.2).f ≫ (A.e q.1 q.2).f :
        (M.X q.1).X ⟶ (M.X q.1).X) =
      (A.e q.1 q.2 * A.e q.1 q.2).f from rfl]
    rw [((A.complete p.1).idem p.2 :
      A.e p.1 p.2 * A.e p.1 p.2 = A.e p.1 p.2)]
    rw [((A.complete q.1).idem q.2 :
      A.e q.1 q.2 * A.e q.1 q.2 = A.e q.1 q.2)]⟩

/-- The matrix element's underlying morphism: the entry cut down by
the two atoms' idempotents. -/
theorem AtomResolution.t_f (A : AtomResolution f M)
    (φ : End M) (p q : A.κ) :
    (A.t φ p q).f = (A.e p.1 p.2).f ≫ (φ p.1 q.1).f ≫
      (A.e q.1 q.2).f := rfl

/-- Cross-class matrix elements vanish (the dichotomy). -/
theorem AtomResolution.t_eq_zero (A : AtomResolution f M)
    (φ : End M) {p q : A.κ} (h : ¬ A.rel p q) :
    A.t φ p q = 0 := by
  by_contra hne
  obtain ⟨ψ, hψ₁, hψ₂⟩ := atom_iso_of_ne_zero f
    (A.isAtom_S p) (A.isAtom_S q) hne
  exact h ⟨⟨A.t φ p q, ψ, hψ₁, hψ₂⟩⟩

/-- **Multiplicativity of the matrix elements**: idempotent
insertion turns the composite's elements into the matrix product
of elements. -/
theorem AtomResolution.t_comp (A : AtomResolution f M)
    (φ ψ : End M) (p r : A.κ) :
    A.t ((φ ≫ ψ : End M)) p r =
      ∑ q : A.κ, (A.t φ p q ≫ A.t ψ q r : A.S p ⟶ A.S r) := by
  apply Karoubi.hom_ext
  rw [show ((∑ q : A.κ, (A.t φ p q ≫ A.t ψ q r :
      A.S p ⟶ A.S r))).f =
    ∑ q : A.κ, ((A.t φ p q ≫ A.t ψ q r :
      A.S p ⟶ A.S r)).f from map_sum (karoubiHomAddHom _ _) _ _]
  rw [A.t_f]
  rw [show ((φ ≫ ψ : End M) p.1 r.1) =
    ∑ j : M.ι, φ p.1 j ≫ ψ j r.1 from rfl]
  rw [show ((∑ j : M.ι, φ p.1 j ≫ ψ j r.1 :
      M.X p.1 ⟶ M.X r.1)).f =
    ∑ j : M.ι, ((φ p.1 j ≫ ψ j r.1 :
      M.X p.1 ⟶ M.X r.1)).f from map_sum (karoubiHomAddHom _ _) _ _]
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  rw [show (∑ q : A.κ, ((A.t φ p q ≫ A.t ψ q r :
      A.S p ⟶ A.S r)).f) =
    ∑ j : M.ι, ∑ b : A.idx j,
      ((A.t φ p ⟨j, b⟩ ≫ A.t ψ ⟨j, b⟩ r :
        A.S p ⟶ A.S r)).f from by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- Per middle object: the inner idempotents sum to the
  -- identity and absorb.
  have hstep : ∀ b : A.idx j,
      ((A.t φ p ⟨j, b⟩ ≫ A.t ψ ⟨j, b⟩ r :
        A.S p ⟶ A.S r)).f =
      (A.e p.1 p.2).f ≫ (φ p.1 j).f ≫ (A.e j b).f ≫
        (ψ j r.1).f ≫ (A.e r.1 r.2).f := by
    intro b
    rw [show ((A.t φ p ⟨j, b⟩ ≫ A.t ψ ⟨j, b⟩ r :
        A.S p ⟶ A.S r)).f =
      (A.t φ p ⟨j, b⟩).f ≫ (A.t ψ ⟨j, b⟩ r).f from rfl]
    rw [A.t_f, A.t_f]
    rw [show ((A.e p.1 p.2).f ≫ (φ p.1 j).f ≫
        (A.e j b).f) ≫ ((A.e j b).f ≫ (ψ j r.1).f ≫
        (A.e r.1 r.2).f) =
      (A.e p.1 p.2).f ≫ (φ p.1 j).f ≫
        ((A.e j b).f ≫ (A.e j b).f) ≫ (ψ j r.1).f ≫
        (A.e r.1 r.2).f from by
        simp only [Category.assoc]]
    rw [show ((A.e j b).f ≫ (A.e j b).f :
        (M.X j).X ⟶ (M.X j).X) =
      (A.e j b * A.e j b).f from rfl]
    rw [((A.complete j).idem b :
      A.e j b * A.e j b = A.e j b)]
  rw [Finset.sum_congr rfl fun b _ => hstep b]
  rw [show (∑ b : A.idx j, (A.e p.1 p.2).f ≫
      (φ p.1 j).f ≫ (A.e j b).f ≫ (ψ j r.1).f ≫
      (A.e r.1 r.2).f) =
    (A.e p.1 p.2).f ≫ (φ p.1 j).f ≫
      (∑ b : A.idx j, (A.e j b).f) ≫ (ψ j r.1).f ≫
      (A.e r.1 r.2).f from by
      rw [Preadditive.sum_comp, Preadditive.comp_sum,
        Preadditive.comp_sum]]
  rw [show (∑ b : A.idx j, (A.e j b).f) = (M.X j).p from by
    calc ∑ b : A.idx j, (A.e j b).f
        = ((∑ b : A.idx j, A.e j b : End (M.X j))).f :=
          (map_sum (karoubiHomAddHom (M.X j) (M.X j)) _ _).symm
      _ = ((1 : End (M.X j))).f := by
          rw [(A.complete j).complete]
      _ = (M.X j).p := rfl]
  suffices h : ((φ p.1 j ≫ ψ j r.1 :
      M.X p.1 ⟶ M.X r.1)).f =
      (φ p.1 j).f ≫ (M.X j).p ≫ (ψ j r.1).f by
    rw [h]
    simp only [Category.assoc]
  rw [show ((φ p.1 j ≫ ψ j r.1 :
      M.X p.1 ⟶ M.X r.1)).f =
    (φ p.1 j).f ≫ (ψ j r.1).f from rfl]
  rw [show (φ p.1 j).f ≫ (M.X j).p ≫ (ψ j r.1).f =
    ((φ p.1 j).f ≫ (M.X j).p) ≫ (ψ j r.1).f from
    (Category.assoc _ _ _).symm]
  rw [Karoubi.comp_p]

/-! ### The scalar matrix -/

/-- Scalars are invariant under object-equality transport. -/
theorem atomScalar_eqToHom_conj
    {S T : Karoubi (SkeinObj f)} (h : S = T)
    (hS : IsAtom f S) (hT : IsAtom f T) (z : End T) :
    atomScalar hS
        ((eqToHom h ≫ z ≫ eqToHom h.symm : End S)) =
      atomScalar hT z := by
  subst h
  simp only [eqToHom_refl, Category.id_comp,
    Category.comp_id]

variable (A : AtomResolution f M)

open scoped Classical in
/-- The scalar matrix of an endomorphism over the atoms. -/
noncomputable def AtomResolution.B (φ : End M) :
    Matrix A.κ A.κ ℂ := fun p q =>
  if h : A.rep p = A.rep q then
    atomScalar (A.isAtom_S (A.rep p))
      (((A.w p).hom ≫ A.t φ p q ≫ (A.w q).inv ≫
        eqToHom (congrArg A.S h.symm) :
          End (A.S (A.rep p))))
  else 0

/-- **The dichotomy**: the scalar matrix vanishes off the class
blocks, there being no isomorphism to transport along. -/
theorem AtomResolution.B_apply_of_ne (φ : End M) {p q : A.κ}
    (h : ¬ A.rep p = A.rep q) : A.B φ p q = 0 :=
  dite_eq_right h

/-- The scalar matrix of the zero endomorphism is zero. -/
theorem AtomResolution.B_zero : A.B (0 : End M) = 0 := by
  funext p q
  change A.B 0 p q = 0
  unfold AtomResolution.B
  split_ifs with h
  · rw [show A.t (0 : End M) p q = 0 from by
      apply Karoubi.hom_ext
      rw [A.t_f]
      rw [show ((0 : End M) p.1 q.1) = 0 from rfl]
      rw [show ((0 : M.X p.1 ⟶ M.X q.1)).f = 0 from rfl]
      rw [Limits.zero_comp, Limits.comp_zero]
      rfl]
    rw [Limits.zero_comp]
    rw [show ((A.w p).hom ≫ (0 : A.S p ⟶ A.S (A.rep p)) :
        A.S (A.rep p) ⟶ A.S (A.rep p)) =
      ((A.w p).hom ≫ 0 : End (A.S (A.rep p))) from rfl]
    rw [Limits.comp_zero]
    exact atomScalar_unique _ (by rw [zero_smul])
  · rfl

/-- **Multiplicativity of the scalar matrix.** -/
theorem AtomResolution.B_comp (φ ψ : End M) :
    A.B ((φ ≫ ψ : End M)) = A.B φ * A.B ψ := by
  funext p r
  rw [Matrix.mul_apply]
  by_cases h : A.rep p = A.rep r
  · rw [show A.B ((φ ≫ ψ : End M)) p r =
      atomScalar (A.isAtom_S (A.rep p))
        (((A.w p).hom ≫ A.t ((φ ≫ ψ : End M)) p r ≫
          (A.w r).inv ≫ eqToHom (congrArg A.S h.symm) :
            End (A.S (A.rep p)))) from dite_eq_left h]
    rw [A.t_comp φ ψ p r]
    rw [show ((A.w p).hom ≫
        (∑ q : A.κ, (A.t φ p q ≫ A.t ψ q r :
          A.S p ⟶ A.S r)) ≫
        (A.w r).inv ≫ eqToHom (congrArg A.S h.symm) :
          End (A.S (A.rep p))) =
      ∑ q : A.κ, ((A.w p).hom ≫
        (A.t φ p q ≫ A.t ψ q r) ≫
        (A.w r).inv ≫ eqToHom (congrArg A.S h.symm) :
          End (A.S (A.rep p))) from by
        rw [Preadditive.sum_comp, Preadditive.comp_sum]]
    refine Eq.trans (show atomScalar (A.isAtom_S (A.rep p))
        (∑ q : A.κ, ((A.w p).hom ≫
          (A.t φ p q ≫ A.t ψ q r) ≫
          (A.w r).inv ≫ eqToHom (congrArg A.S h.symm) :
            End (A.S (A.rep p)))) =
      ∑ q : A.κ, atomScalar (A.isAtom_S (A.rep p))
        (((A.w p).hom ≫ (A.t φ p q ≫ A.t ψ q r) ≫
          (A.w r).inv ≫ eqToHom (congrArg A.S h.symm) :
            End (A.S (A.rep p)))) from by
        classical
        induction (Finset.univ : Finset A.κ) using
          Finset.induction_on with
        | empty =>
            rw [Finset.sum_empty, Finset.sum_empty]
            exact atomScalar_unique _ (by rw [zero_smul])
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha,
              atomScalar_add, ih]) ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : A.rep p = A.rep q
    · rw [show A.B φ p q = atomScalar (A.isAtom_S (A.rep p))
        (((A.w p).hom ≫ A.t φ p q ≫ (A.w q).inv ≫
          eqToHom (congrArg A.S hq.symm) :
            End (A.S (A.rep p)))) from dite_eq_left hq]
      have hqr : A.rep q = A.rep r := hq ▸ h
      rw [show A.B ψ q r = atomScalar (A.isAtom_S (A.rep q))
        (((A.w q).hom ≫ A.t ψ q r ≫ (A.w r).inv ≫
          eqToHom (congrArg A.S hqr.symm) :
            End (A.S (A.rep q)))) from dite_eq_left hqr]
      rw [← atomScalar_eqToHom_conj (congrArg A.S hq)
        (A.isAtom_S (A.rep p)) (A.isAtom_S (A.rep q))]
      rw [← atomScalar_comp]
      congr 1
      -- Pure composition algebra: cancel the middle iso and
      -- the transport pair.
      rw [show ((A.w p).hom ≫ A.t φ p q ≫ (A.w q).inv ≫
          eqToHom (congrArg A.S hq.symm) : _) ≫
        (eqToHom (congrArg A.S hq) ≫
          ((A.w q).hom ≫ A.t ψ q r ≫ (A.w r).inv ≫
            eqToHom (congrArg A.S hqr.symm)) ≫
          eqToHom (congrArg A.S hq).symm) =
        (A.w p).hom ≫ A.t φ p q ≫
          ((A.w q).inv ≫ (A.w q).hom) ≫ A.t ψ q r ≫
          (A.w r).inv ≫
          (eqToHom (congrArg A.S hqr.symm) ≫
            eqToHom (congrArg A.S hq).symm) from by
        simp only [Category.assoc, eqToHom_trans,
          eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]]
      rw [Iso.inv_hom_id, Category.id_comp]
      rw [eqToHom_trans]
      simp only [Category.assoc]
    · rw [A.B_apply_of_ne φ hq, zero_mul]
      rw [A.t_eq_zero φ (fun hrel => hq
        (A.rep_eq_of_rel hrel))]
      rw [Limits.zero_comp]
      rw [show ((A.w p).hom ≫
          ((0 : A.S p ⟶ A.S r) ≫
            (A.w r).inv ≫ eqToHom (congrArg A.S h.symm)) :
          End (A.S (A.rep p))) =
        0 from by
          rw [Limits.zero_comp, Limits.comp_zero]]
      exact atomScalar_unique _ (by rw [zero_smul])
  · rw [A.B_apply_of_ne _ h]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    by_cases hq : A.rep p = A.rep q
    · rw [A.B_apply_of_ne ψ (fun hqr => h (hq.trans hqr)),
        mul_zero]
    · rw [A.B_apply_of_ne φ hq, zero_mul]

/-- The total atom index has decidable equality, classically. -/
noncomputable instance AtomResolution.kappaDec :
    DecidableEq A.κ := Classical.decEq _

/-- Powers transport to matrix powers. -/
theorem AtomResolution.B_pow (φ : End M) (k : ℕ) :
    A.B ((φ ^ (k + 1) : End M)) = (A.B φ) ^ (k + 1) := by
  induction k with
  | zero => rw [pow_one, pow_one]
  | succ j ih =>
      rw [show (φ ^ (j + 1 + 1) : End M) =
        ((φ ≫ φ ^ (j + 1) : End M)) from by
          rw [show ((φ ≫ φ ^ (j + 1) : End M)) =
            φ ^ (j + 1) * φ from rfl, ← pow_succ]]
      rw [A.B_comp, ih, ← pow_succ']

/-- The diagonal scalar recovers the diagonal trace entry, up to
the class weight. -/
theorem AtomResolution.trace_t_diag (φ : End M) (p : A.κ) :
    HomSpace.traceMap f.val (M.X p.1).X.arity
        (A.t φ p p).f =
      A.B φ p p *
        HomSpace.traceMap f.val
          (M.X (A.rep p).1).X.arity
          (Karoubi.Hom.f (𝟙 (A.S (A.rep p)))) := by
  have hBpp : A.B φ p p =
      atomScalar (A.isAtom_S (A.rep p))
        (((A.w p).hom ≫ A.t φ p p ≫ (A.w p).inv ≫
          eqToHom (congrArg A.S (rfl : A.rep p = A.rep p).symm) :
            End (A.S (A.rep p)))) := dite_eq_left rfl
  rw [show eqToHom (congrArg A.S
      (rfl : A.rep p = A.rep p).symm) =
    𝟙 (A.S (A.rep p)) from eqToHom_refl _ _,
    Category.comp_id] at hBpp
  -- Recover t from its scalar through the chosen iso.
  have hspec := atomScalar_spec (A.isAtom_S (A.rep p))
    (((A.w p).hom ≫ A.t φ p p ≫ (A.w p).inv ≫
      eqToHom (congrArg A.S (rfl : A.rep p = A.rep p).symm) :
        End (A.S (A.rep p))))
  rw [show eqToHom (congrArg A.S
      (rfl : A.rep p = A.rep p).symm) =
    𝟙 (A.S (A.rep p)) from eqToHom_refl _ _] at hspec
  rw [Category.comp_id] at hspec
  have ht : A.t φ p p =
      A.B φ p p • ((A.w p).inv ≫ (A.w p).hom) := by
    have h2 := congrArg
      (fun z => (A.w p).inv ≫ z ≫ (A.w p).hom) hspec
    rw [show (A.w p).inv ≫ ((A.w p).hom ≫ A.t φ p p ≫
        (A.w p).inv) ≫ (A.w p).hom =
      ((A.w p).inv ≫ (A.w p).hom) ≫ A.t φ p p ≫
        ((A.w p).inv ≫ (A.w p).hom) from by
        simp only [Category.assoc]] at h2
    rw [Iso.inv_hom_id, Category.id_comp] at h2
    rw [Category.comp_id] at h2
    rw [h2, ← hBpp]
    rw [CategoryTheory.Linear.smul_comp,
      CategoryTheory.Linear.comp_smul, Category.id_comp]
  rw [show (A.t φ p p).f =
    (A.B φ p p • ((A.w p).inv ≫ (A.w p).hom :
      End (A.S p))).f from by rw [← ht]]
  rw [show ((A.B φ p p • ((A.w p).inv ≫ (A.w p).hom :
      End (A.S p)))).f =
    A.B φ p p • (((A.w p).inv ≫ (A.w p).hom :
      End (A.S p))).f from rfl]
  rw [map_smul, smul_eq_mul]
  congr 1
  -- The weight is class-constant: cyclicity swaps the iso pair.
  rw [show (((A.w p).inv ≫ (A.w p).hom : End (A.S p))).f =
    ((A.w p).inv).f ≫ ((A.w p).hom).f from rfl]
  exact (HomSpace.traceMap_comp_comm f (((A.w p).inv).f)
      (((A.w p).hom).f)).trans
    (congrArg
      (HomSpace.traceMap f.val (M.X (A.rep p).1).X.arity)
      (show ((A.w p).hom).f ≫ ((A.w p).inv).f =
        Karoubi.Hom.f (𝟙 (A.S (A.rep p))) from by
          rw [show ((A.w p).hom).f ≫ ((A.w p).inv).f =
            Karoubi.Hom.f ((A.w p).hom ≫ (A.w p).inv)
            from rfl]
          rw [Iso.hom_inv_id]))

/-! ### Class-block restriction -/

/-- The scalar matrix is supported on class blocks. -/
theorem AtomResolution.B_support (φ : End M) {p q : A.κ}
    (h : A.B φ p q ≠ 0) : A.rep p = A.rep q := by
  by_contra hne
  exact h (A.B_apply_of_ne φ hne)

/-- The class-block restriction of a matrix. -/
noncomputable def AtomResolution.restrict (c : A.κ)
    (X : Matrix A.κ A.κ ℂ) :
    Matrix {p : A.κ // A.rep p = c}
      {p : A.κ // A.rep p = c} ℂ :=
  fun p q => X p.val q.val

/-- Products preserve block support. -/
theorem AtomResolution.support_mul
    (X Y : Matrix A.κ A.κ ℂ)
    (hX : ∀ p q, X p q ≠ 0 → A.rep p = A.rep q)
    (hY : ∀ p q, Y p q ≠ 0 → A.rep p = A.rep q) :
    ∀ p q, (X * Y) p q ≠ 0 → A.rep p = A.rep q := by
  intro p q h
  rw [Matrix.mul_apply] at h
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hXr : X p r ≠ 0 := fun h0 => hr (by rw [h0, zero_mul])
  have hYr : Y r q ≠ 0 := fun h0 => hr (by rw [h0, mul_zero])
  exact (hX p r hXr).trans (hY r q hYr)

/-- Restriction respects products of block-supported
matrices. -/
theorem AtomResolution.restrict_mul (c : A.κ)
    (X Y : Matrix A.κ A.κ ℂ)
    (hX : ∀ p q, X p q ≠ 0 → A.rep p = A.rep q) :
    A.restrict c (X * Y) =
      A.restrict c X * A.restrict c Y := by
  classical
  funext p q
  rw [show A.restrict c (X * Y) p q = (X * Y) p.val q.val
    from rfl]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun r => A.rep r = c) _]
  rw [show (∑ r ∈ Finset.univ.filter
      (fun r => ¬ A.rep r = c),
      X p.val r * Y r q.val) = 0 from
    Finset.sum_eq_zero fun r hr => by
      rw [Finset.mem_filter] at hr
      rw [show X p.val r = 0 from by
        by_contra h0
        exact hr.2 ((hX p.val r h0).symm.trans p.prop)]
      rw [zero_mul]]
  rw [add_zero]
  exact Finset.sum_subtype (Finset.univ.filter
      (fun r => A.rep r = c))
    (fun r => by
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ r, h⟩⟩)
    (fun r => X p.val r * Y r q.val)

/-- Powers preserve block support. -/
theorem AtomResolution.support_pow
    (X : Matrix A.κ A.κ ℂ)
    (hX : ∀ p q, X p q ≠ 0 → A.rep p = A.rep q) (k : ℕ) :
    ∀ p q, (X ^ (k + 1)) p q ≠ 0 → A.rep p = A.rep q := by
  induction k with
  | zero =>
      rw [pow_one]
      exact hX
  | succ l ihl =>
      rw [pow_succ X (l + 1)]
      exact A.support_mul _ _ ihl hX

/-- Restriction respects powers of block-supported matrices. -/
theorem AtomResolution.restrict_pow (c : A.κ)
    (X : Matrix A.κ A.κ ℂ)
    (hX : ∀ p q, X p q ≠ 0 → A.rep p = A.rep q) (k : ℕ) :
    A.restrict c (X ^ (k + 1)) =
      (A.restrict c X) ^ (k + 1) := by
  induction k with
  | zero => rw [pow_one, pow_one]
  | succ j ih =>
      rw [pow_succ X (j + 1),
        pow_succ (A.restrict c X) (j + 1)]
      rw [A.restrict_mul c _ _ (A.support_pow X hX j), ih]

/-! ### The nilpotent leg -/

/-- The class weight: the closure trace of an atom identity. -/
noncomputable def AtomResolution.δ (c : A.κ) : ℂ :=
  HomSpace.traceMap f.val (M.X c.1).X.arity
    (Karoubi.Hom.f (𝟙 (A.S c)))

/-- **The nilpotent leg**: nilpotent matrix-envelope
endomorphisms have vanishing diagonal trace. -/
theorem matTrace_eq_zero_of_isNilpotent'
    {φ : End M} (hφ : IsNilpotent φ) :
    matTrace f M φ = 0 := by
  classical
  obtain ⟨k, hk⟩ := hφ
  cases k with
  | zero =>
      have h10 : (1 : End M) = 0 := by
        rw [← pow_zero φ, hk]
      have hφ0 : φ = 0 := by
        calc φ = φ * 1 := (mul_one φ).symm
          _ = φ * 0 := by rw [h10]
          _ = 0 := mul_zero φ
      rw [hφ0, map_zero]
  | succ j =>
      set A := atomResolution f M with hA
      have hBnil : (A.B φ) ^ (j + 1) = 0 := by
        rw [← A.B_pow φ j, hk, A.B_zero]
      calc matTrace f M φ
          = ∑ p : A.κ,
              HomSpace.traceMap f.val (M.X p.1).X.arity
                ((A.e p.1 p.2).f ≫ (φ p.1 p.1).f ≫
                  (A.e p.1 p.2).f) := by
            rw [matTrace_resolution f A φ]
            rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        _ = ∑ p : A.κ, A.B φ p p * A.δ (A.rep p) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            exact A.trace_t_diag φ p
        _ = ∑ c : A.κ, ∑ p ∈ Finset.univ.filter
              (fun p => A.rep p = c),
              A.B φ p p * A.δ (A.rep p) :=
            (Finset.sum_fiberwise_of_maps_to
              (fun p _ => Finset.mem_univ (A.rep p)) _).symm
        _ = ∑ c : A.κ, A.δ c * ∑ p ∈ Finset.univ.filter
              (fun p => A.rep p = c), A.B φ p p := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [Finset.mem_filter] at hp
            rw [hp.2, mul_comm]
        _ = 0 := by
            refine Finset.sum_eq_zero fun c _ => ?_
            have htr : (∑ p ∈ Finset.univ.filter
                (fun p => A.rep p = c), A.B φ p p) =
              Matrix.trace (A.restrict c (A.B φ)) :=
              Finset.sum_subtype (Finset.univ.filter
                  (fun r => A.rep r = c))
                (fun r => by
                  rw [Finset.mem_filter]
                  exact ⟨fun h => h.2,
                    fun h => ⟨Finset.mem_univ r, h⟩⟩)
                (fun r => A.B φ r r)
            rw [htr]
            have hnil : IsNilpotent
                (A.restrict c (A.B φ)) := by
              refine ⟨j + 1, ?_⟩
              rw [← A.restrict_pow c _
                (fun p q h => A.B_support φ h) j, hBnil]
              funext p q
              rfl
            have := Matrix.isNilpotent_trace_of_isNilpotent
              hnil
            rw [IsNilpotent.eq_zero this, mul_zero]

end RS
