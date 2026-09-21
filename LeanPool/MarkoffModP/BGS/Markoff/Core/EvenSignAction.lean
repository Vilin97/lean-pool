/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Action

/-!
# Even sign changes on the Markoff surface

Changing the signs of exactly two coordinates preserves the Markoff equation.
The four transformations form a Klein four-group. Vieta involutions commute
with them, and coordinate transpositions permute them. Thus `Gamma` normalizes
the even-sign subgroup.
-/

namespace BGS.Markoff

universe u

/-- The four sign vectors with product one. -/
inductive EvenSign
  | id
  | neg12
  | neg13
  | neg23
  deriving DecidableEq, Repr

instance : Fintype EvenSign where
  elems := {.id, .neg12, .neg13, .neg23}
  complete x := by cases x <;> simp

namespace EvenSign

def mul : EvenSign → EvenSign → EvenSign
  | .id, s => s
  | s, .id => s
  | .neg12, .neg12 => .id
  | .neg12, .neg13 => .neg23
  | .neg12, .neg23 => .neg13
  | .neg13, .neg12 => .neg23
  | .neg13, .neg13 => .id
  | .neg13, .neg23 => .neg12
  | .neg23, .neg12 => .neg13
  | .neg23, .neg13 => .neg12
  | .neg23, .neg23 => .id

instance : One EvenSign := ⟨.id⟩
instance : Mul EvenSign := ⟨mul⟩
instance : Inv EvenSign := ⟨fun s => s⟩

instance : CommGroup EvenSign where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_comm := by decide

@[simp] theorem one_eq_id : (1 : EvenSign) = .id := rfl
@[simp] theorem inv_eq_self (s : EvenSign) : s⁻¹ = s := rfl
@[simp] theorem card_eq_four : Fintype.card EvenSign = 4 := by decide

end EvenSign

/-- Apply an even sign vector to an affine point. -/
def evenSignPoint {R : Type u} [CommRing R] : EvenSign → Point R → Point R
  | .id, x => x
  | .neg12, x => ⟨-x.x1, -x.x2, x.x3⟩
  | .neg13, x => ⟨-x.x1, x.x2, -x.x3⟩
  | .neg23, x => ⟨x.x1, -x.x2, -x.x3⟩

@[simp]
theorem evenSignPoint_id {R : Type u} [CommRing R] (x : Point R) :
    evenSignPoint .id x = x := rfl

@[simp]
theorem evenSignPoint_mul {R : Type u} [CommRing R]
    (s t : EvenSign) (x : Point R) :
    evenSignPoint (s * t) x = evenSignPoint s (evenSignPoint t x) := by
  change evenSignPoint (EvenSign.mul s t) x =
    evenSignPoint s (evenSignPoint t x)
  cases s <;> cases t <;> ext <;> simp [evenSignPoint, EvenSign.mul]

@[simp]
theorem markoffPolynomial_evenSignPoint {R : Type u} [CommRing R]
    (s : EvenSign) (x : Point R) :
    markoffPolynomial (evenSignPoint s x) = markoffPolynomial x := by
  cases s <;> simp [evenSignPoint, markoffPolynomial]

@[simp]
theorem isMarkoff_evenSignPoint {R : Type u} [CommRing R]
    (s : EvenSign) (x : Point R) :
    IsMarkoff (evenSignPoint s x) ↔ IsMarkoff x := by
  simp only [IsMarkoff, markoffPolynomial_evenSignPoint]

instance evenSignMulActionMarkoffSurface {R : Type u} [CommRing R] :
    MulAction EvenSign (MarkoffSurface R) where
  smul s x := ⟨evenSignPoint s x.1, (isMarkoff_evenSignPoint s x.1).2 x.2⟩
  one_smul x := Subtype.ext (evenSignPoint_id x.1)
  mul_smul s t x := Subtype.ext (evenSignPoint_mul s t x.1)

@[simp]
theorem evenSign_smul_surface_coe {R : Type u} [CommRing R]
    (s : EvenSign) (x : MarkoffSurface R) :
    ((s • x : MarkoffSurface R) : Point R) = evenSignPoint s x.1 := rfl

@[simp]
theorem evenSign_smul_surfaceOrigin {R : Type u} [CommRing R] (s : EvenSign) :
    s • surfaceOrigin R = surfaceOrigin R := by
  cases s <;> apply Subtype.ext <;> ext <;>
    simp [evenSignPoint, surfaceOrigin, origin]

theorem evenSign_smul_ne_surfaceOrigin_iff {R : Type u} [CommRing R]
    (s : EvenSign) (x : MarkoffSurface R) :
    s • x ≠ surfaceOrigin R ↔ x ≠ surfaceOrigin R := by
  constructor
  · intro hs hx
    exact hs (hx ▸ evenSign_smul_surfaceOrigin s)
  · intro hx hs
    apply hx
    calc
      x = s⁻¹ • (s • x) := (inv_smul_smul s x).symm
      _ = s⁻¹ • surfaceOrigin R := congrArg (s⁻¹ • ·) hs
      _ = surfaceOrigin R := evenSign_smul_surfaceOrigin s⁻¹

instance evenSignMulActionPuncturedMarkoffSurface {R : Type u} [CommRing R] :
    MulAction EvenSign (PuncturedMarkoffSurface R) where
  smul s x := ⟨s • x.1, (evenSign_smul_ne_surfaceOrigin_iff s x.1).2 x.2⟩
  one_smul x := Subtype.ext (one_smul EvenSign x.1)
  mul_smul s t x := Subtype.ext (mul_smul s t x.1)

@[simp]
theorem evenSign_smul_punctured_coe {R : Type u} [CommRing R]
    (s : EvenSign) (x : PuncturedMarkoffSurface R) :
    ((s • x : PuncturedMarkoffSurface R) : MarkoffSurface R) = s • x.1 := rfl

def evenSignSurfacePermHom (R : Type u) [CommRing R] :
    EvenSign →* Equiv.Perm (MarkoffSurface R) :=
  MulAction.toPermHom EvenSign (MarkoffSurface R)

@[simp]
theorem evenSignSurfacePermHom_apply {R : Type u} [CommRing R]
    (s : EvenSign) (x : MarkoffSurface R) :
    evenSignSurfacePermHom R s x = s • x := rfl

def evenSignSurfaceSubgroup (R : Type u) [CommRing R] :
    Subgroup (Equiv.Perm (MarkoffSurface R)) :=
  (evenSignSurfacePermHom R).range

@[simp]
theorem vieta1_evenSignPoint {R : Type u} [CommRing R]
    (s : EvenSign) (x : Point R) :
    vieta1 (evenSignPoint s x) = evenSignPoint s (vieta1 x) := by
  cases s <;> ext <;> simp [vieta1, evenSignPoint] <;> ring

@[simp]
theorem vieta2_evenSignPoint {R : Type u} [CommRing R]
    (s : EvenSign) (x : Point R) :
    vieta2 (evenSignPoint s x) = evenSignPoint s (vieta2 x) := by
  cases s <;> ext <;> simp [vieta2, evenSignPoint] <;> ring

@[simp]
theorem vieta3_evenSignPoint {R : Type u} [CommRing R]
    (s : EvenSign) (x : Point R) :
    vieta3 (evenSignPoint s x) = evenSignPoint s (vieta3 x) := by
  cases s <;> ext <;> simp [vieta3, evenSignPoint] <;> ring

def EvenSign.swap12 : EvenSign → EvenSign
  | .id => .id
  | .neg12 => .neg12
  | .neg13 => .neg23
  | .neg23 => .neg13

def EvenSign.swap23 : EvenSign → EvenSign
  | .id => .id
  | .neg12 => .neg13
  | .neg13 => .neg12
  | .neg23 => .neg23

@[simp] theorem EvenSign.swap12_swap12 (s : EvenSign) :
    s.swap12.swap12 = s := by cases s <;> rfl

@[simp] theorem EvenSign.swap23_swap23 (s : EvenSign) :
    s.swap23.swap23 = s := by cases s <;> rfl

@[simp]
theorem swap12_evenSignPoint {R : Type u} [CommRing R]
    (s : EvenSign) (x : Point R) :
    swap12 (evenSignPoint s x) = evenSignPoint s.swap12 (swap12 x) := by
  cases s <;> rfl

@[simp]
theorem swap23_evenSignPoint {R : Type u} [CommRing R]
    (s : EvenSign) (x : Point R) :
    swap23 (evenSignPoint s x) = evenSignPoint s.swap23 (swap23 x) := by
  cases s <;> rfl

private theorem perm_ext_of_point_coe_eq {R : Type u} [CommRing R]
    {f g : Equiv.Perm (MarkoffSurface R)}
    (h : ∀ x : MarkoffSurface R, ((f x : MarkoffSurface R) : Point R) = g x) :
    f = g := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact h x

theorem vieta1SurfacePerm_commute_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    vieta1SurfacePerm R * evenSignSurfacePermHom R s =
      evenSignSurfacePermHom R s * vieta1SurfacePerm R := by
  apply perm_ext_of_point_coe_eq
  intro x
  exact vieta1_evenSignPoint s x.1

theorem vieta2SurfacePerm_commute_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    vieta2SurfacePerm R * evenSignSurfacePermHom R s =
      evenSignSurfacePermHom R s * vieta2SurfacePerm R := by
  apply perm_ext_of_point_coe_eq
  intro x
  exact vieta2_evenSignPoint s x.1

theorem vieta3SurfacePerm_commute_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    vieta3SurfacePerm R * evenSignSurfacePermHom R s =
      evenSignSurfacePermHom R s * vieta3SurfacePerm R := by
  apply perm_ext_of_point_coe_eq
  intro x
  exact vieta3_evenSignPoint s x.1

theorem swap12SurfacePerm_mul_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    swap12SurfacePerm R * evenSignSurfacePermHom R s =
      evenSignSurfacePermHom R s.swap12 * swap12SurfacePerm R := by
  apply perm_ext_of_point_coe_eq
  intro x
  exact swap12_evenSignPoint s x.1

theorem swap23SurfacePerm_mul_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    swap23SurfacePerm R * evenSignSurfacePermHom R s =
      evenSignSurfacePermHom R s.swap23 * swap23SurfacePerm R := by
  apply perm_ext_of_point_coe_eq
  intro x
  exact swap23_evenSignPoint s x.1

private theorem vieta1SurfacePerm_conj_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    vieta1SurfacePerm R * evenSignSurfacePermHom R s *
        (vieta1SurfacePerm R)⁻¹ =
      evenSignSurfacePermHom R s := by
  rw [vieta1SurfacePerm_commute_evenSign]
  simp

private theorem vieta2SurfacePerm_conj_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    vieta2SurfacePerm R * evenSignSurfacePermHom R s *
        (vieta2SurfacePerm R)⁻¹ =
      evenSignSurfacePermHom R s := by
  rw [vieta2SurfacePerm_commute_evenSign]
  simp

private theorem vieta3SurfacePerm_conj_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    vieta3SurfacePerm R * evenSignSurfacePermHom R s *
        (vieta3SurfacePerm R)⁻¹ =
      evenSignSurfacePermHom R s := by
  rw [vieta3SurfacePerm_commute_evenSign]
  simp

private theorem swap12SurfacePerm_conj_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    swap12SurfacePerm R * evenSignSurfacePermHom R s *
        (swap12SurfacePerm R)⁻¹ =
      evenSignSurfacePermHom R s.swap12 := by
  rw [swap12SurfacePerm_mul_evenSign]
  simp

private theorem swap23SurfacePerm_conj_evenSign {R : Type u} [CommRing R]
    (s : EvenSign) :
    swap23SurfacePerm R * evenSignSurfacePermHom R s *
        (swap23SurfacePerm R)⁻¹ =
      evenSignSurfacePermHom R s.swap23 := by
  rw [swap23SurfacePerm_mul_evenSign]
  simp

private theorem mem_evenSign_normalizer_of_conj
    {R : Type u} [CommRing R]
    (q : Equiv.Perm (MarkoffSurface R)) (f : EvenSign → EvenSign)
    (hconj : ∀ s, q * evenSignSurfacePermHom R s * q⁻¹ =
      evenSignSurfacePermHom R (f s))
    (hsurj : Function.Surjective f) :
    q ∈ Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro r
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨f s, (hconj s).symm⟩
  · rintro ⟨s, hs⟩
    obtain ⟨t, rfl⟩ := hsurj s
    refine ⟨t, ?_⟩
    apply (MulAut.conj q).injective
    rw [MulAut.conj_apply, MulAut.conj_apply, hconj]
    exact hs

private theorem vieta1SurfacePerm_normalizes_evenSign {R : Type u} [CommRing R] :
    vieta1SurfacePerm R ∈
      Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) :=
  mem_evenSign_normalizer_of_conj (vieta1SurfacePerm R) id
    vieta1SurfacePerm_conj_evenSign Function.surjective_id

private theorem vieta2SurfacePerm_normalizes_evenSign {R : Type u} [CommRing R] :
    vieta2SurfacePerm R ∈
      Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) :=
  mem_evenSign_normalizer_of_conj (vieta2SurfacePerm R) id
    vieta2SurfacePerm_conj_evenSign Function.surjective_id

private theorem vieta3SurfacePerm_normalizes_evenSign {R : Type u} [CommRing R] :
    vieta3SurfacePerm R ∈
      Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) :=
  mem_evenSign_normalizer_of_conj (vieta3SurfacePerm R) id
    vieta3SurfacePerm_conj_evenSign Function.surjective_id

private theorem swap12SurfacePerm_normalizes_evenSign {R : Type u} [CommRing R] :
    swap12SurfacePerm R ∈
      Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) :=
  mem_evenSign_normalizer_of_conj (swap12SurfacePerm R) EvenSign.swap12
    swap12SurfacePerm_conj_evenSign
    (fun s => ⟨s.swap12, by simp⟩)

private theorem swap23SurfacePerm_normalizes_evenSign {R : Type u} [CommRing R] :
    swap23SurfacePerm R ∈
      Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) :=
  mem_evenSign_normalizer_of_conj (swap23SurfacePerm R) EvenSign.swap23
    swap23SurfacePerm_conj_evenSign
    (fun s => ⟨s.swap23, by simp⟩)

/-- Every Markoff-group element normalizes the subgroup of even sign changes. -/
theorem Gamma_le_evenSignSurfaceSubgroup_normalizer
    (R : Type u) [CommRing R] :
    Gamma R ≤ Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) := by
  change Subgroup.closure (gammaGenerators R) ≤
    Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _)
  rw [Subgroup.closure_le]
  intro q hq
  simp only [gammaGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact vieta1SurfacePerm_normalizes_evenSign
  · exact vieta2SurfacePerm_normalizes_evenSign
  · exact vieta3SurfacePerm_normalizes_evenSign
  · exact swap12SurfacePerm_normalizes_evenSign
  · exact swap23SurfacePerm_normalizes_evenSign

/-- An even sign change can be moved through an arbitrary Gamma word. -/
theorem exists_evenSign_smul_Gamma_smul
    {R : Type u} [CommRing R] (s : EvenSign) (g : Gamma R) :
    ∃ t : EvenSign, ∀ x : PuncturedMarkoffSurface R,
      s • (g • x) = g • (t • x) := by
  have hnormal :
      (g⁻¹ : Gamma R).1 ∈
        Subgroup.normalizer (evenSignSurfaceSubgroup R : Set _) :=
    Gamma_le_evenSignSurfaceSubgroup_normalizer R g⁻¹.2
  have hsign :
      (g⁻¹ : Gamma R).1 * evenSignSurfacePermHom R s * g.1 ∈
        evenSignSurfaceSubgroup R := by
    simpa using
      (Subgroup.mem_set_normalizer_iff.mp hnormal
        (evenSignSurfacePermHom R s)).1 ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := hsign
  refine ⟨t, fun x => ?_⟩
  apply Subtype.ext
  have hperm :
      evenSignSurfacePermHom R s * g.1 =
        g.1 * evenSignSurfacePermHom R t := by
    calc
      evenSignSurfacePermHom R s * g.1 =
          g.1 * ((g⁻¹ : Gamma R).1 * evenSignSurfacePermHom R s * g.1) := by
            simp [mul_assoc]
      _ = g.1 * evenSignSurfacePermHom R t := by rw [← ht]
  exact Equiv.congr_fun hperm x.1

end BGS.Markoff
