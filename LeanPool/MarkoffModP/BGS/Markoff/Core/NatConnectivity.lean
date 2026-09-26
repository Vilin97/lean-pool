/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.SemiringFunctor

/-!
# Connectivity of natural-number Markoff solutions

Every nonzero solution in natural numbers of

`x₁² + x₂² + x₃² = 3 * x₁ * x₂ * x₃`

is connected to `(1, 1, 1)` by coordinate transpositions and the natural-number Vieta moves.
The proof is the classical descent: after ordering the coordinates `a ≤ b ≤ c`, replace `c` by
`3ab - c`.  Away from `(1, 1, 1)`, this is positive and strictly smaller than `c`.

Natural subtraction is used only after proving the needed lower bound, so reduction to a ring
recovers the usual Vieta involution.
-/

@[expose] public section

namespace BGS.Markoff

/-- The first Vieta replacement on points with natural-number coordinates. -/
def natVieta1 (x : Point ℕ) : Point ℕ :=
  ⟨3 * x.x2 * x.x3 - x.x1, x.x2, x.x3⟩

/-- The second Vieta replacement on points with natural-number coordinates. -/
def natVieta2 (x : Point ℕ) : Point ℕ :=
  ⟨x.x1, 3 * x.x1 * x.x3 - x.x2, x.x3⟩

/-- The third Vieta replacement on points with natural-number coordinates. -/
def natVieta3 (x : Point ℕ) : Point ℕ :=
  ⟨x.x1, x.x2, 3 * x.x1 * x.x2 - x.x3⟩

private theorem coordinate_le_vietaProduct {a b c : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c) :
    a ≤ 3 * b * c := by
  by_cases ha : a = 0
  · simp [ha]
  have haPos : 0 < a := Nat.pos_of_ne_zero ha
  apply Nat.le_of_mul_le_mul_left _ haPos
  calc
    a * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by nlinarith
    _ = 3 * a * b * c := h
    _ = a * (3 * b * c) := by ring

private theorem vietaReplacement_preserves {a b c : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c) :
    (3 * b * c - a) ^ 2 + b ^ 2 + c ^ 2 =
      3 * (3 * b * c - a) * b * c := by
  have hle : a ≤ 3 * b * c := coordinate_le_vietaProduct h
  have hcast : ((3 * b * c - a : ℕ) : ℤ) = 3 * b * c - a := by
    rw [Nat.cast_sub hle]
    norm_num
  have hz : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 =
      3 * a * b * c := by
    exact_mod_cast h
  apply_mod_cast (show ((3 * b * c - a : ℕ) : ℤ) ^ 2 + (b : ℤ) ^ 2 +
      (c : ℤ) ^ 2 = 3 * ((3 * b * c - a : ℕ) : ℤ) * b * c by
    rw [hcast]
    nlinarith)

theorem isSemiringMarkoff_natVieta1 (x : Point ℕ) (hx : IsSemiringMarkoff x) :
    IsSemiringMarkoff (natVieta1 x) := by
  exact vietaReplacement_preserves (by simpa [IsSemiringMarkoff] using hx)

theorem isSemiringMarkoff_natVieta2 (x : Point ℕ) (hx : IsSemiringMarkoff x) :
    IsSemiringMarkoff (natVieta2 x) := by
  have hreorder : IsSemiringMarkoff x ↔
      x.x2 ^ 2 + x.x1 ^ 2 + x.x3 ^ 2 = 3 * x.x2 * x.x1 * x.x3 := by
    simp only [IsSemiringMarkoff]
    ring_nf
  have hp := vietaReplacement_preserves (a := x.x2) (b := x.x1) (c := x.x3)
    (hreorder.mp hx)
  simpa [IsSemiringMarkoff, natVieta2, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hp

theorem isSemiringMarkoff_natVieta3 (x : Point ℕ) (hx : IsSemiringMarkoff x) :
    IsSemiringMarkoff (natVieta3 x) := by
  have hreorder : IsSemiringMarkoff x ↔
      x.x3 ^ 2 + x.x1 ^ 2 + x.x2 ^ 2 = 3 * x.x3 * x.x1 * x.x2 := by
    simp only [IsSemiringMarkoff]
    ring_nf
  have hp := vietaReplacement_preserves (a := x.x3) (b := x.x1) (c := x.x2)
    (hreorder.mp hx)
  simpa [IsSemiringMarkoff, natVieta3, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hp

/-- The first natural-number Vieta move restricted to the Markoff surface. -/
def natVieta1Surface (x : SemiringMarkoffSurface ℕ) : SemiringMarkoffSurface ℕ :=
  ⟨natVieta1 x.1, isSemiringMarkoff_natVieta1 x.1 x.2⟩

/-- The second natural-number Vieta move restricted to the Markoff surface. -/
def natVieta2Surface (x : SemiringMarkoffSurface ℕ) : SemiringMarkoffSurface ℕ :=
  ⟨natVieta2 x.1, isSemiringMarkoff_natVieta2 x.1 x.2⟩

/-- The third natural-number Vieta move restricted to the Markoff surface. -/
def natVieta3Surface (x : SemiringMarkoffSurface ℕ) : SemiringMarkoffSurface ℕ :=
  ⟨natVieta3 x.1, isSemiringMarkoff_natVieta3 x.1 x.2⟩

/-- Exchange the first two coordinates of a natural-number Markoff solution. -/
def natSwap12Surface (x : SemiringMarkoffSurface ℕ) : SemiringMarkoffSurface ℕ :=
  ⟨swap12 x.1, by
    simpa [IsSemiringMarkoff, swap12, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using x.2⟩

/-- Exchange the last two coordinates of a natural-number Markoff solution. -/
def natSwap23Surface (x : SemiringMarkoffSurface ℕ) : SemiringMarkoffSurface ℕ :=
  ⟨swap23 x.1, by
    simpa [IsSemiringMarkoff, swap23, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using x.2⟩

@[simp] theorem natVieta1Surface_coe (x : SemiringMarkoffSurface ℕ) :
    (natVieta1Surface x).1 = natVieta1 x.1 := rfl

@[simp] theorem natVieta2Surface_coe (x : SemiringMarkoffSurface ℕ) :
    (natVieta2Surface x).1 = natVieta2 x.1 := rfl

@[simp] theorem natVieta3Surface_coe (x : SemiringMarkoffSurface ℕ) :
    (natVieta3Surface x).1 = natVieta3 x.1 := rfl

@[simp] theorem natSwap12Surface_coe (x : SemiringMarkoffSurface ℕ) :
    (natSwap12Surface x).1 = swap12 x.1 := rfl

@[simp] theorem natSwap23Surface_coe (x : SemiringMarkoffSurface ℕ) :
    (natSwap23Surface x).1 = swap23 x.1 := rfl

@[simp]
theorem natVieta1Surface_involutive (x : SemiringMarkoffSurface ℕ) :
    natVieta1Surface (natVieta1Surface x) = x := by
  have hle : x.1.x1 ≤ 3 * x.1.x2 * x.1.x3 :=
    coordinate_le_vietaProduct x.2
  apply Subtype.ext
  ext <;> simp [natVieta1Surface, natVieta1, Nat.sub_sub_self hle]

@[simp]
theorem natVieta2Surface_involutive (x : SemiringMarkoffSurface ℕ) :
    natVieta2Surface (natVieta2Surface x) = x := by
  have hreorder : x.1.x2 ^ 2 + x.1.x1 ^ 2 + x.1.x3 ^ 2 =
      3 * x.1.x2 * x.1.x1 * x.1.x3 := by
    simpa [IsSemiringMarkoff, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using x.2
  have hle : x.1.x2 ≤ 3 * x.1.x1 * x.1.x3 :=
    coordinate_le_vietaProduct hreorder
  apply Subtype.ext
  ext <;> simp [natVieta2Surface, natVieta2, Nat.sub_sub_self hle]

@[simp]
theorem natVieta3Surface_involutive (x : SemiringMarkoffSurface ℕ) :
    natVieta3Surface (natVieta3Surface x) = x := by
  have hreorder : x.1.x3 ^ 2 + x.1.x1 ^ 2 + x.1.x2 ^ 2 =
      3 * x.1.x3 * x.1.x1 * x.1.x2 := by
    simpa [IsSemiringMarkoff, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using x.2
  have hle : x.1.x3 ≤ 3 * x.1.x1 * x.1.x2 :=
    coordinate_le_vietaProduct hreorder
  apply Subtype.ext
  ext <;> simp [natVieta3Surface, natVieta3, Nat.sub_sub_self hle]

@[simp]
theorem natSwap12Surface_involutive (x : SemiringMarkoffSurface ℕ) :
    natSwap12Surface (natSwap12Surface x) = x := by
  apply Subtype.ext
  rfl

@[simp]
theorem natSwap23Surface_involutive (x : SemiringMarkoffSurface ℕ) :
    natSwap23Surface (natSwap23Surface x) = x := by
  apply Subtype.ext
  rfl

/-- The first natural Vieta move as a permutation of the natural Markoff surface. -/
def natVieta1SurfaceEquiv : Equiv.Perm (SemiringMarkoffSurface ℕ) where
  toFun := natVieta1Surface
  invFun := natVieta1Surface
  left_inv := natVieta1Surface_involutive
  right_inv := natVieta1Surface_involutive

/-- The second natural Vieta move as a permutation of the natural Markoff surface. -/
def natVieta2SurfaceEquiv : Equiv.Perm (SemiringMarkoffSurface ℕ) where
  toFun := natVieta2Surface
  invFun := natVieta2Surface
  left_inv := natVieta2Surface_involutive
  right_inv := natVieta2Surface_involutive

/-- The third natural Vieta move as a permutation of the natural Markoff surface. -/
def natVieta3SurfaceEquiv : Equiv.Perm (SemiringMarkoffSurface ℕ) where
  toFun := natVieta3Surface
  invFun := natVieta3Surface
  left_inv := natVieta3Surface_involutive
  right_inv := natVieta3Surface_involutive

/-- The first coordinate transposition as a permutation of the natural Markoff surface. -/
def natSwap12SurfaceEquiv : Equiv.Perm (SemiringMarkoffSurface ℕ) where
  toFun := natSwap12Surface
  invFun := natSwap12Surface
  left_inv := natSwap12Surface_involutive
  right_inv := natSwap12Surface_involutive

/-- The second coordinate transposition as a permutation of the natural Markoff surface. -/
def natSwap23SurfaceEquiv : Equiv.Perm (SemiringMarkoffSurface ℕ) where
  toFun := natSwap23Surface
  invFun := natSwap23Surface
  left_inv := natSwap23Surface_involutive
  right_inv := natSwap23Surface_involutive

/-- The five standard generators acting on natural-number Markoff solutions. -/
def naturalGammaGenerators : Set (Equiv.Perm (SemiringMarkoffSurface ℕ)) :=
  {natVieta1SurfaceEquiv, natVieta2SurfaceEquiv, natVieta3SurfaceEquiv,
    natSwap12SurfaceEquiv, natSwap23SurfaceEquiv}

/-- The group generated by natural Vieta moves and coordinate transpositions. -/
def NaturalGamma : Subgroup (Equiv.Perm (SemiringMarkoffSurface ℕ)) :=
  Subgroup.closure naturalGammaGenerators

theorem natVieta1SurfaceEquiv_mem_NaturalGamma : natVieta1SurfaceEquiv ∈ NaturalGamma :=
  Subgroup.subset_closure (by simp [naturalGammaGenerators])

theorem natVieta2SurfaceEquiv_mem_NaturalGamma : natVieta2SurfaceEquiv ∈ NaturalGamma :=
  Subgroup.subset_closure (by simp [naturalGammaGenerators])

theorem natVieta3SurfaceEquiv_mem_NaturalGamma : natVieta3SurfaceEquiv ∈ NaturalGamma :=
  Subgroup.subset_closure (by simp [naturalGammaGenerators])

theorem natSwap12SurfaceEquiv_mem_NaturalGamma : natSwap12SurfaceEquiv ∈ NaturalGamma :=
  Subgroup.subset_closure (by simp [naturalGammaGenerators])

theorem natSwap23SurfaceEquiv_mem_NaturalGamma : natSwap23SurfaceEquiv ∈ NaturalGamma :=
  Subgroup.subset_closure (by simp [naturalGammaGenerators])

/-- The orbit relation for the natural Markoff group. -/
def SameNatMarkoffComponent (x y : SemiringMarkoffSurface ℕ) : Prop :=
  y ∈ MulAction.orbit NaturalGamma x

theorem sameNatMarkoffComponent_iff_exists (x y : SemiringMarkoffSurface ℕ) :
    SameNatMarkoffComponent x y ↔ ∃ g : NaturalGamma, g • x = y :=
  Iff.rfl

/-- A single standard move between natural-number Markoff solutions. -/
inductive NatMarkoffStep : SemiringMarkoffSurface ℕ → SemiringMarkoffSurface ℕ → Prop
  | vieta1 (x) : NatMarkoffStep x (natVieta1Surface x)
  | vieta2 (x) : NatMarkoffStep x (natVieta2Surface x)
  | vieta3 (x) : NatMarkoffStep x (natVieta3Surface x)
  | swap12 (x) : NatMarkoffStep x (natSwap12Surface x)
  | swap23 (x) : NatMarkoffStep x (natSwap23Surface x)

@[refl] theorem sameNatMarkoffComponent_refl (x : SemiringMarkoffSurface ℕ) :
    SameNatMarkoffComponent x x :=
  MulAction.mem_orbit_self x

@[symm] theorem sameNatMarkoffComponent_symm {x y : SemiringMarkoffSurface ℕ}
    (h : SameNatMarkoffComponent x y) : SameNatMarkoffComponent y x :=
  MulAction.mem_orbit_symm.mp h

@[trans] theorem sameNatMarkoffComponent_trans {x y z : SemiringMarkoffSurface ℕ}
    (hxy : SameNatMarkoffComponent x y) (hyz : SameNatMarkoffComponent y z) :
    SameNatMarkoffComponent x z := by
  unfold SameNatMarkoffComponent at *
  rwa [(MulAction.orbit_eq_iff).2 hxy] at hyz

theorem sameNatMarkoffComponent_vieta1 (x : SemiringMarkoffSurface ℕ) :
    SameNatMarkoffComponent x (natVieta1Surface x) := by
  exact ⟨⟨natVieta1SurfaceEquiv, natVieta1SurfaceEquiv_mem_NaturalGamma⟩, rfl⟩

theorem sameNatMarkoffComponent_vieta2 (x : SemiringMarkoffSurface ℕ) :
    SameNatMarkoffComponent x (natVieta2Surface x) := by
  exact ⟨⟨natVieta2SurfaceEquiv, natVieta2SurfaceEquiv_mem_NaturalGamma⟩, rfl⟩

theorem sameNatMarkoffComponent_vieta3 (x : SemiringMarkoffSurface ℕ) :
    SameNatMarkoffComponent x (natVieta3Surface x) := by
  exact ⟨⟨natVieta3SurfaceEquiv, natVieta3SurfaceEquiv_mem_NaturalGamma⟩, rfl⟩

theorem sameNatMarkoffComponent_swap12 (x : SemiringMarkoffSurface ℕ) :
    SameNatMarkoffComponent x (natSwap12Surface x) := by
  exact ⟨⟨natSwap12SurfaceEquiv, natSwap12SurfaceEquiv_mem_NaturalGamma⟩, rfl⟩

theorem sameNatMarkoffComponent_swap23 (x : SemiringMarkoffSurface ℕ) :
    SameNatMarkoffComponent x (natSwap23Surface x) := by
  exact ⟨⟨natSwap23SurfaceEquiv, natSwap23SurfaceEquiv_mem_NaturalGamma⟩, rfl⟩

/-- A generated sequence of standard natural moves lies in a single `NaturalGamma` orbit. -/
theorem eqvGen_natMarkoffStep_sameComponent {x y : SemiringMarkoffSurface ℕ}
    (h : Relation.EqvGen NatMarkoffStep x y) : SameNatMarkoffComponent x y := by
  induction h with
  | rel x y hxy =>
      cases hxy with
      | vieta1 => exact sameNatMarkoffComponent_vieta1 x
      | vieta2 => exact sameNatMarkoffComponent_vieta2 x
      | vieta3 => exact sameNatMarkoffComponent_vieta3 x
      | swap12 => exact sameNatMarkoffComponent_swap12 x
      | swap23 => exact sameNatMarkoffComponent_swap23 x
  | refl x => exact sameNatMarkoffComponent_refl x
  | symm x y _ ih => exact sameNatMarkoffComponent_symm ih
  | trans x y z _ _ ihxy ihyz => exact sameNatMarkoffComponent_trans ihxy ihyz

/-- Sum of the coordinates, used as the well-founded descent measure. -/
def natMarkoffHeight (x : SemiringMarkoffSurface ℕ) : ℕ :=
  x.1.x1 + x.1.x2 + x.1.x3

private theorem ordered_descending_vieta {a b c : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c)
    (hnotRoot : ¬(a = 1 ∧ b = 1 ∧ c = 1)) :
    0 < 3 * a * b - c ∧ 3 * a * b - c < c := by
  have hc_le : c ≤ 3 * a * b := by
    have hcPos : 0 < c := lt_of_lt_of_le ha (hab.trans hbc)
    apply Nat.le_of_mul_le_mul_left _ hcPos
    calc
      c * c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by nlinarith
      _ = 3 * a * b * c := h
      _ = c * (3 * a * b) := by ring
  have hc_lt : c < 3 * a * b := by
    have hcPos : 0 < c := lt_of_lt_of_le ha (hab.trans hbc)
    apply Nat.lt_of_mul_lt_mul_left
    calc
      c * c < a ^ 2 + b ^ 2 + c ^ 2 := by nlinarith [sq_pos_of_pos ha]
      _ = 3 * a * b * c := h
      _ = c * (3 * a * b) := by ring
  have hb_lt : b < c := by
    apply lt_of_le_of_ne hbc
    intro hne
    subst c
    have haSqLe : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
    have haOne : a = 1 := by
      by_contra haNe
      have haTwo : 2 ≤ a := by omega
      have hmul : 2 * b ^ 2 ≤ a * b ^ 2 :=
        Nat.mul_le_mul_right (b ^ 2) haTwo
      have hbPos : 0 < b := lt_of_lt_of_le ha hab
      nlinarith [sq_pos_of_pos hbPos]
    have hbOne : b = 1 := by
      subst a
      nlinarith
    exact hnotRoot ⟨haOne, hbOne, hbOne⟩
  have haSqLe : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  have hbSqLe : b ^ 2 ≤ a * b ^ 2 := by
    calc
      b ^ 2 = 1 * b ^ 2 := by simp
      _ ≤ a * b ^ 2 := Nat.mul_le_mul_right (b ^ 2) ha
  have hf : a ^ 2 + 2 * b ^ 2 ≤ 3 * a * b ^ 2 := by
    nlinarith
  have hsum : 3 * a * b ≤ b + c := by
    by_contra hnot
    have hstrict : b + c < 3 * a * b := Nat.lt_of_not_ge hnot
    have hEqZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 =
        3 * a * b * c := by
      exact_mod_cast h
    have hfZ : (a : ℤ) ^ 2 + 2 * (b : ℤ) ^ 2 ≤ 3 * a * b ^ 2 := by
      exact_mod_cast hf
    have hbLtZ : (b : ℤ) < c := by exact_mod_cast hb_lt
    have hstrictZ : (b : ℤ) + c < 3 * a * b := by exact_mod_cast hstrict
    have hprod : 0 < ((c : ℤ) - b) * (3 * a * b - b - c) :=
      mul_pos (sub_pos.mpr hbLtZ) (by omega)
    nlinarith
  exact ⟨Nat.sub_pos_of_lt hc_lt, by omega⟩

theorem natMarkoff_eq_origin_of_x1_eq_zero (x : SemiringMarkoffSurface ℕ)
    (hx1 : x.1.x1 = 0) : x = semiringSurfaceOrigin ℕ := by
  have heq := x.2
  change x.1.x1 ^ 2 + x.1.x2 ^ 2 + x.1.x3 ^ 2 =
    3 * x.1.x1 * x.1.x2 * x.1.x3 at heq
  have hsum : x.1.x2 ^ 2 + x.1.x3 ^ 2 = 0 := by simpa [hx1] using heq
  have hx2 : x.1.x2 = 0 := by nlinarith [hsum]
  have hx3 : x.1.x3 = 0 := by nlinarith [hsum]
  apply Subtype.ext
  ext <;> simp [semiringSurfaceOrigin, origin, hx1, hx2, hx3]

theorem natMarkoff_eq_origin_of_x2_eq_zero (x : SemiringMarkoffSurface ℕ)
    (hx2 : x.1.x2 = 0) : x = semiringSurfaceOrigin ℕ := by
  have heq := x.2
  change x.1.x1 ^ 2 + x.1.x2 ^ 2 + x.1.x3 ^ 2 =
    3 * x.1.x1 * x.1.x2 * x.1.x3 at heq
  have hsum : x.1.x1 ^ 2 + x.1.x3 ^ 2 = 0 := by simpa [hx2] using heq
  have hx1 : x.1.x1 = 0 := by nlinarith [hsum]
  exact natMarkoff_eq_origin_of_x1_eq_zero x hx1

theorem natMarkoff_eq_origin_of_x3_eq_zero (x : SemiringMarkoffSurface ℕ)
    (hx3 : x.1.x3 = 0) : x = semiringSurfaceOrigin ℕ := by
  have heq := x.2
  change x.1.x1 ^ 2 + x.1.x2 ^ 2 + x.1.x3 ^ 2 =
    3 * x.1.x1 * x.1.x2 * x.1.x3 at heq
  have hsum : x.1.x1 ^ 2 + x.1.x2 ^ 2 = 0 := by simpa [hx3] using heq
  have hx1 : x.1.x1 = 0 := by nlinarith [hsum]
  exact natMarkoff_eq_origin_of_x1_eq_zero x hx1

/-- Every coordinate of a nonzero natural Markoff solution is positive. -/
theorem natMarkoff_coordinates_pos_of_ne_origin (x : SemiringMarkoffSurface ℕ)
    (hx : x ≠ semiringSurfaceOrigin ℕ) :
    0 < x.1.x1 ∧ 0 < x.1.x2 ∧ 0 < x.1.x3 := by
  refine ⟨Nat.pos_of_ne_zero fun h => hx (natMarkoff_eq_origin_of_x1_eq_zero x h),
    Nat.pos_of_ne_zero fun h => hx (natMarkoff_eq_origin_of_x2_eq_zero x h),
    Nat.pos_of_ne_zero fun h => hx (natMarkoff_eq_origin_of_x3_eq_zero x h)⟩

private theorem natMarkoff_eq_root_of_coordinates_eq_one
    (x : SemiringMarkoffSurface ℕ) (hx1 : x.1.x1 = 1)
    (hx2 : x.1.x2 = 1) (hx3 : x.1.x3 = 1) :
    x = semiringSurfaceRoot ℕ := by
  apply Subtype.ext
  ext <;> simp [semiringSurfaceRoot, hx1, hx2, hx3]

private theorem exists_ordered_sameNatMarkoffComponent (x : SemiringMarkoffSurface ℕ) :
    ∃ y : SemiringMarkoffSurface ℕ,
      SameNatMarkoffComponent x y ∧
      y.1.x1 ≤ y.1.x2 ∧ y.1.x2 ≤ y.1.x3 ∧
      natMarkoffHeight y = natMarkoffHeight x := by
  by_cases h12 : x.1.x1 ≤ x.1.x2
  · by_cases h23 : x.1.x2 ≤ x.1.x3
    · exact ⟨x, sameNatMarkoffComponent_refl x, h12, h23, rfl⟩
    · have h32 : x.1.x3 < x.1.x2 := Nat.lt_of_not_ge h23
      by_cases h13 : x.1.x1 ≤ x.1.x3
      · refine ⟨natSwap23Surface x, sameNatMarkoffComponent_swap23 x, ?_, ?_, ?_⟩
        · exact h13
        · exact h32.le
        · simp [natMarkoffHeight, natSwap23Surface, swap23]
          omega
      · have h31 : x.1.x3 < x.1.x1 := Nat.lt_of_not_ge h13
        let y := natSwap12Surface (natSwap23Surface x)
        have hxy : SameNatMarkoffComponent x y :=
          sameNatMarkoffComponent_trans (sameNatMarkoffComponent_swap23 x)
            (sameNatMarkoffComponent_swap12 (natSwap23Surface x))
        refine ⟨y, hxy, ?_, ?_, ?_⟩
        · exact h31.le
        · exact h12
        · simp [y, natMarkoffHeight, natSwap12Surface, natSwap23Surface, swap12, swap23]
          omega
  · have h21 : x.1.x2 < x.1.x1 := Nat.lt_of_not_ge h12
    by_cases h13 : x.1.x1 ≤ x.1.x3
    · refine ⟨natSwap12Surface x, sameNatMarkoffComponent_swap12 x, ?_, ?_, ?_⟩
      · exact h21.le
      · exact h13
      · simp [natMarkoffHeight, natSwap12Surface, swap12]
        omega
    · have h31 : x.1.x3 < x.1.x1 := Nat.lt_of_not_ge h13
      by_cases h23 : x.1.x2 ≤ x.1.x3
      · let y := natSwap23Surface (natSwap12Surface x)
        have hxy : SameNatMarkoffComponent x y :=
          sameNatMarkoffComponent_trans (sameNatMarkoffComponent_swap12 x)
            (sameNatMarkoffComponent_swap23 (natSwap12Surface x))
        refine ⟨y, hxy, ?_, ?_, ?_⟩
        · exact h23
        · exact h31.le
        · simp [y, natMarkoffHeight, natSwap12Surface, natSwap23Surface, swap12, swap23]
          omega
      · have h32 : x.1.x3 < x.1.x2 := Nat.lt_of_not_ge h23
        let y := natSwap12Surface (natSwap23Surface (natSwap12Surface x))
        have hxy : SameNatMarkoffComponent x y :=
          sameNatMarkoffComponent_trans (sameNatMarkoffComponent_swap12 x) <|
            sameNatMarkoffComponent_trans
              (sameNatMarkoffComponent_swap23 (natSwap12Surface x))
              (sameNatMarkoffComponent_swap12 (natSwap23Surface (natSwap12Surface x)))
        refine ⟨y, hxy, ?_, ?_, ?_⟩
        · exact h32.le
        · exact h21.le
        · simp [y, natMarkoffHeight, natSwap12Surface, natSwap23Surface, swap12, swap23]
          omega

/-- Every nonzero natural-number Markoff solution is in the `NaturalGamma` orbit of `(1,1,1)`. -/
theorem natMarkoff_ne_origin_sameComponent_root :
    ∀ x : SemiringMarkoffSurface ℕ,
      x ≠ semiringSurfaceOrigin ℕ →
        SameNatMarkoffComponent (semiringSurfaceRoot ℕ) x := by
  intro x
  induction x using (measure natMarkoffHeight).wf.induction with
  | h x ih =>
      intro hx
      obtain ⟨y, hxy, hy12, hy23, hyHeight⟩ :=
        exists_ordered_sameNatMarkoffComponent x
      have hxPos := natMarkoff_coordinates_pos_of_ne_origin x hx
      have hxHeightPos : 0 < natMarkoffHeight x := by
        simp only [natMarkoffHeight]
        omega
      have hyHeightPos : 0 < natMarkoffHeight y := by omega
      have hy : y ≠ semiringSurfaceOrigin ℕ := by
        intro hyOrigin
        subst y
        simp [natMarkoffHeight, semiringSurfaceOrigin, origin] at hyHeightPos
      have hyPos := natMarkoff_coordinates_pos_of_ne_origin y hy
      by_cases hyRoot : y = semiringSurfaceRoot ℕ
      · exact sameNatMarkoffComponent_symm (hyRoot ▸ hxy)
      · have hnotRootCoords :
            ¬(y.1.x1 = 1 ∧ y.1.x2 = 1 ∧ y.1.x3 = 1) := by
          rintro ⟨hy1, hy2, hy3⟩
          exact hyRoot (natMarkoff_eq_root_of_coordinates_eq_one y hy1 hy2 hy3)
        have hdesc := ordered_descending_vieta hyPos.1 hy12 hy23 y.2 hnotRootCoords
        let z := natVieta3Surface y
        have hzHeight : natMarkoffHeight z < natMarkoffHeight x := by
          rw [← hyHeight]
          simp only [z, natMarkoffHeight, natVieta3Surface, natVieta3]
          omega
        have hz : z ≠ semiringSurfaceOrigin ℕ := by
          intro hzOrigin
          have hz1 : z.1.x1 = 0 := by
            rw [hzOrigin]
            rfl
          change y.1.x1 = 0 at hz1
          omega
        have hRootZ : SameNatMarkoffComponent (semiringSurfaceRoot ℕ) z :=
          ih z hzHeight hz
        have hzy : SameNatMarkoffComponent z y :=
          sameNatMarkoffComponent_symm (sameNatMarkoffComponent_vieta3 y)
        exact sameNatMarkoffComponent_trans
          (sameNatMarkoffComponent_trans hRootZ hzy)
          (sameNatMarkoffComponent_symm hxy)

/-- The natural Markoff surface consists of the origin and the single orbit rooted at `(1,1,1)`. -/
theorem natMarkoff_eq_origin_or_sameComponent_root (x : SemiringMarkoffSurface ℕ) :
    x = semiringSurfaceOrigin ℕ ∨
      SameNatMarkoffComponent (semiringSurfaceRoot ℕ) x := by
  by_cases hx : x = semiringSurfaceOrigin ℕ
  · exact Or.inl hx
  · exact Or.inr (natMarkoff_ne_origin_sameComponent_root x hx)

end BGS.Markoff
