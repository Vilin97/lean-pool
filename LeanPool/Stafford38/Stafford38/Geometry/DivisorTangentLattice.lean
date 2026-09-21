/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib

/-!
# The divisor-tangent lattice lemma

Let `V` be a local ring inside a field `F`, `t` an element of its maximal
ideal, and `d` a derivation of `F` with values in an `F`-vector space `Ω`.
Suppose the homogeneous coordinates `Q₀, Q₁, Q j` lie in `V` with

```text
Q₀ = t^a * u,   Q₁ = t^(a+e) * w,   Q j₀ = 1,   a, e ≥ 1,   u a unit.
```

The affine coordinates are `x j = Q j / Q₀` and `x₁ = Q₁ / Q₀`.  Let `W` be
a finitely generated `V`-lattice in `Ω` containing `d t`, `d u`, `d w` and
the `d (Q j)`; in the geometric application `W` is the image of `Ω_{V/k}`.
The *visibility* hypothesis asks that `W` is spanned modulo `t W` by `d t`
and the `d (Q j)`.  Under it,
the differential `d x₁` is a combination of the `d (x j)` with coefficients
in the maximal ideal of `V`:

```text
d x₁ = ∑ j, c j • d (x j),      c j ∈ m_V.
```

This is the algebraic content of the asymptotic-conormal lemma: after
completing `V` the covector `e₁ - ∑ c j e_j` has residue exactly the first
axis, and it annihilates every tangent vector at the generic point because
the identity holds in the module of differentials.  The proof is Nakayama's
lemma applied to the lattice spanned by the scaled differentials
`t^(a+1) u^2 • d (x j)`.

No geometry enters here: the visibility hypothesis is an explicit statement
about the derivation restricted to `V`, and producing a place that satisfies
it is the remaining geometric input of lane C.
-/

namespace Stafford38.Geometry.DivisorTangentLattice

open IsLocalRing

noncomputable section

universe u v w x y

variable {k : Type u} {V : Type v} {F : Type w} {Ω : Type x}
variable [CommRing k] [CommRing V] [IsLocalRing V] [Field F]
variable [Algebra k F] [Algebra V F]
variable [AddCommGroup Ω] [Module k Ω] [Module F Ω] [Module V Ω]
variable [IsScalarTower V F Ω]

variable (d : Derivation k F Ω)
variable {ι : Type y} [Fintype ι]


/-- The `V`-lattice spanned by `d t` and the differentials of the
homogeneous coordinates. -/
def coordinateFrame (t : V) (Q : ι → V) : Submodule V Ω :=
  Submodule.span V {d (algebraMap V F t)} ⊔
    Submodule.span V (Set.range fun j ↦ d (algebraMap V F (Q j)))

theorem dQ_mem_coordinateFrame (t : V) (Q : ι → V) (j : ι) :
    d (algebraMap V F (Q j)) ∈ coordinateFrame d t Q :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)

/-- Normalized divisor-frame data for the lattice lemma.  All coordinates
are elements of `V`.  The lattice `W` is any finitely generated `V`-submodule
containing the differentials of `t`, `u`, `w` and the `Q j`; in the geometric
application it is the image of `Ω_{V/k}`.  The visibility field is the only
non-algebraic hypothesis: modulo `t`, the lattice `W` is spanned by `d t` and
the `d (Q j)`. -/
structure VisibleDivisorFrame (d : Derivation k F Ω) (ι : Type y) [Fintype ι] where
  Q₀ : V
  Q₁ : V
  t : V
  u : V
  w : V
  Q : ι → V
  a : ℕ
  e : ℕ
  j₀ : ι
  W : Submodule V Ω
  t_mem : t ∈ maximalIdeal V
  t_ne : t ≠ 0
  u_unit : IsUnit u
  a_unit : IsUnit (a : V)
  one_le_a : 1 ≤ a
  one_le_e : 1 ≤ e
  Q₀_eq : Q₀ = t ^ a * u
  Q₁_eq : Q₁ = t ^ (a + e) * w
  Q_j₀ : Q j₀ = 1
  W_fg : W.FG
  dt_mem : d (algebraMap V F t) ∈ W
  du_mem : d (algebraMap V F u) ∈ W
  dw_mem : d (algebraMap V F w) ∈ W
  dQ_mem : ∀ j, d (algebraMap V F (Q j)) ∈ W
  visible : W ≤ coordinateFrame d t Q ⊔ Ideal.span {t} • W

namespace VisibleDivisorFrame

variable {d}
variable (D : VisibleDivisorFrame (V := V) d ι)

/-- The scaled differential of the affine coordinate with numerator `P`. -/
def scaledDifferential (P : V) : Ω :=
  (algebraMap V F D.t ^ (D.a + 1) * algebraMap V F D.u ^ 2) •
    d (algebraMap V F P / algebraMap V F D.Q₀)

theorem algebraMap_t_ne_zero (hinj : Function.Injective (algebraMap V F)) :
    algebraMap V F D.t ≠ 0 :=
  (map_ne_zero_iff _ hinj).2 D.t_ne

theorem algebraMap_u_ne_zero : algebraMap V F D.u ≠ 0 :=
  (D.u_unit.map (algebraMap V F)).ne_zero

theorem scale_ne_zero (hinj : Function.Injective (algebraMap V F)) :
    algebraMap V F D.t ^ (D.a + 1) * algebraMap V F D.u ^ 2 ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (D.algebraMap_t_ne_zero hinj))
    (pow_ne_zero _ D.algebraMap_u_ne_zero)

/-- The scaled affine differential in terms of differentials of elements of
`V`.  This is the only place where the quotient rule is used. -/
theorem scaledDifferential_eq (hinj : Function.Injective (algebraMap V F))
    (P : V) :
    D.scaledDifferential P =
      (D.u * D.t) • d (algebraMap V F P) -
        ((D.a : V) * P * D.u) • d (algebraMap V F D.t) -
        (D.t * P) • d (algebraMap V F D.u) := by
  obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le' D.one_le_a
  have hT := D.algebraMap_t_ne_zero hinj
  have hU := D.algebraMap_u_ne_zero
  unfold scaledDifferential
  rw [Derivation.leibniz_div, D.Q₀_eq, map_mul, map_pow, Derivation.leibniz,
    Derivation.leibniz_pow]
  simp only [← algebraMap_smul (R := V) (A := F) (M := Ω), map_mul, map_natCast,
    ha', Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul F]
  simp only [smul_sub, smul_add, smul_smul]
  rw [sub_sub]
  congr 1
  · congr 1
    field_simp
    ring
  · rw [add_comm]
    congr 1
    · congr 1
      field_simp
      ring
    · congr 1
      field_simp
      ring

/-- The lattice spanned by the scaled affine differentials of the
coordinates `Q j`. -/
def scaledLattice : Submodule V Ω :=
  Submodule.span V (Set.range fun j ↦ D.scaledDifferential (D.Q j))

theorem scaledDifferential_mem_scaledLattice (j : ι) :
    D.scaledDifferential (D.Q j) ∈ D.scaledLattice :=
  Submodule.subset_span ⟨j, rfl⟩

theorem scaledDifferential_j₀ (hinj : Function.Injective (algebraMap V F)) :
    D.scaledDifferential (D.Q D.j₀) =
      -(((D.a : V) * D.u) • d (algebraMap V F D.t)) -
        D.t • d (algebraMap V F D.u) := by
  rw [D.scaledDifferential_eq hinj, D.Q_j₀, map_one, Derivation.map_one_eq_zero,
    smul_zero, zero_sub, mul_one, mul_one]

/-- Step (i): `t • d (Q j)` lies in the scaled lattice. -/
theorem t_smul_dQ_mem_scaledLattice (hinj : Function.Injective (algebraMap V F))
    (j : ι) :
    D.t • d (algebraMap V F (D.Q j)) ∈ D.scaledLattice := by
  have hid : (D.u * D.t) • d (algebraMap V F (D.Q j)) =
      D.scaledDifferential (D.Q j) - D.Q j • D.scaledDifferential (D.Q D.j₀) := by
    rw [D.scaledDifferential_eq hinj, D.scaledDifferential_j₀ hinj]
    module
  have hmem : (D.u * D.t) • d (algebraMap V F (D.Q j)) ∈ D.scaledLattice := by
    rw [hid]
    exact Submodule.sub_mem _ (D.scaledDifferential_mem_scaledLattice j)
      (Submodule.smul_mem _ _ (D.scaledDifferential_mem_scaledLattice D.j₀))
  have hinv : D.t • d (algebraMap V F (D.Q j)) =
      (↑D.u_unit.unit⁻¹ : V) • ((D.u * D.t) • d (algebraMap V F (D.Q j))) := by
    rw [smul_smul, ← mul_assoc, Units.inv_mul_of_eq D.u_unit.unit_spec, one_mul]
  rw [hinv]
  exact Submodule.smul_mem _ _ hmem

/-- The ideal generated by the uniformizer. -/
def parameterIdeal : Ideal V := Ideal.span {D.t}

theorem t_mem_parameterIdeal : D.t ∈ D.parameterIdeal :=
  Ideal.mem_span_singleton_self _

theorem parameterIdeal_le_jacobson : D.parameterIdeal ≤ (⊥ : Ideal V).jacobson :=
  (Ideal.span_le.2 (Set.singleton_subset_iff.2 D.t_mem)).trans
    (maximalIdeal_le_jacobson _)

theorem parameterIdeal_fg : D.parameterIdeal.FG :=
  Submodule.fg_span_singleton _

/-- Step (ii): `t • d t` lies in the scaled lattice up to `t²` times the
lattice `W`. -/
theorem t_smul_dt_mem (hinj : Function.Injective (algebraMap V F)) :
    D.t • d (algebraMap V F D.t) ∈
      D.scaledLattice ⊔
        D.parameterIdeal • (D.parameterIdeal • D.W) := by
  have hid : ((D.a : V) * D.u) • (D.t • d (algebraMap V F D.t)) =
      -(D.t • D.scaledDifferential (D.Q D.j₀)) -
        D.t • (D.t • d (algebraMap V F D.u)) := by
    rw [D.scaledDifferential_j₀ hinj]
    module
  have hmem : ((D.a : V) * D.u) • (D.t • d (algebraMap V F D.t)) ∈
      D.scaledLattice ⊔
        D.parameterIdeal • (D.parameterIdeal • D.W) := by
    rw [hid]
    refine Submodule.sub_mem _ (Submodule.neg_mem _ ?_) ?_
    · exact Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (D.scaledDifferential_mem_scaledLattice D.j₀))
    · exact Submodule.mem_sup_right
        (Submodule.smul_mem_smul D.t_mem_parameterIdeal
          (Submodule.smul_mem_smul D.t_mem_parameterIdeal
            D.du_mem))
  have hunit : IsUnit ((D.a : V) * D.u) := D.a_unit.mul D.u_unit
  have hinv : D.t • d (algebraMap V F D.t) =
      (↑hunit.unit⁻¹ : V) • (((D.a : V) * D.u) • (D.t • d (algebraMap V F D.t))) := by
    rw [smul_smul, Units.inv_mul_of_eq hunit.unit_spec, one_smul]
  rw [hinv]
  exact Submodule.smul_mem _ _ hmem

/-- Step (iii): `t` times the unit frame is contained in the scaled lattice
up to `t²` times the unit frame. -/
theorem parameterIdeal_smul_W_le (hinj : Function.Injective (algebraMap V F)) :
    D.parameterIdeal • D.W ≤
      D.scaledLattice ⊔ D.parameterIdeal • (D.parameterIdeal • D.W) := by
  set L := D.scaledLattice
  set I := D.parameterIdeal
  set R := L ⊔ I • (I • D.W)
  -- The elements whose `t`-multiple lies in `R`.
  let M : Submodule V Ω := Submodule.comap (LinearMap.lsmul V Ω D.t) R
  have hM : ∀ ω ∈ M, D.t • ω ∈ R := fun ω hω ↦ hω
  have hcoord : coordinateFrame d D.t D.Q ≤ M := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact D.t_smul_dt_mem hinj
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_sup_left (D.t_smul_dQ_mem_scaledLattice hinj j)
  -- `t` times a visible element lies in `R`.
  have hW : D.W ≤ M := by
    intro ω hω
    obtain ⟨ω₁, hω₁, ω₂, hω₂, rfl⟩ := Submodule.mem_sup.1 (D.visible hω)
    show D.t • (ω₁ + ω₂) ∈ R
    rw [smul_add]
    refine Submodule.add_mem _ (hM ω₁ (hcoord hω₁)) ?_
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul D.t_mem_parameterIdeal hω₂)
  refine Submodule.smul_le.2 ?_
  intro r hr ω hω
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.1 hr
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (hM ω (hW hω))

/-- Nakayama: `t` times the lattice `W` lies in the scaled lattice. -/
theorem parameterIdeal_smul_W_le_scaledLattice
    (hinj : Function.Injective (algebraMap V F)) :
    D.parameterIdeal • D.W ≤ D.scaledLattice :=
  Submodule.le_of_le_smul_of_le_jacobson_bot
    (Submodule.FG.smul D.parameterIdeal_fg D.W_fg)
    D.parameterIdeal_le_jacobson
    (D.parameterIdeal_smul_W_le hinj)

/-- Step (iv): the scaled differential of the selected coordinate `Q₁`
is `t^(a+e-1)` times an element of `t` times the lattice `W`. -/
theorem scaledDifferential_Q₁_eq (hinj : Function.Injective (algebraMap V F)) :
    ∃ ω ∈ D.parameterIdeal • D.W,
      D.scaledDifferential D.Q₁ = D.t ^ (D.a + D.e - 1) • ω := by
  set W := D.W
  obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le' D.one_le_a
  obtain ⟨e', he'⟩ := Nat.exists_eq_add_of_le' D.one_le_e
  -- The unscaled combination inside the unit frame.
  let ω₀ : Ω := (D.u * D.t) • d (algebraMap V F D.w) +
    ((D.e : V) * D.u * D.w) • d (algebraMap V F D.t) -
    (D.t * D.w) • d (algebraMap V F D.u)
  have hω₀ : ω₀ ∈ D.W := by
    refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.smul_mem _ _ D.dw_mem
    · exact Submodule.smul_mem _ _ D.dt_mem
    · exact Submodule.smul_mem _ _ D.du_mem
  refine ⟨D.t • ω₀, Submodule.smul_mem_smul D.t_mem_parameterIdeal hω₀, ?_⟩
  have hexp' : D.a + D.e - 1 = a' + e' + 1 := by omega
  rw [hexp', D.scaledDifferential_eq hinj, D.Q₁_eq, map_mul, map_pow, Derivation.leibniz,
    Derivation.leibniz_pow]
  have hexp : a' + 1 + (e' + 1) - 1 = a' + e' + 1 := by omega
  simp only [ω₀, ha', he', ← Nat.cast_smul_eq_nsmul F, ← map_natCast (algebraMap V F),
    ← map_pow, algebraMap_smul, hexp]
  push_cast
  module

/-- The divisor-tangent lattice lemma.  The differential of the selected
affine coordinate is a combination of the other affine differentials with
coefficients divisible by `t^(a+e-1)`; in particular the coefficients lie in
the maximal ideal of `V`. -/
theorem exists_coefficients (hinj : Function.Injective (algebraMap V F)) :
    ∃ b : ι → V,
      d (algebraMap V F D.Q₁ / algebraMap V F D.Q₀) =
        ∑ j, (D.t ^ (D.a + D.e - 1) * b j) •
          d (algebraMap V F (D.Q j) / algebraMap V F D.Q₀) := by
  classical
  obtain ⟨ω, hω, hℓ⟩ := D.scaledDifferential_Q₁_eq hinj
  have hωL : ω ∈ D.scaledLattice :=
    D.parameterIdeal_smul_W_le_scaledLattice hinj hω
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hωL
  refine ⟨b, ?_⟩
  have hscale := D.scale_ne_zero hinj
  have hleft : (algebraMap V F D.t ^ (D.a + 1) * algebraMap V F D.u ^ 2) •
        d (algebraMap V F D.Q₁ / algebraMap V F D.Q₀) =
      (algebraMap V F D.t ^ (D.a + 1) * algebraMap V F D.u ^ 2) •
        ∑ j, (D.t ^ (D.a + D.e - 1) * b j) •
          d (algebraMap V F (D.Q j) / algebraMap V F D.Q₀) := by
    change D.scaledDifferential D.Q₁ = _
    rw [hℓ, ← hb, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [scaledDifferential, ← algebraMap_smul (R := V) (A := F) (M := Ω), smul_smul,
      map_mul, map_pow]
    ring_nf
  exact smul_right_injective Ω hscale hleft

theorem exists_maximalIdeal_coefficients (hinj : Function.Injective (algebraMap V F)) :
    ∃ c : ι → V, (∀ j, c j ∈ maximalIdeal V) ∧
      d (algebraMap V F D.Q₁ / algebraMap V F D.Q₀) =
        ∑ j, c j • d (algebraMap V F (D.Q j) / algebraMap V F D.Q₀) := by
  obtain ⟨b, hb⟩ := D.exists_coefficients hinj
  refine ⟨fun j ↦ D.t ^ (D.a + D.e - 1) * b j, fun j ↦ ?_, hb⟩
  have hpos : D.a + D.e - 1 = (D.a + D.e - 2) + 1 := by
    have := D.one_le_a; have := D.one_le_e; omega
  show D.t ^ (D.a + D.e - 1) * b j ∈ maximalIdeal V
  rw [hpos, pow_succ]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ D.t_mem)


end VisibleDivisorFrame

end

end Stafford38.Geometry.DivisorTangentLattice
