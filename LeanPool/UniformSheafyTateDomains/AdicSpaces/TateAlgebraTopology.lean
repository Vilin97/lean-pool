/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import LeanPool.UniformSheafyTateDomains.AdicSpaces.TateAlgebra
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings

/-!
# Topology on the Tate Algebra A⟨X⟩

The Tate algebra `A⟨X⟩` inherits the **product topology** from `MvPowerSeries (Fin 1) A`,
where we view power series as functions `(Fin 1 →₀ ℕ) → A` and equip the codomain with
the topology of `A`. The subring `TateAlgebra A ⊂ MvPowerSeries (Fin 1) A` gets the
induced (subspace) topology.

This topology makes `A⟨X⟩` a topological ring (via `Subring.instIsTopologicalRing`)
and is the topology of coefficient-wise convergence: a net of restricted power series
converges iff each coefficient converges in `A`.

## I-adic topology and Huber ring structure

Given a pair of definition `(A₀, I)` for `A`, we construct:

* `TateAlgebra.pairSubring P` : The subring `A₀⟨X⟩ ⊆ A⟨X⟩` of restricted power series
  with coefficients in `A₀`.
* `TateAlgebra.pairConstantHom P` : The constant series embedding `A₀ →+* A₀⟨X⟩`.
* `TateAlgebra.pairIdeal P` : The ideal `I · A₀⟨X⟩` inside `A₀⟨X⟩`.
* `TateAlgebra.pairIdeal_fg P` : Finite generation of `I · A₀⟨X⟩`.
* `TateAlgebra.pairSubring_isHuberRing P` : `A₀⟨X⟩` with the `(I · A₀⟨X⟩)`-adic
  topology is a Huber ring.

The Huber ring structure on `A₀⟨X⟩` uses the pair `(⊤, idealToTop (pairIdeal P))`
where the ring of definition is the whole ring `A₀⟨X⟩` itself, equipped with the
`(pairIdeal P)`-adic topology.

## General results

* `idealToTop I` : Transfer an ideal from `R` to `↥(⊤ : Subring R)`.
* `isAdic_idealToTop I` : The subspace topology on `↥⊤` from the `I`-adic topology
  on `R` is `(idealToTop I)`-adic.
* `pairOfDefinition_ofAdic I hI` : Any ring with finitely generated `I`-adic topology
  admits a pair of definition `(⊤, idealToTop I)`.
* `isHuberRing_ofAdic I hI` : A ring with finitely generated `I`-adic topology is Huber.

## Main results (product topology)

* `TateAlgebra.continuous_coeff` : Each coefficient function `coeff n` is continuous.
* `TateAlgebra.continuous_evalZeroHom` : The evaluation-at-zero map is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6, §8
-/

open MvPowerSeries.WithPiTopology Filter Topology Pointwise

namespace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### Topology instances -/

/-- The topology on `A⟨X⟩` is the subspace topology from `MvPowerSeries (Fin 1) A`
with the product topology. This makes coefficient extraction continuous. -/
example : TopologicalSpace ↥(TateAlgebra A) := inferInstance

/-- `A⟨X⟩` is a topological ring with the subspace topology. -/
example : IsTopologicalRing ↥(TateAlgebra A) := inferInstance

/-! ### Continuity of coefficient extraction -/

/-- The `n`-th coefficient function `coeff n : A⟨X⟩ → A` is continuous
(it's the composition of the continuous embedding into `MvPowerSeries` and
the continuous coefficient projection). -/
theorem continuous_coeff (n : ℕ) :
    Continuous (fun f : ↥(TateAlgebra A) => coeff n f) :=
  (MvPowerSeries.WithPiTopology.continuous_coeff A (toIndex n)).comp continuous_subtype_val

/-- `evalZeroHom` is continuous (it extracts the 0-th coefficient). -/
theorem continuous_evalZeroHom :
    Continuous (evalZeroHom : ↥(TateAlgebra A) → A) :=
  continuous_coeff 0

end TateAlgebra

/-! ### Transfer ideals to ↥⊤ and adic pair of definition

These results show that any commutative ring equipped with a finitely generated
`I`-adic topology admits a canonical pair of definition `(⊤, idealToTop I)`,
making it a Huber ring. This is used to construct the Huber ring structure
on `A₀⟨X⟩`.
-/

section IdealTopTransfer

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Transfer an ideal `I` of `R` to an ideal of `↥(⊤ : Subring R)` via the
inverse of `Subring.topEquiv`. This allows us to work with `PairOfDefinition`,
which requires an ideal of a subring. -/
noncomputable def idealToTop : Ideal ↥(⊤ : Subring R) :=
  I.map (Subring.topEquiv (R := R)).symm.toRingHom

/-- Powers of the transferred ideal equal preimages of the original
powers under `Subtype.val`. -/
theorem idealToTop_pow_eq_preimage (n : ℕ) :
    ((idealToTop I ^ n : Ideal ↥(⊤ : Subring R)) :
      Set ↥(⊤ : Subring R)) =
    Subtype.val ⁻¹' ((I ^ n : Ideal R) : Set R) := by
  unfold idealToTop
  rw [← Ideal.map_pow,
    show (I ^ n).map (Subring.topEquiv (R := R)).symm.toRingHom =
      (I ^ n).map (Subring.topEquiv (R := R)).symm from rfl,
    ← Ideal.comap_symm]
  ext x
  simp only [RingEquiv.symm_symm, Ideal.mem_comap,
    SetLike.mem_coe, Set.mem_preimage]
  rfl

/-- The transferred ideal is finitely generated when the original is. -/
theorem idealToTop_fg (hI : I.FG) : (idealToTop I).FG :=
  hI.map _

/-- When `R` carries the `I`-adic topology, the subspace topology on
`↥(⊤ : Subring R)` is `(idealToTop I)`-adic. This is the key topological
result: the subspace topology on the whole ring (viewed as ↥⊤) correctly
inherits the adic structure. -/
theorem isAdic_idealToTop :
    @IsAdic ↥(⊤ : Subring R) _
      (@instTopologicalSpaceSubtype R (· ∈ (⊤ : Subring R))
        I.adicTopology)
      (idealToTop I) := by
  letI : TopologicalSpace R := I.adicTopology
  letI : IsTopologicalRing R :=
    I.ringFilterBasis.isTopologicalRing
  have hadic : @IsAdic R _ I.adicTopology I := rfl
  rw [@isAdic_iff _ _ _
    (Subring.instIsTopologicalRing (⊤ : Subring R))]
  exact ⟨fun n => by
      rw [idealToTop_pow_eq_preimage I n]
      exact (isAdic_iff.mp hadic).1 n |>.preimage
        continuous_subtype_val,
    fun s hs => by
      rw [nhds_subtype_eq_comap] at hs
      obtain ⟨U, hU, hsU⟩ := Filter.mem_comap.mp hs
      rw [show (0 : ↥(⊤ : Subring R)).val = (0 : R)
        from rfl] at hU
      obtain ⟨n, -, hn⟩ :=
        hadic.hasBasis_nhds_zero.mem_iff.mp hU
      exact ⟨n, (idealToTop_pow_eq_preimage I n ▸
        Set.preimage_mono hn).trans hsU⟩⟩

/-- For a ring `R` with the `I`-adic topology (where `I` is finitely generated),
the pair `(⊤, idealToTop I)` is a pair of definition. -/
noncomputable def pairOfDefinition_ofAdic (hI : I.FG) :
    @PairOfDefinition R _ I.adicTopology := by
  letI : TopologicalSpace R := I.adicTopology
  exact
    { A₀ := ⊤
      I := idealToTop I
      isOpen := isOpen_univ
      fg := idealToTop_fg I hI
      isAdic := isAdic_idealToTop I }

/-- A ring with a finitely generated `I`-adic topology is a Huber ring.
The pair of definition is `(⊤, idealToTop I)`. -/
theorem isHuberRing_ofAdic (hI : I.FG) :
    @IsHuberRing R _ I.adicTopology := by
  letI : TopologicalSpace R := I.adicTopology
  exact ⟨⟨pairOfDefinition_ofAdic I hI⟩⟩

end IdealTopTransfer

/-! ### Ring of definition and ideal for A₀⟨X⟩

Given a pair of definition `(A₀, I)` for a nonarchimedean topological ring `A`,
we construct the algebraic data needed for the Huber ring structure on `A₀⟨X⟩`:
the subring of restricted power series with coefficients in `A₀`, the ideal
generated by constant series from `I`, and finite generation.
-/

namespace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [NonarchimedeanRing A] [IsTopologicalRing A]

/-- The subring of `A⟨X⟩` consisting of restricted power series whose
coefficients all lie in `P.A₀`. This is the "ring of definition"
`A₀⟨X⟩` for the Tate algebra (Wedhorn, §8). -/
noncomputable def pairSubring (P : PairOfDefinition A) :
    Subring ↥(TateAlgebra A) where
  carrier := {f | ∀ s : Fin 1 →₀ ℕ,
    MvPowerSeries.coeff s f.val ∈ P.A₀}
  mul_mem' {f g} hf hg s := by
    simp only [Subring.coe_mul, MvPowerSeries.coeff_mul]
    exact P.A₀.toSubsemiring.sum_mem
      fun p _ => P.A₀.mul_mem (hf p.1) (hg p.2)
  one_mem' s := by
    simp only [OneMemClass.coe_one, MvPowerSeries.coeff_one]
    split
    · exact P.A₀.one_mem
    · exact P.A₀.zero_mem
  add_mem' {f g} hf hg s := by
    simp only [Subring.coe_add, map_add]
    exact P.A₀.add_mem (hf s) (hg s)
  zero_mem' s := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact P.A₀.zero_mem
  neg_mem' {f} hf s := by
    simp only [NegMemClass.coe_neg, map_neg]
    exact P.A₀.neg_mem (hf s)

omit [IsTopologicalRing A] in
/-- Membership in `pairSubring P` means all coefficients lie in `P.A₀`. -/
theorem mem_pairSubring (P : PairOfDefinition A)
    (f : ↥(TateAlgebra A)) :
    f ∈ pairSubring P ↔
      ∀ s, MvPowerSeries.coeff s f.val ∈ P.A₀ :=
  Iff.rfl

/-- The constant power series embedding `P.A₀ →+* A₀⟨X⟩`.
Sends `a ∈ A₀` to the constant restricted power series `C(a)`. -/
noncomputable def pairConstantHom (P : PairOfDefinition A) :
    P.A₀ →+* pairSubring P where
  toFun a := ⟨⟨MvPowerSeries.C a.val,
      MvPowerSeries.IsRestricted_algebraMap a.val⟩, by
    intro s; classical
    simp only [MvPowerSeries.coeff_C]
    split
    · exact a.2
    · exact P.A₀.zero_mem⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_mul, map_mul]))
  map_zero' := Subtype.ext (Subtype.ext (map_zero _))
  map_add' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_add, map_add]))

/-- The ideal `I · A₀⟨X⟩` inside `A₀⟨X⟩`, defined as the image of `P.I`
under the constant power series embedding. This is the ideal of
definition for `A₀⟨X⟩` (Wedhorn, §8). -/
noncomputable def pairIdeal (P : PairOfDefinition A) :
    Ideal (pairSubring P) :=
  Ideal.map (pairConstantHom P) P.I

omit [IsTopologicalRing A] in
/-- The ideal `I · A₀⟨X⟩` is finitely generated (because `I` is). -/
theorem pairIdeal_fg (P : PairOfDefinition A) :
    (pairIdeal P).FG :=
  P.fg.map _

/-! ### Huber ring structure on A₀⟨X⟩ -/

omit [IsTopologicalRing A] in
/-- The ring `A₀⟨X⟩ = pairSubring P`, equipped with the
`(I · A₀⟨X⟩)`-adic topology, is a Huber ring. The pair of definition
is `(⊤, idealToTop (pairIdeal P))`, i.e., the whole ring `A₀⟨X⟩` serves
as its own ring of definition with the ideal `I · A₀⟨X⟩` (Wedhorn, §8). -/
theorem pairSubring_isHuberRing (P : PairOfDefinition A) :
    @IsHuberRing ↥(pairSubring P) _
      (pairIdeal P).adicTopology :=
  isHuberRing_ofAdic _ (pairIdeal_fg P)

omit [IsTopologicalRing A] in
/-- The `(pairIdeal P)`-adic topology on `A₀⟨X⟩` is a ring topology. -/
theorem pairSubring_isTopologicalRing
    (P : PairOfDefinition A) :
    @IsTopologicalRing ↥(pairSubring P)
      (pairIdeal P).adicTopology _ :=
  (pairIdeal P).ringFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- The `(pairIdeal P)`-adic topology on `A₀⟨X⟩` is nonarchimedean. -/
theorem pairSubring_nonarchimedean
    (P : PairOfDefinition A) :
    @NonarchimedeanRing ↥(pairSubring P) _
      (pairIdeal P).adicTopology :=
  Ideal.nonarchimedean (pairIdeal P)

omit [IsTopologicalRing A] in
/-- The `pairIdeal P` is `I`-adic on `A₀⟨X⟩` by construction. -/
theorem pairIdeal_isAdic (P : PairOfDefinition A) :
    @IsAdic ↥(pairSubring P) _
      (pairIdeal P).adicTopology (pairIdeal P) :=
  rfl

/-! ### Natural Tate ring topology on `TateAlgebra A` (Phase 2.2)

We extend the Huber ring structure from `pairSubring P = A₀⟨X⟩` to the full
`TateAlgebra A = A⟨X⟩` by defining a `RingSubgroupsBasis` whose basic
neighborhoods of `0` are the SET-IMAGES of `(pairIdeal P)^n` in `TateAlgebra A`
under the subring inclusion.

The resulting topology makes `pairSubring P = A₀⟨X⟩` an open subring with its
existing `(pairIdeal P)`-adic topology, hence makes `(pairSubring P, pairIdeal P)`
a `PairOfDefinition` and `TateAlgebra A` a Huber ring (Wedhorn §6).

**Why we use `RingSubgroupsBasis` rather than `Ideal.adicTopology`:**
The ideal `pairIdealExt := Ideal.map subtype (pairIdeal P)` of `TateAlgebra A`
generated by the image is *strictly larger* than the set-image, because
multiplication by elements of `TateAlgebra A` outside `pairSubring P` (such as
`1/π`) escapes the subring. So `Ideal.adicTopology pairIdealExt` is the wrong
topology — it would give a `pairSubring P`-adic topology on the whole ring, but
we want only the set-image of `(pairIdeal P)^n` to be the basic neighborhoods.

The `RingSubgroupsBasis` approach uses additive subgroups (set-images), which is
exactly the right notion. The leftMul condition (`∀ x ∈ R, ∀ n, ∃ m, x · G_m ⊆ G_n`)
is the only non-trivial check — it requires the **boundedness** argument
characteristic of Tate rings (every element is `π^{-k}` times a "bounded" element,
and `π^{-k} · J^{n+k} ⊆ J^n` because `π ∈ J`).

**Status (Phase 2.2 session 1):**
- Definitions in place: `tateAlgNhd`, `tateAlgBasis` (RingSubgroupsBasis),
  `tateAlgebraTopology`.
- Filter (antitone) and mul-at-0 conditions: PROVED (easy, ideal multiplication).
- LeftMul condition: SORRY pending the boundedness argument.

**References:**
- Wedhorn lecture notes `1910.05934v1.pdf` §6, especially Definitions 6.1, 6.10.
- `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` Phase 2.2.
-/

section TateAlgebraNaturalTopology

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [NonarchimedeanRing A]

/-- The `n`-th basic neighborhood of `0` in `TateAlgebra A`: the set-image of
`(pairIdeal P)^n` under the inclusion `pairSubring P ↪ TateAlgebra A`,
viewed as an additive subgroup. -/
noncomputable def tateAlgNhd (P : PairOfDefinition A) (n : ℕ) :
    AddSubgroup ↥(TateAlgebra A) :=
  ((pairIdeal P) ^ n).toAddSubgroup.map
    (pairSubring P).subtype.toAddMonoidHom

omit [IsTopologicalRing A] in
/-- The neighborhoods are antitone in `n`. -/
theorem tateAlgNhd_antitone (P : PairOfDefinition A) :
    Antitone (tateAlgNhd P) :=
  fun _ _ h ↦ AddSubgroup.map_mono
    (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

omit [IsTopologicalRing A] in
/-- `0 ∈ tateAlgNhd P n` for all `n`. -/
theorem zero_mem_tateAlgNhd (P : PairOfDefinition A) (n : ℕ) :
    (0 : ↥(TateAlgebra A)) ∈ tateAlgNhd P n :=
  ⟨0, ((pairIdeal P) ^ n).zero_mem, map_zero _⟩

/-! #### Sub-task A: coefficient extraction for `tateAlgNhd P n`

We prove that if `y ∈ tateAlgNhd P n`, then every coefficient of `y` (as an
element of `A`) lies in the image of `P.I^n` under `Subtype.val : P.A₀ → A`.

The proof defines an auxiliary ideal of `pairSubring P` — the elements whose
coefficients all lie in the image of a given ideal of `P.A₀` — and shows:
1. This is actually an ideal of `pairSubring P`.
2. It contains the generators of `pairIdeal P` (constant series from `P.I`).
3. Hence it contains `pairIdeal P` itself, and by multiplication properties,
   `(pairIdeal P)^n ⊆ {elements with coeffs in P.I^n}`. -/

/-- Auxiliary ideal: elements of `pairSubring P` all of whose coefficients lie
in the image of a given ideal `I : Ideal P.A₀` under the inclusion `P.A₀ ↪ A`. -/
noncomputable def coeffInIdealIdeal (P : PairOfDefinition A) (I : Ideal P.A₀) :
    Ideal ↥(pairSubring P) where
  carrier := {z | ∀ l, ∃ b : P.A₀, b ∈ I ∧ (b : A) = MvPowerSeries.coeff l z.val.val}
  zero_mem' l := ⟨0, I.zero_mem, by simp⟩
  add_mem' {z w} hz hw l := by
    obtain ⟨b_z, hb_z, heq_z⟩ := hz l
    obtain ⟨b_w, hb_w, heq_w⟩ := hw l
    refine ⟨b_z + b_w, I.add_mem hb_z hb_w, ?_⟩
    change ((b_z + b_w : P.A₀) : A) = MvPowerSeries.coeff l (z + w).val.val
    push_cast
    rw [heq_z, heq_w, ← map_add]
  smul_mem' r z hz l := by
    -- coeff l (r · z) = Σ_{l_1+l_2=l} (coeff l_1 r) · (coeff l_2 z)
    -- For each term: (coeff l_1 r) ∈ A₀, (coeff l_2 z) = (b_{l_2} : A) for b_{l_2} ∈ I.
    -- Product: (coeff l_1 r) · b_{l_2} ∈ I (ideal closure under P.A₀-mul).
    -- We need to assemble this into one element of I.
    classical
    have hr : ∀ l_1, MvPowerSeries.coeff l_1 r.val.val ∈ P.A₀ := r.property
    -- Build the sum witness
    let f : (Fin 1 →₀ ℕ) × (Fin 1 →₀ ℕ) → P.A₀ := fun p =>
      ⟨MvPowerSeries.coeff p.1 r.val.val, hr p.1⟩ *
        (hz p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · -- Sum of elements in I is in I
      refine I.sum_mem fun p _ => ?_
      -- Each term is (r-coeff) · (z-coeff), and the z-coeff is in I
      exact I.mul_mem_left _ (hz p.2).choose_spec.1
    · -- The sum equals coeff l (r · z)
      change ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (r • z).val.val
      push_cast [f]
      change (∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 r.val.val * ((hz p.2).choose : A)) =
        MvPowerSeries.coeff l (r • z).val.val
      rw [show (r • z).val.val = r.val.val * z.val.val from rfl]
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(hz p.2).choose_spec.2]

omit [IsTopologicalRing A] in
/-- Constant series from `P.I^n` have their unique nonzero coefficient in `P.I^n`. -/
private theorem pairConstantHom_mem_coeffInIdeal (P : PairOfDefinition A) {n : ℕ}
    (c : P.A₀) (hc : c ∈ P.I ^ n) :
    pairConstantHom P c ∈ coeffInIdealIdeal P (P.I ^ n) := by
  intro l
  classical
  by_cases hl : l = 0
  · refine ⟨c, hc, ?_⟩
    show (c : A) = MvPowerSeries.coeff l (pairConstantHom P c).val.val
    subst hl
    change (c : A) = MvPowerSeries.coeff 0 (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_zero_C]
  · refine ⟨0, (P.I ^ n).zero_mem, ?_⟩
    show ((0 : P.A₀) : A) = MvPowerSeries.coeff l (pairConstantHom P c).val.val
    change (0 : A) = MvPowerSeries.coeff l (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_C, if_neg hl]

omit [IsTopologicalRing A] in
/-- `pairIdeal P ⊆ coeffInIdealIdeal P P.I`: every element of `pairIdeal P`
has all coefficients in the image of `P.I` under `Subtype.val`. -/
theorem pairIdeal_le_coeffInIdeal (P : PairOfDefinition A) :
    pairIdeal P ≤ coeffInIdealIdeal P P.I := by
  -- pairIdeal P = Ideal.map (pairConstantHom P) P.I. Use `Ideal.map_le_iff_le_comap`
  -- to reduce to: every `c ∈ P.I` has `pairConstantHom c ∈ coeffInIdealIdeal P P.I`.
  unfold pairIdeal
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  change pairConstantHom P c ∈ coeffInIdealIdeal P P.I
  have h1 : c ∈ P.I ^ 1 := by rw [pow_one]; exact hc
  have := pairConstantHom_mem_coeffInIdeal P (n := 1) c h1
  convert this using 1
  rw [pow_one]

omit [IsTopologicalRing A] in
/-- The auxiliary ideal is compatible with ideal multiplication in `P.A₀`:
if `J_1 ⊆ coeffInIdealIdeal I_1` and `J_2 ⊆ coeffInIdealIdeal I_2`, then
`J_1 · J_2 ⊆ coeffInIdealIdeal (I_1 · I_2)`. -/
theorem coeffInIdealIdeal_mul_mono (P : PairOfDefinition A) {I₁ I₂ : Ideal P.A₀}
    {J₁ J₂ : Ideal ↥(pairSubring P)}
    (h₁ : J₁ ≤ coeffInIdealIdeal P I₁) (h₂ : J₂ ≤ coeffInIdealIdeal P I₂) :
    J₁ * J₂ ≤ coeffInIdealIdeal P (I₁ * I₂) := by
  intro z hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · -- Case: product a * b with a ∈ J₁, b ∈ J₂
    intro a ha b hb l
    classical
    -- Use h₁ on a and h₂ on b to get coefficient witnesses
    have ha' : a ∈ coeffInIdealIdeal P I₁ := h₁ ha
    have hb' : b ∈ coeffInIdealIdeal P I₂ := h₂ hb
    -- Build the sum witness for coeff l (a * b)
    let f : (Fin 1 →₀ ℕ) × (Fin 1 →₀ ℕ) → P.A₀ := fun p =>
      (ha' p.1).choose * (hb' p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · refine (I₁ * I₂).sum_mem fun p _ => ?_
      exact Ideal.mul_mem_mul (ha' p.1).choose_spec.1 (hb' p.2).choose_spec.1
    · change ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (a * b).val.val
      push_cast [f]
      change (∑ p ∈ Finset.antidiagonal l,
          ((ha' p.1).choose : A) * ((hb' p.2).choose : A)) =
        MvPowerSeries.coeff l (a * b).val.val
      rw [show (a * b).val.val = a.val.val * b.val.val from rfl]
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(ha' p.1).choose_spec.2, (hb' p.2).choose_spec.2]
  · -- Case: z₁ + z₂ both with the property
    intro z₁ z₂ h₁' h₂' l
    obtain ⟨b₁, hb₁, heq₁⟩ := h₁' l
    obtain ⟨b₂, hb₂, heq₂⟩ := h₂' l
    refine ⟨b₁ + b₂, (I₁ * I₂).add_mem hb₁ hb₂, ?_⟩
    change ((b₁ : A) + (b₂ : A)) = MvPowerSeries.coeff l (z₁ + z₂).val.val
    rw [show (z₁ + z₂).val.val = z₁.val.val + z₂.val.val from rfl, map_add,
      ← heq₁, ← heq₂]

omit [IsTopologicalRing A] in
/-- `(pairIdeal P)^n ⊆ coeffInIdealIdeal P (P.I^n)`: elements of `(pairIdeal P)^n`
have all coefficients in the image of `P.I^n` under `Subtype.val`. -/
theorem pairIdeal_pow_le_coeffInIdeal (P : PairOfDefinition A) (n : ℕ) :
    (pairIdeal P) ^ n ≤ coeffInIdealIdeal P (P.I ^ n) := by
  induction n with
  | zero =>
    -- (pairIdeal P)^0 = ⊤ and P.I^0 = ⊤.
    intro z _ l
    refine ⟨⟨MvPowerSeries.coeff l z.val.val, z.property l⟩, ?_, rfl⟩
    -- Goal: ⟨..., ...⟩ ∈ P.I ^ 0. Since P.I^0 = 1 = ⊤, this is trivial.
    simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact coeffInIdealIdeal_mul_mono P ih (pairIdeal_le_coeffInIdeal P)

omit [IsTopologicalRing A] in
/-- **Sub-task A (main result):** if `y ∈ tateAlgNhd P n`, then every coefficient
of `y` (as an element of `A` via `MvPowerSeries.coeff`) lies in the image of
`P.I^n` under `Subtype.val`. -/
theorem tateAlgNhd_coeff_mem (P : PairOfDefinition A) (n : ℕ)
    {y : ↥(TateAlgebra A)} (hy : y ∈ tateAlgNhd P n) (l : Fin 1 →₀ ℕ) :
    ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = MvPowerSeries.coeff l y.val := by
  obtain ⟨z, hz, rfl⟩ := hy
  -- y = ↑z, so y.val = z.val.val
  have := pairIdeal_pow_le_coeffInIdeal P n hz l
  change ∃ b, b ∈ P.I ^ n ∧ (b : A) =
    MvPowerSeries.coeff l ((pairSubring P).subtype.toAddMonoidHom z).val
  exact this

omit [IsTopologicalRing A] in
/-- The product `tateAlgNhd P n · tateAlgNhd P n ⊆ tateAlgNhd P n`, because
`(pairIdeal P)^n · (pairIdeal P)^n ⊆ (pairIdeal P)^(2n) ⊆ (pairIdeal P)^n`. -/
private theorem tateAlgNhd_mul (P : PairOfDefinition A) (i : ℕ) :
    ∃ j, (tateAlgNhd P j : Set ↥(TateAlgebra A)) *
      (tateAlgNhd P j : Set ↥(TateAlgebra A)) ⊆
        (tateAlgNhd P i : Set ↥(TateAlgebra A)) := by
  refine ⟨i, ?_⟩
  rintro _ ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨d₂, hd₂, rfl⟩, rfl⟩
  refine ⟨d₁ * d₂, ?_, MulMemClass.coe_mul ..⟩
  exact Ideal.pow_le_pow_right (Nat.le_add_left i i)
    (pow_add (pairIdeal P) i i ▸ Ideal.mul_mem_mul hd₁ hd₂)

/-! #### Sub-tasks B and C: I-adic continuity + almost-all-coeffs -/

omit [NonarchimedeanRing A] in
/-- **Sub-task B:** For any `a ∈ A` and any `n : ℕ`, there exists `m : ℕ` such
that `a · b ∈ image of P.I^n` (under `Subtype.val`) whenever `b ∈ image of P.I^m`.

This is the continuity of left-multiplication by `a` at `0` in A's topology,
applied to the neighborhood `image of P.I^n`. -/
theorem exists_mul_pow_subset_pow (P : PairOfDefinition A) (a : A) (n : ℕ) :
    ∃ m : ℕ, ∀ b : P.A₀, b ∈ P.I ^ m →
      ∃ c : P.A₀, c ∈ P.I ^ n ∧ (c : A) = a * (b : A) := by
  -- The image of `P.I^n` under `Subtype.val : P.A₀ → A` is a nhd of 0 in A
  -- (by `P.hasBasis_nhds_zero`).
  have hU : (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) ∈ nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  -- By continuity of `(a * ·)` at 0, the preimage is also a nhd of 0.
  have hcont : Continuous fun b : A => a * b := continuous_const.mul continuous_id
  have hV : (fun b : A => a * b) ⁻¹' (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) ∈
      nhds (0 : A) := by
    have h0 : (0 : A) ∈
        (fun b : A => a * b) ⁻¹' (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) := by
      simp only [Set.mem_preimage, mul_zero]
      exact ⟨0, (P.I ^ n).zero_mem, rfl⟩
    exact hcont.continuousAt.preimage_mem_nhds (by
      rw [show (a * (0 : A)) = (0 : A) from mul_zero a]
      exact hU)
  -- Extract m from the basis.
  obtain ⟨m, -, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp hV
  refine ⟨m, fun b hb => ?_⟩
  -- b ∈ P.I^m, goal: ∃ c ∈ P.I^n, (c : A) = a * (b : A).
  have hbA : (b : A) ∈ (Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀)) :=
    ⟨b, hb, rfl⟩
  have := hm hbA
  simp only [Set.mem_preimage, Set.mem_image] at this
  obtain ⟨c, hc, heq⟩ := this
  exact ⟨c, hc, heq⟩

/-- **Sub-task C:** For `x ∈ TateAlgebra A` and `n : ℕ`, eventually every
coefficient of `x` lies in `image of P.I^n` under `Subtype.val`. Equivalently,
`{l : Fin 1 →₀ ℕ | coeff l x ∉ image of P.I^n}` is cofinite.

This follows from `x` being a restricted power series (`coeff l x → 0` cofinitely
in A) and `image of P.I^n` being a neighborhood of `0` in A. -/
theorem tateAlgebra_coeff_eventually_in_pow (P : PairOfDefinition A)
    (x : ↥(TateAlgebra A)) (n : ℕ) :
    ∀ᶠ (l : Fin 1 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) := by
  -- x is restricted, so its coefficients converge to 0 cofinitely.
  have hres : Filter.Tendsto
      (fun l : Fin 1 →₀ ℕ => MvPowerSeries.coeff l x.val)
      Filter.cofinite (nhds (0 : A)) := x.property
  -- The target set is a nhd of 0 in A.
  have hU : (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) ∈ nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  exact hres hU

/-! #### Sub-task D: Reverse coefficient characterization (principal case)

For the principal case `P.I = (π : P.A₀)` with `π` a unit in `A`, we can
directly reconstruct membership in `(pairIdeal P)^n` from the coefficient
condition. The key observation: `y = π^n · g` where `g` is the "divided"
series `π^{-n} · y` (using the inverse of `π` in `A`).

The element `g` has coefficients in `P.A₀` (because each `y_l = a_l · π^n`
in `P.A₀`, and `π^{-n} · y_l = a_l ∈ P.A₀`). It's automatically restricted
because it's the product of `y` (a restricted series) with the constant
series `π^{-n}` in `TateAlgebra A`.
-/

omit [IsTopologicalRing A] in
/-- **Sub-task D (principal case):** if `P.I = (π)` for some `π ∈ P.A₀` that
is a unit in `A`, and `y ∈ pairSubring P` has all coefficients in the image
of `P.I^n`, then `y ∈ tateAlgNhd P n` (i.e., `⟨y, hy_pair⟩ ∈ (pairIdeal P)^n`).

The principal-pair hypothesis is needed to use `Ideal.mem_span_singleton` for
the decomposition `b_l = a_l * π^n`. The topologically-nilpotent-unit hypothesis
is needed for `π` to be invertible in `A` (so we can construct the "divided"
series `g = π^{-n} · y`). -/
theorem tateAlgNhd_of_coeff_mem_principal (P : PairOfDefinition A) (n : ℕ)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    {y : ↥(TateAlgebra A)} (hy_pair : y ∈ pairSubring P)
    (hy_coeff : ∀ l : Fin 1 →₀ ℕ, ∃ b : P.A₀, b ∈ P.I ^ n ∧
      (b : A) = MvPowerSeries.coeff l y.val) :
    y ∈ tateAlgNhd P n := by
  classical
  -- Step 1: Define πinv, the inverse of π in A.
  let πinv : A := ↑hπ_unit.unit⁻¹
  have hπinv_mul : (π : A) * πinv = 1 := hπ_unit.mul_val_inv
  have hπinv_pow : (π : A) ^ n * πinv ^ n = 1 := by
    rw [← mul_pow, hπinv_mul, one_pow]
  -- Step 2: P.I ^ n = span {π^n}
  have hpow : (P.I ^ n : Ideal P.A₀) = Ideal.span {π ^ n} := by
    rw [hπ_gen, Ideal.span_singleton_pow]
  -- Step 3: Define the "divided" series g = (C πinv^n) * y in TateAlgebra A.
  let g_val : ↥(TateAlgebra A) := algebraMap A ↥(TateAlgebra A) (πinv ^ n) * y
  -- Step 4: g_val ∈ pairSubring P (all coefficients are in P.A₀)
  have hg_in : g_val ∈ pairSubring P := by
    intro l
    -- coeff l g_val = πinv^n * coeff l y.val
    have hcoeff_g : MvPowerSeries.coeff l g_val.val = πinv ^ n * MvPowerSeries.coeff l y.val := by
      change MvPowerSeries.coeff l
        (((algebraMap A ↥(TateAlgebra A)) (πinv ^ n) * y).val) = _
      change MvPowerSeries.coeff l
        ((MvPowerSeries.C (πinv ^ n) : MvPowerSeries (Fin 1) A) * y.val) = _
      rw [MvPowerSeries.coeff_C_mul]
    change MvPowerSeries.coeff l g_val.val ∈ P.A₀
    rw [hcoeff_g]
    -- coeff l y.val = (b_l : A) for b_l ∈ P.I^n = span{π^n}, so b_l = a_l * π^n
    obtain ⟨b, hb_mem, hb_eq⟩ := hy_coeff l
    rw [← hb_eq]
    rw [hpow] at hb_mem
    obtain ⟨a, ha_eq⟩ := Ideal.mem_span_singleton.mp hb_mem
    -- b = π^n * a (Ideal.mem_span_singleton gives the multiple form)
    rw [ha_eq]
    -- Goal: πinv^n * ((π^n * a : P.A₀) : A) ∈ P.A₀
    change πinv ^ n * ((π ^ n * a : P.A₀) : A) ∈ P.A₀
    have : πinv ^ n * ((π ^ n * a : P.A₀) : A) = (a : A) := by
      push_cast
      rw [show πinv ^ n * ((π : A) ^ n * (a : A)) = ((π : A) ^ n * πinv ^ n) * (a : A) by ring,
        hπinv_pow, one_mul]
    rw [this]
    exact a.property
  -- Step 5: y = pairConstantHom(π^n) * g_in_subring in pairSubring P.
  let g_in_subring : ↥(pairSubring P) := ⟨g_val, hg_in⟩
  have hy_eq : (⟨y, hy_pair⟩ : ↥(pairSubring P)) = pairConstantHom P (π ^ n) * g_in_subring := by
    apply Subtype.ext
    apply Subtype.ext
    -- Both sides as MvPowerSeries (Fin 1) A
    ext l
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l
        ((pairConstantHom P (π ^ n) * g_in_subring : ↥(pairSubring P)) : ↥(TateAlgebra A)).val
    -- RHS = coeff l ((pairConstantHom (π^n)).val * g_val.val)
    -- = coeff l (C (π^n : A) * (C (πinv^n) * y.val))
    -- = coeff l (C ((π^n : A) * πinv^n) * y.val)
    -- = coeff l (C 1 * y.val) = coeff l y.val
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l
        ((MvPowerSeries.C ((π : A) ^ n)) * g_val.val)
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l ((MvPowerSeries.C ((π : A) ^ n)) *
        ((MvPowerSeries.C (πinv ^ n)) * y.val))
    rw [← mul_assoc, ← map_mul, hπinv_pow, map_one, one_mul]
  -- Step 6: Conclude y ∈ tateAlgNhd P n.
  refine ⟨⟨y, hy_pair⟩, ?_, rfl⟩
  rw [hy_eq]
  -- (pairConstantHom(π^n) * g_in_subring) ∈ (pairIdeal P)^n
  have hπ_in : pairConstantHom P π ∈ pairIdeal P := by
    unfold pairIdeal
    exact Ideal.mem_map_of_mem _
      (by rw [hπ_gen]; exact Ideal.mem_span_singleton_self π)
  have hπn_in : pairConstantHom P (π ^ n) ∈ (pairIdeal P) ^ n := by
    rw [map_pow]
    exact Ideal.pow_mem_pow hπ_in n
  exact ((pairIdeal P) ^ n).mul_mem_right g_in_subring hπn_in

omit [IsTopologicalRing A] in
/-- **Easy case of leftMul:** when `x ∈ pairSubring P`, multiplication by `x`
preserves the basic neighborhoods because they are images of ideals of
`pairSubring P`, which are closed under multiplication by elements of
`pairSubring P`. Take `j = i`. -/
private theorem tateAlgNhd_leftMul_of_mem (P : PairOfDefinition A)
    {x : ↥(TateAlgebra A)} (hx : x ∈ pairSubring P) (i : ℕ) :
    (tateAlgNhd P i : Set ↥(TateAlgebra A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd P i : Set ↥(TateAlgebra A)) := by
  rintro _ ⟨y, hy, rfl⟩
  -- `x · ↑y = ↑(⟨x, hx⟩ * y)` and `⟨x, hx⟩ * y ∈ (pairIdeal P)^i` because
  -- ideals are closed under left multiplication by ring elements.
  refine ⟨⟨x, hx⟩ * y, ?_, ?_⟩
  · exact ((pairIdeal P) ^ i).mul_mem_left ⟨x, hx⟩ hy
  · exact MulMemClass.coe_mul ..

/-- **Sub-task F (assembly): the leftMul condition for a principal pair.**

For a principal pair `P.I = (π : P.A₀)` with `π` a unit in `A`, the condition
`∃ j, x · tateAlgNhd P j ⊆ tateAlgNhd P i` holds for every `x ∈ TateAlgebra A`
and every `i : ℕ`.

**Proof:** Using Sub-tasks A (forward coefficient extraction), B (I-adic
continuity), C (restricted series convergence), and D (reverse coefficient
characterization, principal case):
1. By Sub-task C, `S := {l : coeff l x ∉ image P.I^i}` is finite.
2. For each `l ∈ S`, Sub-task B gives `m_l` with `coeff l x · image P.I^{m_l} ⊆ image P.I^i`.
3. Take `j := max(i, sup {m_l : l ∈ S})` (over the finite set).
4. For `y ∈ tateAlgNhd P j`: Sub-task A gives all coefficients of `y` in image P.I^j.
5. Compute coefficients of `x · y` via `MvPowerSeries.coeff_mul`:
   `(x · y)_k = Σ_{l+m=k} (coeff l x) · (coeff m y)`.
   Each term is in image P.I^i (splitting on `l ∈ S` vs `l ∉ S`).
6. Hence all coefficients of `x · y` are in image P.I^i. Since these are in
   P.A₀, `x · y ∈ pairSubring P`.
7. By Sub-task D (principal case), `x · y ∈ (pairIdeal P)^i`, i.e.,
   `x · y ∈ tateAlgNhd P i`. -/
theorem tateAlgNhd_leftMul_of_principal [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(TateAlgebra A)) (i : ℕ) :
    ∃ j, (tateAlgNhd P j : Set ↥(TateAlgebra A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd P i : Set ↥(TateAlgebra A)) := by
  classical
  -- Step 1: Find the finite set S of "bad" indices (coeff l x ∉ image P.I^i).
  have hS : ∀ᶠ (l : Fin 1 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A) :=
    tateAlgebra_coeff_eventually_in_pow P x i
  -- Extract the finite set where the condition fails.
  set S : Set (Fin 1 →₀ ℕ) := {l |
    MvPowerSeries.coeff l x.val ∉
      (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A)} with hS_def
  have hS_finite : S.Finite := hS
  -- Step 2: For each l ∈ S, find m_l via Sub-task B.
  let m_fn : (Fin 1 →₀ ℕ) → ℕ := fun (l : Fin 1 →₀ ℕ) =>
    (exists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose
  have hm_spec : ∀ (l : Fin 1 →₀ ℕ), ∀ b : P.A₀, b ∈ P.I ^ (m_fn l) →
      ∃ c : P.A₀, c ∈ P.I ^ i ∧ (c : A) = MvPowerSeries.coeff l x.val * (b : A) :=
    fun l => (exists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose_spec
  -- Step 3: Take j := max(i, sup {m_l : l ∈ S}).
  let j : ℕ := max i (hS_finite.toFinset.sup m_fn)
  have hj_ge_i : i ≤ j := le_max_left _ _
  have hj_ge_m : ∀ l ∈ hS_finite.toFinset, m_fn l ≤ j := fun l hl =>
    le_max_of_le_right (Finset.le_sup hl)
  refine ⟨j, ?_⟩
  -- Step 4: For y with ↑y ∈ tateAlgNhd P j, show x * ↑y ∈ tateAlgNhd P i.
  rintro _ ⟨y, hy, rfl⟩
  change (x * (pairSubring P).subtype y) ∈ tateAlgNhd P i
  -- From Sub-task A: coefficients of y lie in image P.I^j.
  have hy_coeff : ∀ l, ∃ b : P.A₀, b ∈ P.I ^ j ∧
      (b : A) = MvPowerSeries.coeff l ((pairSubring P).subtype y).val :=
    pairIdeal_pow_le_coeffInIdeal P j hy
  set xy : ↥(TateAlgebra A) := x * (pairSubring P).subtype y with hxy_def
  -- **Key claim:** every coefficient of xy is in the image of P.I^i.
  -- For each antidiagonal pair p = (p.1, p.2), the product
  -- `(coeff p.1 x) * (coeff p.2 y)` is in image P.I^i, with a concrete
  -- P.A₀ witness `term_of p`. Define this witness first.
  have hterm : ∀ p : (Fin 1 →₀ ℕ) × (Fin 1 →₀ ℕ),
      ∃ c : P.A₀, c ∈ P.I ^ i ∧
        (c : A) = MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
    intro p
    -- Extract the y-coefficient witness (in P.I^j).
    obtain ⟨b_p, hb_p_mem, hb_p_eq⟩ := hy_coeff p.2
    by_cases hp : p.1 ∈ S
    · -- Bad case: use Sub-task B via `hm_spec`.
      have hb_lower : b_p ∈ P.I ^ (m_fn p.1) :=
        Ideal.pow_le_pow_right (hj_ge_m p.1 (hS_finite.mem_toFinset.mpr hp)) hb_p_mem
      obtain ⟨c, hc_mem, hc_eq⟩ := hm_spec p.1 b_p hb_lower
      refine ⟨c, hc_mem, ?_⟩
      rw [hc_eq, hb_p_eq]
      rfl
    · -- Good case: coeff p.1 x is already in image P.I^i.
      rw [hS_def] at hp
      simp only [Set.mem_setOf_eq, not_not] at hp
      obtain ⟨a, ha_mem, ha_eq⟩ := hp
      refine ⟨a * b_p, Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hj_ge_i hb_p_mem), ?_⟩
      push_cast
      rw [ha_eq, hb_p_eq]
      rfl
  -- Assemble the sum witness for each coefficient of xy.
  have hxy_coeff : ∀ l, ∃ c : P.A₀, c ∈ P.I ^ i ∧
      (c : A) = MvPowerSeries.coeff l xy.val := by
    intro l
    -- coeff l xy = Σ_p (coeff p.1 x) * (coeff p.2 y) over antidiagonal.
    have hcoeff : MvPowerSeries.coeff l xy.val =
        ∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
      change MvPowerSeries.coeff l (x.val * y.val.val) = _
      rw [MvPowerSeries.coeff_mul]
    -- Build the sum witness in P.A₀.
    refine ⟨∑ p ∈ Finset.antidiagonal l, (hterm p).choose, ?_, ?_⟩
    · -- Sum of elements of P.I^i stays in P.I^i.
      exact (P.I ^ i).sum_mem fun p _ => (hterm p).choose_spec.1
    · -- Coerce and match with coeff l xy.
      rw [hcoeff]
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      exact (hterm p).choose_spec.2
  -- Coefficient condition implies `xy ∈ pairSubring P` (since P.I^i ⊆ P.A₀).
  have hxy_pair : xy ∈ pairSubring P := by
    intro l
    obtain ⟨c, _, hc_eq⟩ := hxy_coeff l
    rw [← hc_eq]
    exact c.property
  -- Apply Sub-task D (principal case) to conclude.
  exact tateAlgNhd_of_coeff_mem_principal P i π hπ_gen hπ_unit hxy_pair hxy_coeff

omit [IsTopologicalRing A] in
/-- **The leftMul condition (Phase 2.2):** for every `x ∈ TateAlgebra A` and
every `i : ℕ`, there exists `j` with `x · tateAlgNhd P j ⊆ tateAlgNhd P i`.

This is the general-pair version, derived from the principal-pair version
`tateAlgNhd_leftMul_of_principal` via Wedhorn 6.14 (any Tate ring admits a
principal pair of definition). Phase 2.2 session 2 supplies the principal
case; the reduction to the general case via Wedhorn 6.14 is deferred.

For now, we state the general theorem with an explicit principal-pair
hypothesis passed via `IsTateRing`. This matches the typical usage pattern
where downstream consumers supply an appropriate principal pair. -/
theorem tateAlgNhd_leftMul [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(TateAlgebra A)) (i : ℕ) :
    ∃ j, (tateAlgNhd P j : Set ↥(TateAlgebra A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd P i : Set ↥(TateAlgebra A)) :=
  tateAlgNhd_leftMul_of_principal P π hπ_gen hπ_unit x i

/-- The `RingSubgroupsBasis` for the natural Tate topology on `TateAlgebra A`.
Requires a principal pair of definition. -/
noncomputable def tateAlgBasis [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    RingSubgroupsBasis (tateAlgNhd P) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (tateAlgNhd_antitone P (le_max_left i j))
        (tateAlgNhd_antitone P (le_max_right i j))⟩)
    (tateAlgNhd_mul P)
    (tateAlgNhd_leftMul P π hπ_gen hπ_unit)

/-- The natural Tate topology on `TateAlgebra A`, with `0`-neighborhoods
`{set-image of (pairIdeal P)^n}`. Requires a principal pair of definition. -/
@[reducible] noncomputable def tateAlgebraTopology [IsTateRing A]
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    TopologicalSpace ↥(TateAlgebra A) :=
  (tateAlgBasis P π hπ_gen hπ_unit).topology

omit [IsTopologicalRing A] in
/-- The natural Tate topology is a ring topology. -/
theorem tateAlgebraTopology_isTopologicalRing [IsTateRing A]
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    @IsTopologicalRing ↥(TateAlgebra A) (tateAlgebraTopology P π hπ_gen hπ_unit) _ :=
  (tateAlgBasis P π hπ_gen hπ_unit).toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `tateAlgNhd P n` (as a set in `TateAlgebra A`) is contained in `pairSubring P`,
because each basic neighborhood is the image of an ideal of `pairSubring P` under
the subring inclusion. -/
theorem tateAlgNhd_le_pairSubring (P : PairOfDefinition A) (n : ℕ) :
    (tateAlgNhd P n : Set ↥(TateAlgebra A)) ⊆
      (pairSubring P : Set ↥(TateAlgebra A)) := by
  rintro _ ⟨y, _, rfl⟩
  exact y.property

omit [IsTopologicalRing A] in
/-- `pairSubring P` is open in `TateAlgebra A` with the natural Tate topology.
The subgroup `tateAlgNhd P 1 = image of pairIdeal P` is a basic neighborhood of `0`
contained in `pairSubring P`. -/
theorem pairSubring_isOpen [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π}) (hπ_unit : IsUnit ((π : A))) :
    @IsOpen ↥(TateAlgebra A) (tateAlgebraTopology P π hπ_gen hπ_unit)
      ((pairSubring P : Subring ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) := by
  letI : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology P π hπ_gen hπ_unit
  haveI := tateAlgebraTopology_isTopologicalRing P π hπ_gen hπ_unit
  refine (pairSubring P).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
  refine Filter.mem_of_superset
    ((tateAlgBasis P π hπ_gen hπ_unit).hasBasis_nhds_zero.mem_of_mem (i := 1) trivial) ?_
  exact tateAlgNhd_le_pairSubring P 1

/-! ### Unparameterized canonical natural Tate topology

Using `IsTateRing.principalPair` (via `exists_principal_pairOfDefinition`,
Wedhorn 6.14), we get a canonical principal pair of definition and hence a
canonical natural Tate topology on `TateAlgebra A`, without needing to supply
a pair of definition explicitly. -/

/-- The canonical `RingSubgroupsBasis` for the natural Tate topology on
`TateAlgebra A`, using `IsTateRing.principalPair` via Wedhorn 6.14. -/
noncomputable def tateAlgBasis' [IsTateRing A] :
    RingSubgroupsBasis (tateAlgNhd (IsTateRing.principalPair A).toPairOfDefinition) :=
  let P := IsTateRing.principalPair A
  tateAlgBasis P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

/-- The canonical natural Tate topology on `TateAlgebra A` for any Tate ring `A`.
Uses the canonical principal pair of definition `IsTateRing.principalPair A`
supplied by Wedhorn 6.14. -/
@[reducible] noncomputable def tateAlgebraTopology' [IsTateRing A] :
    TopologicalSpace ↥(TateAlgebra A) :=
  tateAlgBasis' (A := A).topology

omit [IsTopologicalRing A] in
/-- The canonical natural Tate topology is a ring topology. -/
theorem tateAlgebraTopology'_isTopologicalRing [IsTateRing A] :
    @IsTopologicalRing ↥(TateAlgebra A) tateAlgebraTopology' _ :=
  tateAlgBasis'.toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `pairSubring (IsTateRing.principalPair A).toPairOfDefinition` is open in the
canonical natural Tate topology. -/
theorem pairSubring_principalPair_isOpen' [IsTateRing A] :
    @IsOpen ↥(TateAlgebra A) tateAlgebraTopology'
      ((pairSubring (IsTateRing.principalPair A).toPairOfDefinition :
        Subring ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) :=
  let P := IsTateRing.principalPair A
  pairSubring_isOpen P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

/-! ### Canonical topology and foundational instances on `TateAlgebra A`

For a Tate ring `A`, we install `tateAlgebraTopology'` as the **canonical**
`TopologicalSpace` instance on `↥(TateAlgebra A)` (priority 1000). This
shadows the default `instTopologicalSpaceSubtype` (the subspace/product
topology from `MvPowerSeries`) which is too coarse for adic geometry.

The canonical topology makes `TateAlgebra A` a Tate ring: it is a ring topology
(`IsTopologicalRing`), Hausdorff (`T2Space`), complete (`CompleteSpace`), and
carries a topologically nilpotent unit (`IsTateRing`). The ring of definition
is `pairSubring P` (= `A₀⟨X⟩`) with ideal of definition `pairIdeal P`. -/

/-- The canonical topology on `TateAlgebra A` for Tate rings: the natural Tate
topology from the `RingSubgroupsBasis` construction. This shadows the default
subspace topology `instTopologicalSpaceSubtype`. -/
@[reducible, instance 1000]
noncomputable def instTopologicalSpaceTateAlgebra [IsTateRing A] :
    TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'

@[reducible, instance 1000]
noncomputable def instIsTopologicalRingTateAlgebra [IsTateRing A] :
    IsTopologicalRing ↥(TateAlgebra A) := tateAlgebraTopology'_isTopologicalRing

@[reducible, instance 1000]
noncomputable def instUniformSpaceTateAlgebra [IsTateRing A] :
    UniformSpace ↥(TateAlgebra A) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    instTopologicalSpaceTateAlgebra
    instIsTopologicalRingTateAlgebra.to_topologicalAddGroup

@[reducible, instance 1000]
noncomputable def instIsUniformAddGroupTateAlgebra [IsTateRing A] :
    @IsUniformAddGroup ↥(TateAlgebra A) instUniformSpaceTateAlgebra _ :=
  @isUniformAddGroup_of_addCommGroup _ _ _
    instIsTopologicalRingTateAlgebra.to_topologicalAddGroup

/-- `TateAlgebra A` is a noetherian ring whenever `A` is strongly noetherian.
This is `IsStronglyNoetherian.isNoetherianRing_restricted` specialized to `k = 1`,
since `TateAlgebra A = restrictedMvPowerSeriesSubring 1 A` by definition. -/
instance [IsStronglyNoetherian A] : IsNoetherianRing ↥(TateAlgebra A) :=
  IsStronglyNoetherian.isNoetherianRing_restricted 1

omit [IsTopologicalRing A] [NonarchimedeanRing A] in
/-- In a Hausdorff adic ring, the intersection of all powers of the ideal is zero. -/
private theorem pairIdeal_iInter_eq_zero [T2Space A] (P : PairOfDefinition A) :
    ∀ b : ↥P.A₀, (∀ n : ℕ, b ∈ P.I ^ n) → b = 0 := by
  have hHausdorff : IsHausdorff P.I ↥P.A₀ :=
    (IsAdic.isHausdorff_iff P.isAdic).mpr inferInstance
  intro b hb_all
  apply hHausdorff.haus'
  intro n
  rw [SModEq.zero]
  change b ∈ P.I ^ n • (⊤ : Submodule ↥P.A₀ ↥P.A₀)
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact hb_all n

omit [IsTopologicalRing A] in
/-- `TateAlgebra A` is T2 (Hausdorff) whenever `A` is T2. Uses the canonical
Tate topology via `instTopologicalSpaceTateAlgebra`. -/
@[reducible, instance 1000]
noncomputable def instT2SpaceTateAlgebra [IsTateRing A] [T2Space A] :
    T2Space ↥(TateAlgebra A) := by
  change @T2Space _ tateAlgebraTopology'
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  haveI : IsTopologicalRing ↥(TateAlgebra A) := tateAlgebraTopology'_isTopologicalRing
  haveI : IsTopologicalAddGroup ↥(TateAlgebra A) := IsTopologicalRing.to_topologicalAddGroup
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro y hy_ne
  -- Since y ≠ 0, some coefficient is nonzero.
  obtain ⟨l, hl⟩ : ∃ l, MvPowerSeries.coeff l y.val ≠ 0 := by
    contrapose! hy_ne
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro l
    simpa using hy_ne l
  -- Find n such that `coeff l y.val ∉ image P.I^n`.
  suffices h : ∃ n, MvPowerSeries.coeff l y.val ∉
      (Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) by
    obtain ⟨n, hn⟩ := h
    refine ⟨(tateAlgNhd P n : Set _),
      tateAlgBasis'.hasBasis_nhds_zero.mem_of_mem (i := n) trivial, ?_⟩
    intro hy_mem
    obtain ⟨b, hb_mem, hb_eq⟩ := tateAlgNhd_coeff_mem P n hy_mem l
    exact hn ⟨b, hb_mem, hb_eq⟩
  -- Suppose for contradiction that coeff l y.val ∈ image P.I^n for all n.
  by_contra hall
  push Not at hall
  -- Extract a common witness b ∈ ⋂ n, P.I^n from the injectivity of Subtype.val.
  obtain ⟨b, _, hb_eq⟩ := hall 0
  have hb_all : ∀ n : ℕ, b ∈ P.I ^ n := by
    intro n
    obtain ⟨b_n, hb_n_mem, hb_n_eq⟩ := hall n
    have : b = b_n := Subtype.ext (hb_eq.trans hb_n_eq.symm)
    rw [this]; exact hb_n_mem
  -- Apply the Hausdorff intersection lemma.
  have hb_zero : b = 0 := pairIdeal_iInter_eq_zero P b hb_all
  rw [hb_zero] at hb_eq
  simp at hb_eq
  exact hl hb_eq.symm

/-! ### Completeness of `TateAlgebra A` with the natural Tate topology

We prove that `TateAlgebra A` is complete with respect to the canonical natural Tate
topology `tateAlgebraTopology'`, provided the ground ring `A` is complete and Hausdorff.

The proof uses `UniformSpace.complete_of_cauchySeq_tendsto`: since the uniformity is
countably generated (the basis `tateAlgNhd P n` is indexed by `ℕ`), it suffices to show
every Cauchy sequence converges.

Given a Cauchy sequence `u` in `TateAlgebra A`:
1. Each coefficient sequence `fun n => coeff l (u n)` is Cauchy in `A`.
2. By completeness of `A`, each coefficient sequence converges to some `c l`.
3. The limit function `c` is restricted (its coefficients tend to 0 cofinitely).
4. The sequence `u` converges to `c` in `tateAlgebraTopology'`.

Reference: Wedhorn, §8.
-/

omit [NonarchimedeanRing A] in
/-- The image of `P.I^n` under `Subtype.val : P.A₀ → A` is a closed additive subgroup
(being an open additive subgroup in a topological ring, hence clopen). -/
private theorem pow_image_isClosed (P : PairOfDefinition A) (n : ℕ) :
    IsClosed (Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) := by
  -- The image is open (P.pow_image_isOpen), hence clopen as an additive subgroup.
  -- First show it's an open set, then use that open subgroups are closed.
  have hopen := P.pow_image_isOpen n
  -- It's an additive subgroup: image of an ideal under a ring hom.
  -- Open additive subgroups of topological groups are closed.
  rw [show Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) =
    (AddSubgroup.map P.A₀.subtype.toAddMonoidHom (P.I ^ n).toAddSubgroup : Set A) from rfl]
  exact AddSubgroup.isClosed_of_isOpen _ (by
    rw [show (AddSubgroup.map P.A₀.subtype.toAddMonoidHom (P.I ^ n).toAddSubgroup : Set A) =
      Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) from rfl]
    exact hopen)

/-- The `CompleteSpace` instance for `TateAlgebra A` with the canonical natural Tate topology.

This is the main result: if `A` is a complete Hausdorff Tate ring, then `A⟨X⟩` is complete
with respect to the natural Tate topology (the `I`-adic topology on coefficients).

See Wedhorn, §8 (completeness of Tate algebras). -/
theorem tateAlgebraTopology'_completeSpace [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    @CompleteSpace ↥(TateAlgebra A)
      (@IsTopologicalAddGroup.rightUniformSpace _ _
        tateAlgebraTopology'
        (@IsTopologicalRing.to_topologicalAddGroup _ _
          tateAlgebraTopology' (tateAlgebraTopology'_isTopologicalRing))) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra A) := tateAlgebraTopology'_isTopologicalRing
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  letI uT : UniformSpace ↥(TateAlgebra A) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : @IsUniformAddGroup _ uT _ := @isUniformAddGroup_of_addCommGroup _ _ _ haddgrp
  -- Step 1: The uniformity is countably generated (basis indexed by ℕ).
  -- Since uT = rightUniformSpace, its topology equals tateAlgebraTopology' definitionally.
  -- The nhds basis {tateAlgNhd P n}_n is ℕ-indexed, hence countably generated.
  haveI : (@nhds _ τ (0 : ↥(TateAlgebra A))).IsCountablyGenerated :=
    tateAlgBasis'.hasBasis_nhds_zero.isCountablyGenerated
  haveI hcg : (@uniformity _ uT).IsCountablyGenerated :=
    @IsUniformAddGroup.uniformity_countably_generated _ uT _ _ (by
      convert ‹(@nhds _ τ (0 : ↥(TateAlgebra A))).IsCountablyGenerated›)
  -- Step 2: Use the sequential completeness criterion.
  apply @UniformSpace.complete_of_cauchySeq_tendsto _ uT hcg
  intro u hu
  -- Set up the uniform space on A: use the rightUniformSpace from the topology.
  letI uA : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : @IsUniformAddGroup A uA _ := isUniformAddGroup_of_addCommGroup
  -- The uniformity of (TateAlgebra A, uT) has a basis from tateAlgBasis'.
  -- The uniformity of (A, uA) has a basis from P.hasBasis_nhds_zero.
  -- hu_basis: the Cauchy condition in terms of tateAlgNhd.
  have hu_basis : ∀ n : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N,
      u m - u k ∈ tateAlgNhd P n := by
    intro n
    -- The set of pairs (x,y) with y - x ∈ tateAlgNhd P n is in the uniformity.
    have hmem : (fun p : ↥(TateAlgebra A) × ↥(TateAlgebra A) => p.2 - p.1) ⁻¹'
        (tateAlgNhd P n : Set _) ∈ @uniformity _ uT := by
      rw [@uniformity_eq_comap_nhds_zero' _ _ _ haddgrp]
      exact Filter.mem_comap.mpr ⟨(tateAlgNhd P n : Set _),
        tateAlgBasis'.hasBasis_nhds_zero.mem_of_mem (i := n) trivial,
        fun p hp => by simpa only [Set.mem_preimage, sub_eq_add_neg] using hp⟩
    obtain ⟨N, hN⟩ := cauchySeq_iff.mp hu _ hmem
    exact ⟨N, fun m hm k hk => by
      have h1 := hN m hm k hk
      simp only [Set.mem_preimage] at h1
      -- h1 : u k - u m ∈ tateAlgNhd P n (since preimage is p.2 - p.1 and pair is (u m, u k))
      rw [show u m - u k = -(u k - u m) from by ring]
      exact neg_mem h1⟩
  -- Step 3: For each l, the coefficient sequence is Cauchy in (A, uA).
  -- Since uA is a letI, CauchySeq will use it automatically.
  have hcoeff_cauchy : ∀ l : Fin 1 →₀ ℕ,
      CauchySeq (fun n => MvPowerSeries.coeff l (u n).val) := by
    intro l
    rw [cauchySeq_iff]
    intro V hV
    -- The uniformity on A (= uA = rightUniformSpace) is comap (· - ·) (nhds 0).
    rw [uniformity_eq_comap_nhds_zero'] at hV
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
    obtain ⟨n, _, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hW
    obtain ⟨N, hN⟩ := hu_basis n
    refine ⟨N, fun m hm k hk => ?_⟩
    have hdiff := hN m hm k hk
    obtain ⟨b, hb_mem, hb_eq⟩ := tateAlgNhd_coeff_mem P n hdiff l
    -- Goal: (coeff l (u m), coeff l (u k)) ∈ V.
    -- preimage is p.2 + -p.1, so we need coeff l (u k) - coeff l (u m) ∈ W.
    -- We have b with b = coeff l (u m - u k) = coeff l (u m) - coeff l (u k).
    -- image P.I^n is a subgroup, so -b also has image in P.I^n,
    -- and -b = coeff l (u k) - coeff l (u m).
    apply hWV
    simp only [Set.mem_preimage]
    apply hn
    refine ⟨-b, (P.I ^ n).neg_mem hb_mem, ?_⟩
    simp only [Subring.coe_neg, hb_eq]
    change -MvPowerSeries.coeff l (u m - u k).val =
      MvPowerSeries.coeff l (u k).val + -MvPowerSeries.coeff l (u m).val
    rw [show (u m - u k).val = (u m).val - (u k).val from rfl, map_sub, neg_sub,
      sub_eq_add_neg]
  -- Extract coefficient-wise limits using completeness of A.
  have hcoeff_conv : ∀ l : Fin 1 →₀ ℕ, ∃ a : A,
      Tendsto (fun n => MvPowerSeries.coeff l (u n).val) atTop (nhds a) :=
    fun l => cauchySeq_tendsto_of_complete (hcoeff_cauchy l)
  choose c hc using hcoeff_conv
  -- Step 4: The limit function c is restricted (coefficients tend to 0 cofinitely).
  have hc_restricted : MvPowerSeries.IsRestricted (fun l => c l : MvPowerSeries (Fin 1) A) := by
    -- IsRestricted means: Tendsto (fun l => f l) cofinite (nhds 0),
    -- where f is viewed as a function (Fin 1 →₀ ℕ) → A.
    -- Since our f is (fun l => c l), we need Tendsto c cofinite (nhds 0).
    change Tendsto c cofinite (nhds 0)
    rw [tendsto_nhds]
    intro U hU h0U
    rw [Filter.mem_cofinite]
    -- Extract n such that image P.I^n ⊆ U.
    obtain ⟨n, _, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp (hU.mem_nhds h0U)
    -- Since u is Cauchy, find N for this n.
    obtain ⟨N, hN⟩ := hu_basis n
    -- u N is restricted, so all but finitely many coefficients of u N are in image P.I^n.
    have hfin : ∀ᶠ l in cofinite,
        MvPowerSeries.coeff l (u N).val ∈
          (Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) :=
      tateAlgebra_coeff_eventually_in_pow P (u N) n
    -- The "bad" set for u N is finite.
    set S : Set (Fin 1 →₀ ℕ) := {l |
      MvPowerSeries.coeff l (u N).val ∉
        (Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A)}
    have hS_fin : S.Finite := hfin
    -- The "bad" set for the limit is contained in S.
    suffices hsub : {l | c l ∉ U} ⊆ S from hS_fin.subset hsub
    intro l hl
    simp only [Set.mem_setOf_eq] at hl ⊢
    -- Suppose coeff l (u N) ∈ image P.I^n. Then c l ∈ image P.I^n ⊆ U, contradiction.
    intro h_in
    apply hl; apply hn
    -- Show c l ∈ image P.I^n using closedness + eventual membership.
    apply (pow_image_isClosed P n).mem_of_tendsto (hc l)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun k hk => ?_⟩
    -- coeff l (u k) = coeff l (u N) + coeff l (u k - u N).
    -- Both terms are in image P.I^n (an additive subgroup).
    obtain ⟨b_diff, hb_diff_mem, hb_diff_eq⟩ := tateAlgNhd_coeff_mem P n (hN k hk N le_rfl) l
    obtain ⟨b_N, hb_N_mem, hb_N_eq⟩ := h_in
    refine ⟨b_N + b_diff, (P.I ^ n).add_mem hb_N_mem hb_diff_mem, ?_⟩
    push_cast
    rw [hb_N_eq, hb_diff_eq]
    simp [map_sub]
  -- Step 5: Construct the limit element of TateAlgebra A.
  let f : ↥(TateAlgebra A) := ⟨fun l => c l, hc_restricted⟩
  refine ⟨f, ?_⟩
  -- Step 6: Show u n → f in tateAlgebraTopology'.
  -- Use the basis characterization: u n → f iff ∀ k, eventually u n - f ∈ tateAlgNhd P k.
  rw [(tateAlgBasis'.hasBasis_nhds f).tendsto_right_iff]
  intro k _
  -- We need: eventually (fun n => u n ∈ {b | b - f ∈ tateAlgNhd P k}).
  rw [Filter.eventually_atTop]
  -- The key: for large enough n, all coefficients of u n - f are in image P.I^k.
  -- Then by tateAlgNhd_of_coeff_mem_principal, u n - f ∈ tateAlgNhd P k.
  -- Find N from the Cauchy condition for k.
  obtain ⟨N, hN⟩ := hu_basis k
  -- Also, for each l, coeff l (u n) → c l, so eventually coeff l (u n) - c l ∈ image P.I^k.
  -- But we need a UNIFORM N that works for ALL l simultaneously.
  -- The trick: for m ≥ N, u m - u N ∈ tateAlgNhd P k, so all coefficients of u m - u N
  -- are in image P.I^k. Taking m → ∞, all coefficients of f - u N are in image P.I^k
  -- (by closedness of image P.I^k). Then u n - f = (u n - u N) - (f - u N), and
  -- both have coefficients in image P.I^k (an additive subgroup).
  -- Actually, more directly: for n ≥ N, coeff l (u n) - c l is the limit as m → ∞ of
  -- coeff l (u n) - coeff l (u m) = coeff l (u n - u m), which for m ≥ N is in image P.I^k.
  -- By closedness, the limit coeff l (u n) - c l is also in image P.I^k.
  refine ⟨N, fun n hn => ?_⟩
  change u n - f ∈ tateAlgNhd P k
  -- First show u n - f ∈ pairSubring P (all coefficients in P.A₀).
  -- Then show all coefficients of u n - f are in image P.I^k.
  -- Then apply tateAlgNhd_of_coeff_mem_principal.
  have hcoeff_diff : ∀ l : Fin 1 →₀ ℕ,
      ∃ b : ↥P.A₀, b ∈ P.I ^ k ∧ (b : A) = MvPowerSeries.coeff l (u n - f).val := by
    intro l
    -- coeff l (u n - f) = coeff l (u n).val - c l.
    -- This equals lim_{m→∞} (coeff l (u n) - coeff l (u m)) = lim coeff l (u n - u m).
    -- For m ≥ N, u n - u m ∈ tateAlgNhd P k, so coeff l (u n - u m) ∈ image P.I^k.
    -- By closedness of image P.I^k, the limit is also in image P.I^k.
    have hcoeff_val : MvPowerSeries.coeff l (u n - f).val =
        MvPowerSeries.coeff l (u n).val - c l := by
      change MvPowerSeries.coeff l ((u n).val - f.val) =
        MvPowerSeries.coeff l (u n).val - c l
      rw [map_sub]
      simp only [MvPowerSeries.coeff_apply, f]
    -- The sequence (coeff l (u m))_m converges to c l.
    have htend : Tendsto (fun m => MvPowerSeries.coeff l (u n).val -
        MvPowerSeries.coeff l (u m).val)
        atTop (nhds (MvPowerSeries.coeff l (u n).val - c l)) :=
      tendsto_const_nhds.sub (hc l)
    -- For m ≥ N, the value is in image P.I^k (closed set).
    have hev : ∀ᶠ m in atTop,
        MvPowerSeries.coeff l (u n).val - MvPowerSeries.coeff l (u m).val ∈
          (Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) := by
      rw [Filter.eventually_atTop]
      refine ⟨N, fun m hm => ?_⟩
      obtain ⟨b, hb_mem, hb_eq⟩ := tateAlgNhd_coeff_mem P k (hN n hn m hm) l
      exact ⟨b, hb_mem, by rw [hb_eq]; simp [map_sub]⟩
    -- By closedness, the limit is in image P.I^k.
    have hlim_mem := (pow_image_isClosed P k).mem_of_tendsto htend hev
    rw [← hcoeff_val] at hlim_mem
    obtain ⟨b, hb_mem, hb_eq⟩ := hlim_mem
    exact ⟨b, hb_mem, hb_eq⟩
  -- Now we have all coefficients of u n - f in image P.I^k.
  -- Show u n - f ∈ pairSubring P.
  have hpair : (u n - f) ∈ pairSubring P := by
    intro s
    obtain ⟨b, _, hb_eq⟩ := hcoeff_diff s
    rw [← hb_eq]; exact b.property
  -- Apply reverse coefficient characterization.
  let PP := IsTateRing.principalPair A
  exact tateAlgNhd_of_coeff_mem_principal PP.toPairOfDefinition k PP.π PP.I_eq_span PP.π_isUnit
    hpair hcoeff_diff

/-! ### PairOfDefinition, algebraMap continuity, and IsTateRing for TateAlgebra A

We show that `TateAlgebra A` with `tateAlgebraTopology'` admits a pair of definition
`(pairSubring P, pairIdeal P)`, that `algebraMap A (TateAlgebra A)` is continuous,
and that `TateAlgebra A` is itself a Tate ring. -/

omit [IsTopologicalRing A] in
/-- The preimage of `tateAlgNhd P n` (as a set in `TateAlgebra A`) under the inclusion
`pairSubring P ↪ TateAlgebra A` equals `(pairIdeal P)^n` (as a set in `pairSubring P`).
This is because `tateAlgNhd P n` is exactly the image of `(pairIdeal P)^n`. -/
theorem tateAlgNhd_preimage_eq (P : PairOfDefinition A) (n : ℕ) :
    (pairSubring P).subtype ⁻¹' (tateAlgNhd P n : Set ↥(TateAlgebra A)) =
      ((pairIdeal P) ^ n : Ideal ↥(pairSubring P)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (Subtype.val_injective heq) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

omit [IsTopologicalRing A] in
/-- The subspace topology on `pairSubring P` from `tateAlgebraTopology'` equals the
`pairIdeal P`-adic topology. This is the key `isAdic` result for the pair of definition.

The proof uses `isAdic_iff`: we show that (1) each `(pairIdeal P)^n` is open in the
subspace topology, and (2) every neighborhood of `0` in the subspace topology contains
some `(pairIdeal P)^n`. Both follow from the fact that the preimage of `tateAlgNhd P n`
under the subring inclusion is exactly `(pairIdeal P)^n`. -/
theorem pairIdeal_isAdic_subspace [IsTateRing A] :
    @IsAdic ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition) _
      (@instTopologicalSpaceSubtype ↥(TateAlgebra A)
        (· ∈ (pairSubring (IsTateRing.principalPair A).toPairOfDefinition :
          Subring ↥(TateAlgebra A)))
        tateAlgebraTopology')
      (pairIdeal (IsTateRing.principalPair A).toPairOfDefinition) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra A) := tateAlgebraTopology'_isTopologicalRing
  letI τ_sub : TopologicalSpace ↥(pairSubring P) :=
    instTopologicalSpaceSubtype
  haveI hring_sub : @IsTopologicalRing ↥(pairSubring P) τ_sub _ :=
    Subring.instIsTopologicalRing (pairSubring P)
  rw [@isAdic_iff _ _ _ hring_sub]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · -- (1) Each (pairIdeal P)^n is open in the subspace topology.
    -- The preimage of tateAlgNhd P n under subtype is (pairIdeal P)^n.
    rw [show ((pairIdeal P ^ n : Ideal ↥(pairSubring P)) : Set ↥(pairSubring P)) =
      (pairSubring P).subtype ⁻¹' (tateAlgNhd P n : Set ↥(TateAlgebra A)) from
      (tateAlgNhd_preimage_eq P n).symm]
    -- tateAlgNhd P n is open in tateAlgebraTopology' (it's a basis element).
    exact isOpen_induced (tateAlgBasis'.openAddSubgroup n).isOpen'
  · -- (2) Every nhd of 0 in the subspace topology contains some (pairIdeal P)^n.
    rw [nhds_subtype_eq_comap] at hs
    obtain ⟨U, hU, hsU⟩ := Filter.mem_comap.mp hs
    rw [show (0 : ↥(pairSubring P)).val = (0 : ↥(TateAlgebra A)) from rfl] at hU
    obtain ⟨n, -, hn⟩ := tateAlgBasis'.hasBasis_nhds_zero.mem_iff.mp hU
    exact ⟨n, (tateAlgNhd_preimage_eq P n ▸ Set.preimage_mono hn).trans hsU⟩

/-- A `PairOfDefinition` for `TateAlgebra A` equipped with `tateAlgebraTopology'`.
The ring of definition is `pairSubring P = A₀⟨X⟩` and the ideal of definition is
`pairIdeal P = I · A₀⟨X⟩`, where `P = IsTateRing.principalPair A`. -/
noncomputable def tateAlgebra_pairOfDefinition [IsTateRing A] :
    @PairOfDefinition ↥(TateAlgebra A) _
      tateAlgebraTopology' := by
  letI : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  exact {
    A₀ := pairSubring (IsTateRing.principalPair A).toPairOfDefinition
    I := pairIdeal (IsTateRing.principalPair A).toPairOfDefinition
    isOpen := pairSubring_principalPair_isOpen'
    fg := pairIdeal_fg (IsTateRing.principalPair A).toPairOfDefinition
    isAdic := pairIdeal_isAdic_subspace
  }

/-- `algebraMap A (TateAlgebra A)` is continuous from A's topology to `tateAlgebraTopology'`.

Since `algebraMap a` is the constant power series `C(a)`, its `l`-th coefficient is `a`
(when `l = 0`) or `0` (otherwise). For any basic neighborhood `tateAlgNhd P n`, the
preimage under `algebraMap` contains the image of `P.I^n` in `A`, which is open. -/
theorem tateAlgebra_algebraMap_continuous [IsTateRing A] :
    @Continuous _ _ _ tateAlgebraTopology'
      (algebraMap A ↥(TateAlgebra A)) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra A) := tateAlgebraTopology'_isTopologicalRing
  -- It suffices to show continuity at 0 (for an additive group hom).
  rw [continuous_def]
  intro U hU
  -- We need to show (algebraMap A _) ⁻¹' U is open in A.
  rw [isOpen_iff_mem_nhds]
  intro a ha
  -- Since U is open and algebraMap a ∈ U, U ∈ nhds (algebraMap a).
  have hU_nhds : U ∈ @nhds _ τ (algebraMap A _ a) := hU.mem_nhds ha
  -- Translate using the basis: there exists n such that
  -- {b | b - algebraMap a ∈ tateAlgNhd P n} ⊆ U.
  obtain ⟨n, -, hn⟩ := (tateAlgBasis'.hasBasis_nhds (algebraMap A _ a)).mem_iff.mp hU_nhds
  -- Show the preimage contains the translate a + (image of P.I^n).
  -- For any a' with a' - a ∈ (image of P.I^n under Subtype.val), we have
  -- algebraMap a' - algebraMap a ∈ tateAlgNhd P n.
  apply mem_nhds_iff.mpr
  refine ⟨(fun x => x + a) '' (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)), ?_, ?_, ?_⟩
  · -- Subset: for x ∈ a + image(P.I^n), algebraMap x ∈ U.
    rintro x ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    -- Need: algebraMap (↑b + a) ∈ U, i.e., algebraMap (↑b + a) - algebraMap a ∈ tateAlgNhd P n.
    rw [Set.mem_preimage]
    apply hn
    change algebraMap A ↥(TateAlgebra A) ((b : A) + a) -
      algebraMap A ↥(TateAlgebra A) a ∈ tateAlgNhd P n
    rw [map_add, add_sub_cancel_right]
    -- algebraMap (b : A) ∈ tateAlgNhd P n.
    -- Since b ∈ P.I^n, pairConstantHom P b ∈ (pairIdeal P)^n (by map_pow + mem_map).
    refine ⟨pairConstantHom P ⟨b, b.property⟩, ?_, ?_⟩
    · rw [show (pairIdeal P) ^ n = Ideal.map (pairConstantHom P) (P.I ^ n) from by
        simp only [pairIdeal, ← Ideal.map_pow]]
      exact Ideal.mem_map_of_mem _ hb
    · apply Subtype.ext; rfl
  · -- Open: a + image(P.I^n) is open (image of an open set under translation).
    have hopen : IsOpen (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) :=
      P.pow_image_isOpen n
    exact (Homeomorph.addRight a).isOpenMap _ hopen
  · -- Membership: a ∈ a + image(P.I^n).
    exact ⟨0, ⟨0, (P.I ^ n).zero_mem, rfl⟩, by simp⟩

/-- `TateAlgebra A` with `tateAlgebraTopology'` is a Tate ring.

The Huber ring structure comes from `tateAlgebra_pairOfDefinition`. The topologically
nilpotent unit is `algebraMap π` where `π` is the generator of the principal pair of `A`:
`π` is a unit in `A`, so `algebraMap π` is a unit in `TateAlgebra A`, and `π` is
topologically nilpotent in `A`, so `algebraMap π` is topologically nilpotent in
`TateAlgebra A` by continuity of `algebraMap`. -/
theorem tateAlgebra_isTateRing [IsTateRing A] :
    @IsTateRing ↥(TateAlgebra A) _ tateAlgebraTopology' := by
  letI τ : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra A) := tateAlgebraTopology'_isTopologicalRing
  exact @IsTateRing.mk _ _ τ
    ⟨⟨tateAlgebra_pairOfDefinition⟩⟩
    (by
      obtain ⟨u, hu_nilp⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
      refine ⟨Units.map (algebraMap A ↥(TateAlgebra A) : A →* ↥(TateAlgebra A)) u, ?_⟩
      -- IsTopologicallyNilpotent (algebraMap u) in tateAlgebraTopology'.
      change @IsTopologicallyNilpotent _ _ τ
        ((Units.map (algebraMap A ↥(TateAlgebra A) : A →* ↥(TateAlgebra A)) u : ↥(TateAlgebra A)))
      change Tendsto (fun n => ((Units.map (algebraMap A ↥(TateAlgebra A) : A →* ↥(TateAlgebra A))
        u : ↥(TateAlgebra A)) ^ n)) atTop (@nhds _ τ 0)
      have hval : ∀ n : ℕ, (Units.map (algebraMap A ↥(TateAlgebra A) : A →* ↥(TateAlgebra A))
          u : ↥(TateAlgebra A)) ^ n = algebraMap A ↥(TateAlgebra A) ((u : A) ^ n) := by
        intro n
        show ((Units.map (algebraMap A ↥(TateAlgebra A) : A →* ↥(TateAlgebra A)) u :
          ↥(TateAlgebra A)) ^ n) = _
        rw [show (Units.map (algebraMap A ↥(TateAlgebra A) : A →* ↥(TateAlgebra A)) u :
          ↥(TateAlgebra A)) = algebraMap A ↥(TateAlgebra A) (u : A) from rfl, map_pow]
      simp_rw [hval]
      rw [show (0 : ↥(TateAlgebra A)) = algebraMap A ↥(TateAlgebra A) 0 from (map_zero _).symm]
      exact tateAlgebra_algebraMap_continuous.continuousAt.tendsto.comp hu_nilp)

/-! ### Phase 2.4: Apply Prop 6.17 to get ideals closed in TateAlgebra A

With the `IsTateRing (TateAlgebra A)` instance and `PairOfDefinition` in hand,
we can apply `Wedhorn.isClosed_ideal_of_noetherian` to show that ANY ideal of
`TateAlgebra A` is closed under `tateAlgebraTopology'` — in particular,
`oneSubfXIdeal s = (1 - s·X)` is closed. -/

/-- Every ideal of `TateAlgebra A` is closed under `tateAlgebraTopology'`,
given that the ring of definition `pairSubring P` is noetherian.

This is Wedhorn Prop 6.17 applied to `A = TateAlgebra A_orig`. -/
theorem tateAlgebra_isClosed_ideal [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    [IsNoetherianRing ↥(tateAlgebra_pairOfDefinition (A := A)).A₀]
    (J : Ideal ↥(TateAlgebra A)) :
    IsClosed (J : Set ↥(TateAlgebra A)) := by
  -- Wedhorn Prop 6.17 applied to TateAlgebra A.
  -- The IsClosed uses instTopologicalSpaceTateAlgebra (= tateAlgebraTopology').
  -- Prop 6.17 needs [UniformSpace] [IsUniformAddGroup] [IsTopologicalRing] [T2Space]
  -- [CompleteSpace] [IsTateRing] — all with the Tate topology.
  -- Use instUniformSpaceTateAlgebra, reconcile via IsUniformAddGroup.toUniformSpace_eq.
  haveI hCS : @CompleteSpace _ instUniformSpaceTateAlgebra :=
    tateAlgebraTopology'_completeSpace hA_complete
  haveI hTR : @IsTateRing ↥(TateAlgebra A) _ instTopologicalSpaceTateAlgebra :=
    tateAlgebra_isTateRing
  -- Prop 6.17 returns IsClosed with respect to instUniformSpaceTateAlgebra.toTopologicalSpace.
  -- This equals instTopologicalSpaceTateAlgebra because instUniformSpaceTateAlgebra was
  -- built from it via rightUniformSpace.
  -- Use convert to bridge the topology difference.
  suffices h : @IsClosed _ instUniformSpaceTateAlgebra.toTopologicalSpace (J : Set _) by
    convert h using 1
  exact @Wedhorn.isClosed_ideal_of_noetherian ↥(TateAlgebra A) _
    instUniformSpaceTateAlgebra instIsUniformAddGroupTateAlgebra
    (show @IsTopologicalRing _ instUniformSpaceTateAlgebra.toTopologicalSpace _ by
      convert instIsTopologicalRingTateAlgebra)
    (show @T2Space _ instUniformSpaceTateAlgebra.toTopologicalSpace by
      convert instT2SpaceTateAlgebra; exact ‹T2Space A›)
    hCS
    (show @IsTateRing _ _ instUniformSpaceTateAlgebra.toTopologicalSpace by
      convert hTR)
    (show @PairOfDefinition _ _ instUniformSpaceTateAlgebra.toTopologicalSpace by
      convert tateAlgebra_pairOfDefinition) ‹_› J

/-! ### Phase 2.5: Quotient A⟨X⟩/(1-sX) is complete + T2

With `tateAlgebra_isClosed_ideal` giving `(1-sX)` closed, the quotient
inherits completeness and Hausdorffness from standard Mathlib results. -/

section Phase25Quotient

/-- The ideal `(1 - fX)` in `A⟨X⟩`. No discrete topology needed. -/
noncomputable def oneSubfXIdeal (f : A) : Ideal ↥(TateAlgebra A) :=
  Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}

/-- The quotient topology on `A⟨X⟩/(1-fX)` using the canonical Tate topology on `A⟨X⟩`. -/
@[reducible]
noncomputable def quotientOneSubfXIdealTopology [IsTateRing A] (f : A) :
    TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra _
    (oneSubfXIdeal f)

/-- The quotient `A⟨X⟩/(1-fX)` is a topological ring. -/
noncomputable instance quotientOneSubfXIdealTopology_isTopologicalRing [IsTateRing A] (f : A) :
    @IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientOneSubfXIdealTopology f) _ :=
  @topologicalRing_quotient ↥(TateAlgebra A)
    instTopologicalSpaceTateAlgebra _
    (oneSubfXIdeal f) (instIsTopologicalRingTateAlgebra)

/-- The quotient `A⟨X⟩/(1-fX)` has the IsTopologicalAddGroup structure. -/
noncomputable instance quotientOneSubfXIdealTopology_isTopologicalAddGroup [IsTateRing A] (f : A) :
    @IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientOneSubfXIdealTopology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (quotientOneSubfXIdealTopology f)
    (quotientOneSubfXIdealTopology_isTopologicalRing f)

/-- The uniform space on the quotient `A⟨X⟩/(1-fX)`. -/
@[reducible, instance]
noncomputable def quotientOneSubfXIdealUniformSpace [IsTateRing A] (f : A) :
    UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (quotientOneSubfXIdealTopology f)
    (quotientOneSubfXIdealTopology_isTopologicalAddGroup f)

/-- `TateAlgebra A` is first-countable (nhds basis indexed by ℕ). -/
@[reducible, instance 1000]
noncomputable def instFirstCountableTopologyTateAlgebra [IsTateRing A] :
    FirstCountableTopology ↥(TateAlgebra A) := by
  constructor; intro a
  have h0 := (tateAlgBasis' (A := A)).hasBasis_nhds_zero.isCountablyGenerated
  rw [← map_add_left_nhds_zero a]
  exact Filter.map.isCountablyGenerated _ _

/-- The ideal `(1-sX)` is closed in `TateAlgebra A` under the canonical topology.
Corollary of `tateAlgebra_isClosed_ideal`. -/
theorem oneSubfXIdeal_isClosed [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (s : A) :
    IsClosed ((oneSubfXIdeal s : Ideal ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) := by
  haveI : IsNoetherianRing ↥(tateAlgebra_pairOfDefinition (A := A)).A₀ := hnoeth
  exact tateAlgebra_isClosed_ideal hA_complete (oneSubfXIdeal s)

/-- The quotient `A⟨X⟩/(1-sX)` is T2. -/
theorem quotient_oneSubfXIdeal_t2Space [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (s : A) :
    T2Space (↥(TateAlgebra A) ⧸ oneSubfXIdeal s) := by
  haveI : IsClosed ((oneSubfXIdeal s).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    oneSubfXIdeal_isClosed hA_complete hnoeth s
  infer_instance

/-- The quotient `A⟨X⟩/(1-sX)` is complete under the canonical quotient topology.

**Proof:** `TateAlgebra A` is complete (`tateAlgebraTopology'_completeSpace`) and
first-countable (`instFirstCountableTopologyTateAlgebra`). The ideal `(1-sX)` is
closed (`oneSubfXIdeal_isClosed`). By `QuotientAddGroup.completeSpace_right'`
(Bourbaki IX.3.1 Prop 4), the quotient of a complete first-countable topological
group by a closed normal subgroup is complete. -/
theorem quotient_oneSubfXIdeal_completeSpace [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (s : A) :
    @CompleteSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal s)
      (quotientOneSubfXIdealUniformSpace s) := by
  -- Set up the canonical topology instances on TateAlgebra A.
  letI τ : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  haveI _hring : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  -- TateAlgebra A is first-countable (basis indexed by ℕ).
  haveI : FirstCountableTopology ↥(TateAlgebra A) := instFirstCountableTopologyTateAlgebra
  -- TateAlgebra A is complete.
  haveI hCS : @CompleteSpace ↥(TateAlgebra A)
      (IsTopologicalAddGroup.rightUniformSpace ↥(TateAlgebra A)) :=
    tateAlgebraTopology'_completeSpace hA_complete
  -- (1-sX) is closed (uses hnoeth via oneSubfXIdeal_isClosed).
  haveI : IsClosed ((oneSubfXIdeal s).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    oneSubfXIdeal_isClosed hA_complete hnoeth s
  -- Apply QuotientAddGroup.completeSpace_right' (Bourbaki IX.3.1 Prop 4).
  -- The result gives CompleteSpace for rightUniformSpace on the quotient.
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra A) _ τ haddgrp ‹_›
    (oneSubfXIdeal s).toAddSubgroup inferInstance hCS

/-! #### Plus-branch principal ideal `(algebraMap f − X)` (T138)

Mirror of the `oneSubfXIdeal` block above for the principal ideal
`Ideal.span {algebraMap f − X}`, used by the `B₁_gen` Laurent quotient
in `LaurentCoverExact.lean`. The chain is identical: closed-ideal via
`tateAlgebra_isClosed_ideal`, T2 of the quotient via the standard
`T1Space (G ⧸ N)` instance pipeline, and `CompleteSpace` of the
quotient via `QuotientAddGroup.completeSpace_right'`.

Keeping this in `TateAlgebraTopology.lean` (a lighter upstream file
than `Example638.lean`) lets downstream consumers — notably
`LaurentBaireSupport.lean` — reach the `CompleteSpace` for `B₁_gen f`
without the heavier `Example638` import chain that previously caused
a `whnf` timeout in T137. -/

/-- The ideal `(algebraMap f − X)` in `A⟨X⟩`. Plus-branch analog of
`oneSubfXIdeal`. -/
noncomputable def plusFSubXIdeal (f : A) : Ideal ↥(TateAlgebra A) :=
  Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}

/-- The quotient topology on `A⟨X⟩/(algebraMap f − X)` using the canonical
Tate topology on `A⟨X⟩`. -/
@[reducible]
noncomputable def quotientPlusFSubXIdealTopology [IsTateRing A] (f : A) :
    TopologicalSpace (↥(TateAlgebra A) ⧸ plusFSubXIdeal f) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra _
    (plusFSubXIdeal f)

/-- The quotient `A⟨X⟩/(algebraMap f − X)` is a topological ring. -/
noncomputable instance quotientPlusFSubXIdealTopology_isTopologicalRing
    [IsTateRing A] (f : A) :
    @IsTopologicalRing (↥(TateAlgebra A) ⧸ plusFSubXIdeal f)
      (quotientPlusFSubXIdealTopology f) _ :=
  @topologicalRing_quotient ↥(TateAlgebra A)
    instTopologicalSpaceTateAlgebra _
    (plusFSubXIdeal f) (instIsTopologicalRingTateAlgebra)

/-- The quotient `A⟨X⟩/(algebraMap f − X)` has the `IsTopologicalAddGroup`
structure. -/
noncomputable instance quotientPlusFSubXIdealTopology_isTopologicalAddGroup
    [IsTateRing A] (f : A) :
    @IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ plusFSubXIdeal f)
      (quotientPlusFSubXIdealTopology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (quotientPlusFSubXIdealTopology f)
    (quotientPlusFSubXIdealTopology_isTopologicalRing f)

/-- The uniform space on the quotient `A⟨X⟩/(algebraMap f − X)`. -/
@[reducible, instance]
noncomputable def quotientPlusFSubXIdealUniformSpace [IsTateRing A] (f : A) :
    UniformSpace (↥(TateAlgebra A) ⧸ plusFSubXIdeal f) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (quotientPlusFSubXIdealTopology f)
    (quotientPlusFSubXIdealTopology_isTopologicalAddGroup f)

/-- The ideal `(algebraMap f − X)` is closed in `TateAlgebra A` under the
canonical Tate topology. Corollary of `tateAlgebra_isClosed_ideal`. -/
theorem plusFSubXIdeal_isClosed [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (f : A) :
    IsClosed ((plusFSubXIdeal f : Ideal ↥(TateAlgebra A)) :
      Set ↥(TateAlgebra A)) := by
  haveI : IsNoetherianRing ↥(tateAlgebra_pairOfDefinition (A := A)).A₀ := hnoeth
  exact tateAlgebra_isClosed_ideal hA_complete (plusFSubXIdeal f)

/-- The quotient `A⟨X⟩/(algebraMap f − X)` is T2. -/
theorem quotient_plusFSubXIdeal_t2Space [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (f : A) :
    T2Space (↥(TateAlgebra A) ⧸ plusFSubXIdeal f) := by
  haveI : IsClosed ((plusFSubXIdeal f).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    plusFSubXIdeal_isClosed hA_complete hnoeth f
  infer_instance

/-- The quotient `A⟨X⟩/(algebraMap f − X)` is complete under the canonical
quotient topology. Mirror of `quotient_oneSubfXIdeal_completeSpace`. -/
theorem quotient_plusFSubXIdeal_completeSpace [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (f : A) :
    @CompleteSpace (↥(TateAlgebra A) ⧸ plusFSubXIdeal f)
      (quotientPlusFSubXIdealUniformSpace f) := by
  letI τ : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  haveI _hring : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : FirstCountableTopology ↥(TateAlgebra A) := instFirstCountableTopologyTateAlgebra
  haveI hCS : @CompleteSpace ↥(TateAlgebra A)
      (IsTopologicalAddGroup.rightUniformSpace ↥(TateAlgebra A)) :=
    tateAlgebraTopology'_completeSpace hA_complete
  haveI : IsClosed ((plusFSubXIdeal f).toAddSubgroup : Set ↥(TateAlgebra A)) :=
    plusFSubXIdeal_isClosed hA_complete hnoeth f
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra A) _ τ haddgrp ‹_›
    (plusFSubXIdeal f).toAddSubgroup inferInstance hCS

end Phase25Quotient

/-! ### Bivariate Tate algebra topology foundation (T-BIV-TOP Phase 1)

Foundation for the bivariate Tate algebra `A⟨X, Y⟩ = TateAlgebra₂ A`, mirroring
the univariate `pairSubring` / `pairIdeal` / Huber-ring stack above (lines
193-290). This is Phase 1 of T013 / T-BIV-TOP and covers:

* `pairSubring₂ P` : The bivariate ring of definition `A₀⟨X, Y⟩ ⊆ A⟨X, Y⟩` of
  restricted bivariate power series with coefficients in `P.A₀`.
* `pairConstantHom₂ P` : Constant series embedding `P.A₀ →+* A₀⟨X, Y⟩`.
* `pairIdeal₂ P` : The ideal `I · A₀⟨X, Y⟩` of `A₀⟨X, Y⟩`.
* `pairIdeal₂_fg`, `pairSubring₂_isHuberRing`, `pairSubring₂_isTopologicalRing`,
  `pairSubring₂_nonarchimedean`, `pairIdeal₂_isAdic` : Huber-ring structure on
  `A₀⟨X, Y⟩` with the `I · A₀⟨X, Y⟩`-adic topology.
* `tateAlgNhd₂ P n` : The `n`-th basic `0`-neighborhood in `A⟨X, Y⟩`, defined
  as the image of `(pairIdeal₂ P)^n` under the subring inclusion.

**Phase 2-4 (deferred to a follow-up ticket)**: the full Tate topology on
`TateAlgebra₂ A` (via `RingSubgroupsBasis` + leftMul boundedness), T2/complete
instances, `tateAlgebra₂_isClosed_ideal`, bivariate quotient topology, and
`bivariateLocToQuotient_continuous`. These mirror the univariate lines 822-1558
and together constitute ~400 new lines of intricate porting from univariate
(in particular the leftMul proof chain around `tateAlgNhd_leftMul_of_principal`
and the first-countable + closed-ideal based `completeSpace` argument). -/

section TateAlgebra₂Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [NonarchimedeanRing A] [IsTopologicalRing A]

/-- The subring of `A⟨X, Y⟩` consisting of restricted bivariate power series
whose coefficients all lie in `P.A₀`. This is the bivariate analog of
`pairSubring P` and serves as the ring of definition `A₀⟨X, Y⟩`. -/
noncomputable def pairSubring₂ (P : PairOfDefinition A) :
    Subring ↥(TateAlgebra₂ A) where
  carrier := {f | ∀ s : Fin 2 →₀ ℕ,
    MvPowerSeries.coeff s f.val ∈ P.A₀}
  mul_mem' {f g} hf hg s := by
    simp only [Subring.coe_mul, MvPowerSeries.coeff_mul]
    exact P.A₀.toSubsemiring.sum_mem
      fun p _ => P.A₀.mul_mem (hf p.1) (hg p.2)
  one_mem' s := by
    simp only [OneMemClass.coe_one, MvPowerSeries.coeff_one]
    split
    · exact P.A₀.one_mem
    · exact P.A₀.zero_mem
  add_mem' {f g} hf hg s := by
    simp only [Subring.coe_add, map_add]
    exact P.A₀.add_mem (hf s) (hg s)
  zero_mem' s := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact P.A₀.zero_mem
  neg_mem' {f} hf s := by
    simp only [NegMemClass.coe_neg, map_neg]
    exact P.A₀.neg_mem (hf s)

omit [IsTopologicalRing A] in
/-- Membership in `pairSubring₂ P` means all bivariate coefficients lie in `P.A₀`. -/
theorem mem_pairSubring₂ (P : PairOfDefinition A)
    (f : ↥(TateAlgebra₂ A)) :
    f ∈ pairSubring₂ P ↔
      ∀ s : Fin 2 →₀ ℕ, MvPowerSeries.coeff s f.val ∈ P.A₀ :=
  Iff.rfl

/-- The bivariate constant power series embedding `P.A₀ →+* A₀⟨X, Y⟩`.
Sends `a ∈ A₀` to the constant restricted bivariate power series `C(a)`. -/
noncomputable def pairConstantHom₂ (P : PairOfDefinition A) :
    P.A₀ →+* pairSubring₂ P where
  toFun a := ⟨⟨MvPowerSeries.C a.val,
      MvPowerSeries.IsRestricted_algebraMap a.val⟩, by
    intro s; classical
    simp only [MvPowerSeries.coeff_C]
    split
    · exact a.2
    · exact P.A₀.zero_mem⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_mul, map_mul]))
  map_zero' := Subtype.ext (Subtype.ext (map_zero _))
  map_add' x y :=
    Subtype.ext (Subtype.ext (by
      simp [Subring.coe_add, map_add]))

/-- The ideal `I · A₀⟨X, Y⟩` inside `A₀⟨X, Y⟩`, defined as the image of `P.I`
under the bivariate constant power series embedding. Bivariate analog of
`pairIdeal P`. -/
noncomputable def pairIdeal₂ (P : PairOfDefinition A) :
    Ideal (pairSubring₂ P) :=
  Ideal.map (pairConstantHom₂ P) P.I

omit [IsTopologicalRing A] in
/-- The bivariate ideal `I · A₀⟨X, Y⟩` is finitely generated (because `I` is). -/
theorem pairIdeal₂_fg (P : PairOfDefinition A) :
    (pairIdeal₂ P).FG :=
  P.fg.map _

omit [IsTopologicalRing A] in
/-- `A₀⟨X, Y⟩ = pairSubring₂ P` with its `(I · A₀⟨X, Y⟩)`-adic topology is a
Huber ring. Bivariate analog of `pairSubring_isHuberRing`. -/
theorem pairSubring₂_isHuberRing (P : PairOfDefinition A) :
    @IsHuberRing ↥(pairSubring₂ P) _
      (pairIdeal₂ P).adicTopology :=
  isHuberRing_ofAdic _ (pairIdeal₂_fg P)

omit [IsTopologicalRing A] in
/-- The `(pairIdeal₂ P)`-adic topology on `A₀⟨X, Y⟩` is a ring topology. -/
theorem pairSubring₂_isTopologicalRing (P : PairOfDefinition A) :
    @IsTopologicalRing ↥(pairSubring₂ P)
      (pairIdeal₂ P).adicTopology _ :=
  (pairIdeal₂ P).ringFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- The `(pairIdeal₂ P)`-adic topology on `A₀⟨X, Y⟩` is nonarchimedean. -/
theorem pairSubring₂_nonarchimedean (P : PairOfDefinition A) :
    @NonarchimedeanRing ↥(pairSubring₂ P) _
      (pairIdeal₂ P).adicTopology :=
  Ideal.nonarchimedean (pairIdeal₂ P)

omit [IsTopologicalRing A] in
/-- `pairIdeal₂ P` is `I`-adic on `A₀⟨X, Y⟩` by construction. -/
theorem pairIdeal₂_isAdic (P : PairOfDefinition A) :
    @IsAdic ↥(pairSubring₂ P) _
      (pairIdeal₂ P).adicTopology (pairIdeal₂ P) :=
  rfl

/-! #### Basic neighborhoods for `TateAlgebra₂` -/

/-- The `n`-th basic neighborhood of `0` in `TateAlgebra₂ A`: the set-image of
`(pairIdeal₂ P)^n` under the inclusion `pairSubring₂ P ↪ TateAlgebra₂ A`.
Bivariate analog of `tateAlgNhd P n`. -/
noncomputable def tateAlgNhd₂ (P : PairOfDefinition A) (n : ℕ) :
    AddSubgroup ↥(TateAlgebra₂ A) :=
  ((pairIdeal₂ P) ^ n).toAddSubgroup.map
    (pairSubring₂ P).subtype.toAddMonoidHom

omit [IsTopologicalRing A] in
/-- The bivariate neighborhoods are antitone in `n`. -/
theorem tateAlgNhd₂_antitone (P : PairOfDefinition A) :
    Antitone (tateAlgNhd₂ P) :=
  fun _ _ h ↦ AddSubgroup.map_mono
    (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

omit [IsTopologicalRing A] in
/-- `0 ∈ tateAlgNhd₂ P n` for all `n`. -/
theorem zero_mem_tateAlgNhd₂ (P : PairOfDefinition A) (n : ℕ) :
    (0 : ↥(TateAlgebra₂ A)) ∈ tateAlgNhd₂ P n :=
  ⟨0, ((pairIdeal₂ P) ^ n).zero_mem, map_zero _⟩

omit [IsTopologicalRing A] in
/-- The preimage of `tateAlgNhd₂ P n` under the subring inclusion equals
`(pairIdeal₂ P)^n`. Bivariate analog of the univariate
`locNhd_preimage_eq_locIdeal_pow`-style bridge. -/
theorem tateAlgNhd₂_preimage_eq (P : PairOfDefinition A) (n : ℕ) :
    (pairSubring₂ P).subtype ⁻¹' (tateAlgNhd₂ P n : Set ↥(TateAlgebra₂ A)) =
      ((pairIdeal₂ P) ^ n : Ideal (pairSubring₂ P)) := by
  ext d
  constructor
  · rintro ⟨d', hd', heq⟩
    exact (Subtype.val_injective heq) ▸ hd'
  · intro hd
    exact ⟨d, hd, rfl⟩

omit [IsTopologicalRing A] in
/-- Multiplicative closure of bivariate neighborhoods: the product
`tateAlgNhd₂ P j · tateAlgNhd₂ P j` is contained in `tateAlgNhd₂ P i` for
`j = i + i` (or any suitable choice). Bivariate analog of `tateAlgNhd_mul`. -/
private theorem tateAlgNhd₂_mul (P : PairOfDefinition A) (i : ℕ) :
    ∃ j, (tateAlgNhd₂ P j : Set ↥(TateAlgebra₂ A)) *
      (tateAlgNhd₂ P j : Set ↥(TateAlgebra₂ A)) ⊆
        (tateAlgNhd₂ P i : Set ↥(TateAlgebra₂ A)) := by
  refine ⟨i, ?_⟩
  rintro _ ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨d₂, hd₂, rfl⟩, rfl⟩
  exact ⟨d₁ * d₂, Ideal.pow_le_pow_right (Nat.le_add_left i i)
    (pow_add (pairIdeal₂ P) i i ▸ Ideal.mul_mem_mul hd₁ hd₂),
    MulMemClass.coe_mul ..⟩

/-! #### Phase 2 Sub-task A: bivariate coefficient extraction

Bivariate analog of the univariate `coeffInIdealIdeal` / `pairIdeal_pow_le_coeffInIdeal`
chain (lines 368-510): we show that elements of `(pairIdeal₂ P)^n` have all
bivariate coefficients in the image of `P.I^n` under `Subtype.val : P.A₀ → A`.

Proofs are direct line-by-line ports from univariate, with `Fin 1 →₀ ℕ`
replaced by `Fin 2 →₀ ℕ` and the various `₂` substitutions. The only structural
change is the index type; every step relies on general `MvPowerSeries.coeff_mul`
/ `Finset.antidiagonal` / `Ideal.map_le_iff_le_comap` / `Submodule.mul_induction_on`
machinery that works for any σ. -/

/-- Bivariate auxiliary ideal: elements of `pairSubring₂ P` all of whose
bivariate coefficients lie in the image of `I : Ideal P.A₀` under
`Subtype.val : P.A₀ → A`. Bivariate analog of `coeffInIdealIdeal`. -/
noncomputable def coeffInIdealIdeal₂ (P : PairOfDefinition A) (I : Ideal P.A₀) :
    Ideal ↥(pairSubring₂ P) where
  carrier := {z | ∀ l : Fin 2 →₀ ℕ, ∃ b : P.A₀, b ∈ I ∧
    (b : A) = MvPowerSeries.coeff l z.val.val}
  zero_mem' l := ⟨0, I.zero_mem, by simp⟩
  add_mem' {z w} hz hw l := by
    obtain ⟨b_z, hb_z, heq_z⟩ := hz l
    obtain ⟨b_w, hb_w, heq_w⟩ := hw l
    refine ⟨b_z + b_w, I.add_mem hb_z hb_w, ?_⟩
    change ((b_z + b_w : P.A₀) : A) = MvPowerSeries.coeff l (z + w).val.val
    push_cast
    rw [heq_z, heq_w, ← map_add]
  smul_mem' r z hz l := by
    classical
    have hr : ∀ l_1, MvPowerSeries.coeff l_1 r.val.val ∈ P.A₀ := r.property
    let f : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) → P.A₀ := fun p =>
      ⟨MvPowerSeries.coeff p.1 r.val.val, hr p.1⟩ *
        (hz p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · refine I.sum_mem fun p _ => ?_
      exact I.mul_mem_left _ (hz p.2).choose_spec.1
    · change ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (r • z).val.val
      push_cast [f]
      change (∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 r.val.val * ((hz p.2).choose : A)) =
        MvPowerSeries.coeff l (r • z).val.val
      rw [show (r • z).val.val = r.val.val * z.val.val from rfl]
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(hz p.2).choose_spec.2]

omit [IsTopologicalRing A] in
/-- Bivariate constant series from `P.I^n` have their unique nonzero coefficient
in `P.I^n`. Bivariate analog of `pairConstantHom_mem_coeffInIdeal`. -/
private theorem pairConstantHom₂_mem_coeffInIdealIdeal₂ (P : PairOfDefinition A)
    {n : ℕ} (c : P.A₀) (hc : c ∈ P.I ^ n) :
    pairConstantHom₂ P c ∈ coeffInIdealIdeal₂ P (P.I ^ n) := by
  intro l
  classical
  by_cases hl : l = 0
  · refine ⟨c, hc, ?_⟩
    show (c : A) = MvPowerSeries.coeff l (pairConstantHom₂ P c).val.val
    subst hl
    change (c : A) = MvPowerSeries.coeff 0 (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_zero_C]
  · refine ⟨0, (P.I ^ n).zero_mem, ?_⟩
    show ((0 : P.A₀) : A) = MvPowerSeries.coeff l (pairConstantHom₂ P c).val.val
    change (0 : A) = MvPowerSeries.coeff l (MvPowerSeries.C (c : A))
    rw [MvPowerSeries.coeff_C, if_neg hl]

omit [IsTopologicalRing A] in
/-- `pairIdeal₂ P ⊆ coeffInIdealIdeal₂ P P.I`. Bivariate analog of
`pairIdeal_le_coeffInIdeal`. -/
theorem pairIdeal₂_le_coeffInIdealIdeal₂ (P : PairOfDefinition A) :
    pairIdeal₂ P ≤ coeffInIdealIdeal₂ P P.I := by
  unfold pairIdeal₂
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  change pairConstantHom₂ P c ∈ coeffInIdealIdeal₂ P P.I
  have h1 : c ∈ P.I ^ 1 := by rw [pow_one]; exact hc
  have := pairConstantHom₂_mem_coeffInIdealIdeal₂ P (n := 1) c h1
  convert this using 1
  rw [pow_one]

omit [IsTopologicalRing A] in
/-- Bivariate auxiliary ideal is compatible with ideal multiplication in `P.A₀`.
Bivariate analog of `coeffInIdealIdeal_mul_mono`. -/
theorem coeffInIdealIdeal₂_mul_mono (P : PairOfDefinition A) {I₁ I₂ : Ideal P.A₀}
    {J₁ J₂ : Ideal ↥(pairSubring₂ P)}
    (h₁ : J₁ ≤ coeffInIdealIdeal₂ P I₁) (h₂ : J₂ ≤ coeffInIdealIdeal₂ P I₂) :
    J₁ * J₂ ≤ coeffInIdealIdeal₂ P (I₁ * I₂) := by
  intro z hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb l
    classical
    have ha' : a ∈ coeffInIdealIdeal₂ P I₁ := h₁ ha
    have hb' : b ∈ coeffInIdealIdeal₂ P I₂ := h₂ hb
    let f : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) → P.A₀ := fun p =>
      (ha' p.1).choose * (hb' p.2).choose
    refine ⟨∑ p ∈ Finset.antidiagonal l, f p, ?_, ?_⟩
    · refine (I₁ * I₂).sum_mem fun p _ => ?_
      exact Ideal.mul_mem_mul (ha' p.1).choose_spec.1 (hb' p.2).choose_spec.1
    · change ((∑ p ∈ Finset.antidiagonal l, f p : P.A₀) : A) =
        MvPowerSeries.coeff l (a * b).val.val
      push_cast [f]
      change (∑ p ∈ Finset.antidiagonal l,
          ((ha' p.1).choose : A) * ((hb' p.2).choose : A)) =
        MvPowerSeries.coeff l (a * b).val.val
      rw [show (a * b).val.val = a.val.val * b.val.val from rfl]
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [(ha' p.1).choose_spec.2, (hb' p.2).choose_spec.2]
  · intro z₁ z₂ h₁' h₂' l
    obtain ⟨b₁, hb₁, heq₁⟩ := h₁' l
    obtain ⟨b₂, hb₂, heq₂⟩ := h₂' l
    refine ⟨b₁ + b₂, (I₁ * I₂).add_mem hb₁ hb₂, ?_⟩
    change ((b₁ : A) + (b₂ : A)) = MvPowerSeries.coeff l (z₁ + z₂).val.val
    rw [show (z₁ + z₂).val.val = z₁.val.val + z₂.val.val from rfl, map_add,
      ← heq₁, ← heq₂]

omit [IsTopologicalRing A] in
/-- `(pairIdeal₂ P)^n ⊆ coeffInIdealIdeal₂ P (P.I^n)`. Bivariate analog of
`pairIdeal_pow_le_coeffInIdeal`. -/
theorem pairIdeal₂_pow_le_coeffInIdealIdeal₂ (P : PairOfDefinition A) (n : ℕ) :
    (pairIdeal₂ P) ^ n ≤ coeffInIdealIdeal₂ P (P.I ^ n) := by
  induction n with
  | zero =>
    intro z _ l
    refine ⟨⟨MvPowerSeries.coeff l z.val.val, z.property l⟩, ?_, rfl⟩
    simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact coeffInIdealIdeal₂_mul_mono P ih (pairIdeal₂_le_coeffInIdealIdeal₂ P)

omit [IsTopologicalRing A] in
/-- **Bivariate Sub-task A (main result):** if `y ∈ tateAlgNhd₂ P n`, then every
bivariate coefficient of `y` lies in the image of `P.I^n` under `Subtype.val`.
Bivariate analog of `tateAlgNhd_coeff_mem`. -/
theorem tateAlgNhd₂_coeff_mem (P : PairOfDefinition A) (n : ℕ)
    {y : ↥(TateAlgebra₂ A)} (hy : y ∈ tateAlgNhd₂ P n) (l : Fin 2 →₀ ℕ) :
    ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = MvPowerSeries.coeff l y.val := by
  obtain ⟨z, hz, rfl⟩ := hy
  have := pairIdeal₂_pow_le_coeffInIdealIdeal₂ P n hz l
  change ∃ b, b ∈ P.I ^ n ∧ (b : A) =
    MvPowerSeries.coeff l ((pairSubring₂ P).subtype.toAddMonoidHom z).val
  exact this

/-! #### Phase 2 Sub-task C: bivariate restricted-series decay

Bivariate analog of `tateAlgebra_coeff_eventually_in_pow` (line 567). -/

/-- **Bivariate Sub-task C:** for `x ∈ TateAlgebra₂ A` and `n : ℕ`, eventually
every bivariate coefficient of `x` lies in `image of P.I^n` under `Subtype.val`.
Bivariate analog of `tateAlgebra_coeff_eventually_in_pow`. -/
theorem tateAlgebra₂_coeff_eventually_in_pow (P : PairOfDefinition A)
    (x : ↥(TateAlgebra₂ A)) (n : ℕ) :
    ∀ᶠ (l : Fin 2 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) := by
  have hres : Filter.Tendsto
      (fun l : Fin 2 →₀ ℕ => MvPowerSeries.coeff l x.val)
      Filter.cofinite (nhds (0 : A)) := x.property
  have hU : (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) ∈
      nhds (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem trivial
  exact hres hU

/-! #### Phase 2 Sub-task D: bivariate reverse coefficient characterization -/

omit [IsTopologicalRing A] in
/-- **Bivariate Sub-task D (principal case):** if `P.I = (π)` with `π` a unit
in `A`, and `y ∈ pairSubring₂ P` has all bivariate coefficients in the image
of `P.I^n`, then `y ∈ tateAlgNhd₂ P n`. Bivariate analog of
`tateAlgNhd_of_coeff_mem_principal`. -/
theorem tateAlgNhd₂_of_coeff_mem_principal (P : PairOfDefinition A) (n : ℕ)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    {y : ↥(TateAlgebra₂ A)} (hy_pair : y ∈ pairSubring₂ P)
    (hy_coeff : ∀ l : Fin 2 →₀ ℕ, ∃ b : P.A₀, b ∈ P.I ^ n ∧
      (b : A) = MvPowerSeries.coeff l y.val) :
    y ∈ tateAlgNhd₂ P n := by
  classical
  let πinv : A := ↑hπ_unit.unit⁻¹
  have hπinv_mul : (π : A) * πinv = 1 := hπ_unit.mul_val_inv
  have hπinv_pow : (π : A) ^ n * πinv ^ n = 1 := by
    rw [← mul_pow, hπinv_mul, one_pow]
  have hpow : (P.I ^ n : Ideal P.A₀) = Ideal.span {π ^ n} := by
    rw [hπ_gen, Ideal.span_singleton_pow]
  let g_val : ↥(TateAlgebra₂ A) := algebraMap A ↥(TateAlgebra₂ A) (πinv ^ n) * y
  have hg_in : g_val ∈ pairSubring₂ P := by
    intro l
    have hcoeff_g : MvPowerSeries.coeff l g_val.val =
        πinv ^ n * MvPowerSeries.coeff l y.val := by
      change MvPowerSeries.coeff l
        (((algebraMap A ↥(TateAlgebra₂ A)) (πinv ^ n) * y).val) = _
      change MvPowerSeries.coeff l
        ((MvPowerSeries.C (πinv ^ n) : MvPowerSeries (Fin 2) A) * y.val) = _
      rw [MvPowerSeries.coeff_C_mul]
    change MvPowerSeries.coeff l g_val.val ∈ P.A₀
    rw [hcoeff_g]
    obtain ⟨b, hb_mem, hb_eq⟩ := hy_coeff l
    rw [← hb_eq]
    rw [hpow] at hb_mem
    obtain ⟨a, ha_eq⟩ := Ideal.mem_span_singleton.mp hb_mem
    rw [ha_eq]
    change πinv ^ n * ((π ^ n * a : P.A₀) : A) ∈ P.A₀
    have : πinv ^ n * ((π ^ n * a : P.A₀) : A) = (a : A) := by
      push_cast
      rw [show πinv ^ n * ((π : A) ^ n * (a : A)) =
          ((π : A) ^ n * πinv ^ n) * (a : A) by ring,
        hπinv_pow, one_mul]
    rw [this]
    exact a.property
  let g_in_subring : ↥(pairSubring₂ P) := ⟨g_val, hg_in⟩
  have hy_eq : (⟨y, hy_pair⟩ : ↥(pairSubring₂ P)) =
      pairConstantHom₂ P (π ^ n) * g_in_subring := by
    apply Subtype.ext
    apply Subtype.ext
    ext l
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l
        ((pairConstantHom₂ P (π ^ n) * g_in_subring :
          ↥(pairSubring₂ P)) : ↥(TateAlgebra₂ A)).val
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l
        ((MvPowerSeries.C ((π : A) ^ n)) * g_val.val)
    change MvPowerSeries.coeff l y.val =
      MvPowerSeries.coeff l ((MvPowerSeries.C ((π : A) ^ n)) *
        ((MvPowerSeries.C (πinv ^ n)) * y.val))
    rw [← mul_assoc, ← map_mul, hπinv_pow, map_one, one_mul]
  refine ⟨⟨y, hy_pair⟩, ?_, rfl⟩
  rw [hy_eq]
  have hπ_in : pairConstantHom₂ P π ∈ pairIdeal₂ P := by
    unfold pairIdeal₂
    exact Ideal.mem_map_of_mem _
      (by rw [hπ_gen]; exact Ideal.mem_span_singleton_self π)
  have hπn_in : pairConstantHom₂ P (π ^ n) ∈ (pairIdeal₂ P) ^ n := by
    rw [map_pow]
    exact Ideal.pow_mem_pow hπ_in n
  exact ((pairIdeal₂ P) ^ n).mul_mem_right g_in_subring hπn_in

omit [IsTopologicalRing A] in
/-- **Bivariate easy case of leftMul:** when `x ∈ pairSubring₂ P`, multiplication
by `x` preserves the basic bivariate neighborhoods. Bivariate analog of
`tateAlgNhd_leftMul_of_mem`. -/
private theorem tateAlgNhd₂_leftMul_of_mem (P : PairOfDefinition A)
    {x : ↥(TateAlgebra₂ A)} (hx : x ∈ pairSubring₂ P) (i : ℕ) :
    (tateAlgNhd₂ P i : Set ↥(TateAlgebra₂ A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd₂ P i : Set ↥(TateAlgebra₂ A)) := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨x, hx⟩ * y, ?_, ?_⟩
  · exact ((pairIdeal₂ P) ^ i).mul_mem_left ⟨x, hx⟩ hy
  · exact MulMemClass.coe_mul ..

/-! #### Phase 2 Sub-task F: bivariate leftMul assembly (principal case) -/

/-- **Bivariate leftMul (principal case):** for a principal pair `P.I = (π)`
with `π` a unit in `A`, the condition `∃ j, x · tateAlgNhd₂ P j ⊆ tateAlgNhd₂ P i`
holds for every `x ∈ TateAlgebra₂ A` and every `i : ℕ`. Bivariate analog of
`tateAlgNhd_leftMul_of_principal`. -/
theorem tateAlgNhd₂_leftMul_of_principal [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(TateAlgebra₂ A)) (i : ℕ) :
    ∃ j, (tateAlgNhd₂ P j : Set ↥(TateAlgebra₂ A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd₂ P i : Set ↥(TateAlgebra₂ A)) := by
  classical
  have hS : ∀ᶠ (l : Fin 2 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l x.val ∈
        (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A) :=
    tateAlgebra₂_coeff_eventually_in_pow P x i
  set S : Set (Fin 2 →₀ ℕ) := {l |
    MvPowerSeries.coeff l x.val ∉
      (Subtype.val '' ((P.I ^ i : Ideal P.A₀) : Set P.A₀) : Set A)} with hS_def
  have hS_finite : S.Finite := hS
  let m_fn : (Fin 2 →₀ ℕ) → ℕ := fun (l : Fin 2 →₀ ℕ) =>
    (exists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose
  have hm_spec : ∀ (l : Fin 2 →₀ ℕ), ∀ b : P.A₀, b ∈ P.I ^ (m_fn l) →
      ∃ c : P.A₀, c ∈ P.I ^ i ∧ (c : A) = MvPowerSeries.coeff l x.val * (b : A) :=
    fun l => (exists_mul_pow_subset_pow P (MvPowerSeries.coeff l x.val) i).choose_spec
  let j : ℕ := max i (hS_finite.toFinset.sup m_fn)
  have hj_ge_i : i ≤ j := le_max_left _ _
  have hj_ge_m : ∀ l ∈ hS_finite.toFinset, m_fn l ≤ j := fun l hl =>
    le_max_of_le_right (Finset.le_sup hl)
  refine ⟨j, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  change (x * (pairSubring₂ P).subtype y) ∈ tateAlgNhd₂ P i
  have hy_coeff : ∀ l, ∃ b : P.A₀, b ∈ P.I ^ j ∧
      (b : A) = MvPowerSeries.coeff l ((pairSubring₂ P).subtype y).val :=
    pairIdeal₂_pow_le_coeffInIdealIdeal₂ P j hy
  set xy : ↥(TateAlgebra₂ A) := x * (pairSubring₂ P).subtype y with hxy_def
  have hterm : ∀ p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ),
      ∃ c : P.A₀, c ∈ P.I ^ i ∧
        (c : A) = MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
    intro p
    obtain ⟨b_p, hb_p_mem, hb_p_eq⟩ := hy_coeff p.2
    by_cases hp : p.1 ∈ S
    · have hb_lower : b_p ∈ P.I ^ (m_fn p.1) := by
        have hle : m_fn p.1 ≤ j := hj_ge_m p.1 (hS_finite.mem_toFinset.mpr hp)
        exact Ideal.pow_le_pow_right hle hb_p_mem
      obtain ⟨c, hc_mem, hc_eq⟩ := hm_spec p.1 b_p hb_lower
      refine ⟨c, hc_mem, ?_⟩
      rw [hc_eq, hb_p_eq]
      rfl
    · rw [hS_def] at hp
      simp only [Set.mem_setOf_eq, not_not] at hp
      obtain ⟨a, ha_mem, ha_eq⟩ := hp
      refine ⟨a * b_p, Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hj_ge_i hb_p_mem), ?_⟩
      push_cast
      rw [ha_eq, hb_p_eq]
      rfl
  have hxy_coeff : ∀ l, ∃ c : P.A₀, c ∈ P.I ^ i ∧
      (c : A) = MvPowerSeries.coeff l xy.val := by
    intro l
    have hcoeff : MvPowerSeries.coeff l xy.val =
        ∑ p ∈ Finset.antidiagonal l,
          MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val := by
      change MvPowerSeries.coeff l (x.val * y.val.val) = _
      rw [MvPowerSeries.coeff_mul]
    refine ⟨∑ p ∈ Finset.antidiagonal l, (hterm p).choose, ?_, ?_⟩
    · exact (P.I ^ i).sum_mem fun p _ => (hterm p).choose_spec.1
    · rw [hcoeff]
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      exact (hterm p).choose_spec.2
  have hxy_pair : xy ∈ pairSubring₂ P := by
    intro l
    obtain ⟨c, _, hc_eq⟩ := hxy_coeff l
    rw [← hc_eq]
    exact c.property
  exact tateAlgNhd₂_of_coeff_mem_principal P i π hπ_gen hπ_unit hxy_pair hxy_coeff

omit [IsTopologicalRing A] in
/-- **Bivariate leftMul condition (general form):** for every `x ∈ TateAlgebra₂ A`
and every `i : ℕ`, there exists `j` with `x · tateAlgNhd₂ P j ⊆ tateAlgNhd₂ P i`.
Bivariate analog of `tateAlgNhd_leftMul`. -/
theorem tateAlgNhd₂_leftMul [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A)))
    (x : ↥(TateAlgebra₂ A)) (i : ℕ) :
    ∃ j, (tateAlgNhd₂ P j : Set ↥(TateAlgebra₂ A)) ⊆
      (x * ·) ⁻¹' (tateAlgNhd₂ P i : Set ↥(TateAlgebra₂ A)) :=
  tateAlgNhd₂_leftMul_of_principal P π hπ_gen hπ_unit x i

/-! #### Phase 2: bivariate RingSubgroupsBasis and topology instances -/

/-- The bivariate `RingSubgroupsBasis` (principal-pair-parametrised form).
Bivariate analog of `tateAlgBasis`. -/
noncomputable def tateAlgBasis₂ [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    RingSubgroupsBasis (tateAlgNhd₂ P) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (tateAlgNhd₂_antitone P (le_max_left i j))
        (tateAlgNhd₂_antitone P (le_max_right i j))⟩)
    (tateAlgNhd₂_mul P)
    (tateAlgNhd₂_leftMul P π hπ_gen hπ_unit)

/-- The natural bivariate Tate topology on `TateAlgebra₂ A` (principal-pair form).
Bivariate analog of `tateAlgebraTopology`. -/
@[reducible] noncomputable def tateAlgebra₂Topology [IsTateRing A]
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    TopologicalSpace ↥(TateAlgebra₂ A) :=
  (tateAlgBasis₂ P π hπ_gen hπ_unit).topology

omit [IsTopologicalRing A] in
/-- The natural bivariate Tate topology is a ring topology. Bivariate analog of
`tateAlgebraTopology_isTopologicalRing`. -/
theorem tateAlgebra₂Topology_isTopologicalRing [IsTateRing A]
    (P : PairOfDefinition A) (π : P.A₀) (hπ_gen : P.I = Ideal.span {π})
    (hπ_unit : IsUnit ((π : A))) :
    @IsTopologicalRing ↥(TateAlgebra₂ A) (tateAlgebra₂Topology P π hπ_gen hπ_unit) _ :=
  (tateAlgBasis₂ P π hπ_gen hπ_unit).toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `tateAlgNhd₂ P n` is contained in `pairSubring₂ P` as a set. Bivariate analog of
`tateAlgNhd_le_pairSubring`. -/
theorem tateAlgNhd₂_le_pairSubring₂ (P : PairOfDefinition A) (n : ℕ) :
    (tateAlgNhd₂ P n : Set ↥(TateAlgebra₂ A)) ⊆
      (pairSubring₂ P : Set ↥(TateAlgebra₂ A)) := by
  rintro _ ⟨y, _, rfl⟩
  exact y.property

omit [IsTopologicalRing A] in
/-- `pairSubring₂ P` is open in `TateAlgebra₂ A` with the natural Tate topology.
Bivariate analog of `pairSubring_isOpen`. -/
theorem pairSubring₂_isOpen [IsTateRing A] (P : PairOfDefinition A)
    (π : P.A₀) (hπ_gen : P.I = Ideal.span {π}) (hπ_unit : IsUnit ((π : A))) :
    @IsOpen ↥(TateAlgebra₂ A) (tateAlgebra₂Topology P π hπ_gen hπ_unit)
      ((pairSubring₂ P : Subring ↥(TateAlgebra₂ A)) : Set ↥(TateAlgebra₂ A)) := by
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology P π hπ_gen hπ_unit
  haveI := tateAlgebra₂Topology_isTopologicalRing P π hπ_gen hπ_unit
  refine (pairSubring₂ P).toAddSubgroup.isOpen_of_mem_nhds (g := 0) ?_
  refine Filter.mem_of_superset
    ((tateAlgBasis₂ P π hπ_gen hπ_unit).hasBasis_nhds_zero.mem_of_mem (i := 1) trivial) ?_
  exact tateAlgNhd₂_le_pairSubring₂ P 1

/-! #### Unparameterised canonical bivariate Tate topology -/

/-- The canonical bivariate `RingSubgroupsBasis`, using `IsTateRing.principalPair`.
Bivariate analog of `tateAlgBasis'`. -/
noncomputable def tateAlgBasis'₂ [IsTateRing A] :
    RingSubgroupsBasis (tateAlgNhd₂ (IsTateRing.principalPair A).toPairOfDefinition) :=
  let P := IsTateRing.principalPair A
  tateAlgBasis₂ P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

/-- The canonical natural bivariate Tate topology on `TateAlgebra₂ A`.
Bivariate analog of `tateAlgebraTopology'`. -/
@[reducible] noncomputable def tateAlgebra₂Topology' [IsTateRing A] :
    TopologicalSpace ↥(TateAlgebra₂ A) :=
  tateAlgBasis'₂ (A := A).topology

omit [IsTopologicalRing A] in
/-- The canonical natural bivariate Tate topology is a ring topology.
Bivariate analog of `tateAlgebraTopology'_isTopologicalRing`. -/
theorem tateAlgebra₂Topology'_isTopologicalRing [IsTateRing A] :
    @IsTopologicalRing ↥(TateAlgebra₂ A) tateAlgebra₂Topology' _ :=
  tateAlgBasis'₂.toRingFilterBasis.isTopologicalRing

omit [IsTopologicalRing A] in
/-- `pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition` is open in the
canonical bivariate natural Tate topology. Bivariate analog of
`pairSubring_principalPair_isOpen'`. -/
theorem pairSubring₂_principalPair_isOpen' [IsTateRing A] :
    @IsOpen ↥(TateAlgebra₂ A) tateAlgebra₂Topology'
      ((pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :
        Subring ↥(TateAlgebra₂ A)) : Set ↥(TateAlgebra₂ A)) :=
  let P := IsTateRing.principalPair A
  pairSubring₂_isOpen P.toPairOfDefinition P.π P.I_eq_span P.π_isUnit

/-! #### Canonical foundational instances for `TateAlgebra₂ A` -/

/-- The canonical topology instance on `TateAlgebra₂ A` for Tate rings.
Bivariate analog of `instTopologicalSpaceTateAlgebra`. -/
@[reducible, instance 1000]
noncomputable def instTopologicalSpaceTateAlgebra₂ [IsTateRing A] :
    TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'

@[reducible, instance 1000]
noncomputable def instIsTopologicalRingTateAlgebra₂ [IsTateRing A] :
    IsTopologicalRing ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'_isTopologicalRing

@[reducible, instance 1000]
noncomputable def instUniformSpaceTateAlgebra₂ [IsTateRing A] :
    UniformSpace ↥(TateAlgebra₂ A) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    instTopologicalSpaceTateAlgebra₂
    instIsTopologicalRingTateAlgebra₂.to_topologicalAddGroup

@[reducible, instance 1000]
noncomputable def instIsUniformAddGroupTateAlgebra₂ [IsTateRing A] :
    @IsUniformAddGroup ↥(TateAlgebra₂ A) instUniformSpaceTateAlgebra₂ _ :=
  @isUniformAddGroup_of_addCommGroup _ _ _
    instIsTopologicalRingTateAlgebra₂.to_topologicalAddGroup

/-- `TateAlgebra₂ A` is a noetherian ring whenever `A` is strongly noetherian.
Bivariate analog of the univariate `IsStronglyNoetherian.isNoetherianRing_restricted 1`. -/
instance [IsStronglyNoetherian A] : IsNoetherianRing ↥(TateAlgebra₂ A) :=
  IsStronglyNoetherian.isNoetherianRing_restricted 2

/-! #### Phase 3: bivariate T2 and completeness -/

omit [IsTopologicalRing A] [NonarchimedeanRing A] in
/-- Bivariate analog of `pairIdeal_iInter_eq_zero`. In a Hausdorff adic ring,
the intersection of all powers of the ideal is zero (this is purely about
`P, A`, reused identically). -/
private theorem pairIdeal₂_iInter_eq_zero [T2Space A] (P : PairOfDefinition A) :
    ∀ b : ↥P.A₀, (∀ n : ℕ, b ∈ P.I ^ n) → b = 0 :=
  pairIdeal_iInter_eq_zero P

omit [IsTopologicalRing A] in
/-- **Bivariate T2**: `TateAlgebra₂ A` is Hausdorff under the canonical bivariate
Tate topology whenever `A` is T2. Bivariate analog of `instT2SpaceTateAlgebra`. -/
@[reducible, instance 1000]
noncomputable def instT2SpaceTateAlgebra₂ [IsTateRing A] [T2Space A] :
    T2Space ↥(TateAlgebra₂ A) := by
  change @T2Space _ tateAlgebra₂Topology'
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  haveI : IsTopologicalRing ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'_isTopologicalRing
  haveI : IsTopologicalAddGroup ↥(TateAlgebra₂ A) := IsTopologicalRing.to_topologicalAddGroup
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro y hy_ne
  obtain ⟨l, hl⟩ : ∃ l, MvPowerSeries.coeff l y.val ≠ 0 := by
    contrapose! hy_ne
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro l
    simpa using hy_ne l
  suffices h : ∃ n, MvPowerSeries.coeff l y.val ∉
      (Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) by
    obtain ⟨n, hn⟩ := h
    refine ⟨(tateAlgNhd₂ P n : Set _),
      tateAlgBasis'₂.hasBasis_nhds_zero.mem_of_mem (i := n) trivial, ?_⟩
    intro hy_mem
    obtain ⟨b, hb_mem, hb_eq⟩ := tateAlgNhd₂_coeff_mem P n hy_mem l
    exact hn ⟨b, hb_mem, hb_eq⟩
  by_contra hall
  push Not at hall
  obtain ⟨b, _, hb_eq⟩ := hall 0
  have hb_all : ∀ n : ℕ, b ∈ P.I ^ n := by
    intro n
    obtain ⟨b_n, hb_n_mem, hb_n_eq⟩ := hall n
    have : b = b_n := Subtype.ext (hb_eq.trans hb_n_eq.symm)
    rw [this]; exact hb_n_mem
  have hb_zero : b = 0 := pairIdeal₂_iInter_eq_zero P b hb_all
  rw [hb_zero] at hb_eq
  simp at hb_eq
  exact hl hb_eq.symm

/-- **Bivariate CompleteSpace**: `TateAlgebra₂ A` is complete under the canonical
bivariate Tate topology. Bivariate analog of `tateAlgebraTopology'_completeSpace`.

The proof mirrors the univariate Cauchy-diagonal construction: coefficient
sequences are Cauchy in `A`, the ground ring's completeness yields coefficient
limits, the limit function is restricted (via closedness of `P.I^n` images and
eventual-decay), and convergence follows via the `tateAlgNhd₂`-basis criterion
plus `tateAlgNhd₂_of_coeff_mem_principal`.

Reuses `pow_image_isClosed` (general, `P, A`-only) directly from univariate. -/
theorem tateAlgebra₂Topology'_completeSpace [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    @CompleteSpace ↥(TateAlgebra₂ A)
      (@IsTopologicalAddGroup.rightUniformSpace _ _
        tateAlgebra₂Topology'
        (@IsTopologicalRing.to_topologicalAddGroup _ _
          tateAlgebra₂Topology' (tateAlgebra₂Topology'_isTopologicalRing))) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'_isTopologicalRing
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra₂ A) :=
    IsTopologicalRing.to_topologicalAddGroup
  letI uT : UniformSpace ↥(TateAlgebra₂ A) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : @IsUniformAddGroup _ uT _ := @isUniformAddGroup_of_addCommGroup _ _ _ haddgrp
  haveI : (@nhds _ τ (0 : ↥(TateAlgebra₂ A))).IsCountablyGenerated :=
    tateAlgBasis'₂.hasBasis_nhds_zero.isCountablyGenerated
  haveI hcg : (@uniformity _ uT).IsCountablyGenerated :=
    @IsUniformAddGroup.uniformity_countably_generated _ uT _ _ (by
      convert ‹(@nhds _ τ (0 : ↥(TateAlgebra₂ A))).IsCountablyGenerated›)
  apply @UniformSpace.complete_of_cauchySeq_tendsto _ uT hcg
  intro u hu
  letI uA : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : @IsUniformAddGroup A uA _ := isUniformAddGroup_of_addCommGroup
  have hu_basis : ∀ n : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N,
      u m - u k ∈ tateAlgNhd₂ P n := by
    intro n
    have hmem : (fun p : ↥(TateAlgebra₂ A) × ↥(TateAlgebra₂ A) => p.2 - p.1) ⁻¹'
        (tateAlgNhd₂ P n : Set _) ∈ @uniformity _ uT := by
      rw [@uniformity_eq_comap_nhds_zero' _ _ _ haddgrp]
      exact Filter.mem_comap.mpr ⟨(tateAlgNhd₂ P n : Set _),
        tateAlgBasis'₂.hasBasis_nhds_zero.mem_of_mem (i := n) trivial,
        fun p hp => by simpa only [Set.mem_preimage, sub_eq_add_neg] using hp⟩
    obtain ⟨N, hN⟩ := cauchySeq_iff.mp hu _ hmem
    exact ⟨N, fun m hm k hk => by
      have h1 := hN m hm k hk
      simp only [Set.mem_preimage] at h1
      rw [show u m - u k = -(u k - u m) from by ring]
      exact neg_mem h1⟩
  have hcoeff_cauchy : ∀ l : Fin 2 →₀ ℕ,
      CauchySeq (fun n => MvPowerSeries.coeff l (u n).val) := by
    intro l
    rw [cauchySeq_iff]
    intro V hV
    rw [uniformity_eq_comap_nhds_zero'] at hV
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
    obtain ⟨n, _, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hW
    obtain ⟨N, hN⟩ := hu_basis n
    refine ⟨N, fun m hm k hk => ?_⟩
    have hdiff := hN m hm k hk
    obtain ⟨b, hb_mem, hb_eq⟩ := tateAlgNhd₂_coeff_mem P n hdiff l
    apply hWV
    simp only [Set.mem_preimage]
    apply hn
    refine ⟨-b, (P.I ^ n).neg_mem hb_mem, ?_⟩
    simp only [Subring.coe_neg, hb_eq]
    change -MvPowerSeries.coeff l (u m - u k).val =
      MvPowerSeries.coeff l (u k).val + -MvPowerSeries.coeff l (u m).val
    rw [show (u m - u k).val = (u m).val - (u k).val from rfl, map_sub, neg_sub,
      sub_eq_add_neg]
  have hcoeff_conv : ∀ l : Fin 2 →₀ ℕ, ∃ a : A,
      Tendsto (fun n => MvPowerSeries.coeff l (u n).val) atTop (nhds a) :=
    fun l => cauchySeq_tendsto_of_complete (hcoeff_cauchy l)
  choose c hc using hcoeff_conv
  have hc_restricted : MvPowerSeries.IsRestricted (fun l => c l : MvPowerSeries (Fin 2) A) := by
    change Tendsto c cofinite (nhds 0)
    rw [tendsto_nhds]
    intro U hU h0U
    rw [Filter.mem_cofinite]
    obtain ⟨n, _, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp (hU.mem_nhds h0U)
    obtain ⟨N, hN⟩ := hu_basis n
    have hfin : ∀ᶠ l in cofinite,
        MvPowerSeries.coeff l (u N).val ∈
          (Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) :=
      tateAlgebra₂_coeff_eventually_in_pow P (u N) n
    set S : Set (Fin 2 →₀ ℕ) := {l |
      MvPowerSeries.coeff l (u N).val ∉
        (Subtype.val '' ((P.I ^ n : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A)}
    have hS_fin : S.Finite := hfin
    suffices hsub : {l | c l ∉ U} ⊆ S from hS_fin.subset hsub
    intro l hl
    simp only [Set.mem_setOf_eq] at hl ⊢
    intro h_in
    apply hl; apply hn
    apply (pow_image_isClosed P n).mem_of_tendsto (hc l)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun k hk => ?_⟩
    obtain ⟨b_diff, hb_diff_mem, hb_diff_eq⟩ := tateAlgNhd₂_coeff_mem P n (hN k hk N le_rfl) l
    obtain ⟨b_N, hb_N_mem, hb_N_eq⟩ := h_in
    refine ⟨b_N + b_diff, (P.I ^ n).add_mem hb_N_mem hb_diff_mem, ?_⟩
    push_cast
    rw [hb_N_eq, hb_diff_eq]
    simp [map_sub]
  let f : ↥(TateAlgebra₂ A) := ⟨fun l => c l, hc_restricted⟩
  refine ⟨f, ?_⟩
  rw [(tateAlgBasis'₂.hasBasis_nhds f).tendsto_right_iff]
  intro k _
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := hu_basis k
  refine ⟨N, fun n hn => ?_⟩
  change u n - f ∈ tateAlgNhd₂ P k
  have hcoeff_diff : ∀ l : Fin 2 →₀ ℕ,
      ∃ b : ↥P.A₀, b ∈ P.I ^ k ∧ (b : A) = MvPowerSeries.coeff l (u n - f).val := by
    intro l
    have hcoeff_val : MvPowerSeries.coeff l (u n - f).val =
        MvPowerSeries.coeff l (u n).val - c l := by
      change MvPowerSeries.coeff l ((u n).val - f.val) =
        MvPowerSeries.coeff l (u n).val - c l
      rw [map_sub]
      simp only [MvPowerSeries.coeff_apply, f]
    have htend : Tendsto (fun m => MvPowerSeries.coeff l (u n).val -
        MvPowerSeries.coeff l (u m).val)
        atTop (nhds (MvPowerSeries.coeff l (u n).val - c l)) :=
      tendsto_const_nhds.sub (hc l)
    have hev : ∀ᶠ m in atTop,
        MvPowerSeries.coeff l (u n).val - MvPowerSeries.coeff l (u m).val ∈
          (Subtype.val '' ((P.I ^ k : Ideal ↥P.A₀) : Set ↥P.A₀) : Set A) := by
      rw [Filter.eventually_atTop]
      refine ⟨N, fun m hm => ?_⟩
      obtain ⟨b, hb_mem, hb_eq⟩ := tateAlgNhd₂_coeff_mem P k (hN n hn m hm) l
      exact ⟨b, hb_mem, by rw [hb_eq]; simp [map_sub]⟩
    have hlim_mem := (pow_image_isClosed P k).mem_of_tendsto htend hev
    rw [← hcoeff_val] at hlim_mem
    obtain ⟨b, hb_mem, hb_eq⟩ := hlim_mem
    exact ⟨b, hb_mem, hb_eq⟩
  have hpair : (u n - f) ∈ pairSubring₂ P := by
    intro s
    obtain ⟨b, _, hb_eq⟩ := hcoeff_diff s
    rw [← hb_eq]; exact b.property
  let PP := IsTateRing.principalPair A
  exact tateAlgNhd₂_of_coeff_mem_principal PP.toPairOfDefinition k PP.π PP.I_eq_span PP.π_isUnit
    hpair hcoeff_diff

/-! #### Phase 4: bivariate PairOfDefinition, Tate ring, closed ideals -/

omit [IsTopologicalRing A] in
/-- Bivariate analog of `pairIdeal_isAdic_subspace`: the subspace topology on
`pairSubring₂ P` equals the `pairIdeal₂ P`-adic topology. -/
theorem pairIdeal₂_isAdic_subspace [IsTateRing A] :
    @IsAdic ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition) _
      (@instTopologicalSpaceSubtype ↥(TateAlgebra₂ A)
        (· ∈ (pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :
          Subring ↥(TateAlgebra₂ A)))
        tateAlgebra₂Topology')
      (pairIdeal₂ (IsTateRing.principalPair A).toPairOfDefinition) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'_isTopologicalRing
  letI τ_sub : TopologicalSpace ↥(pairSubring₂ P) :=
    instTopologicalSpaceSubtype
  haveI hring_sub : @IsTopologicalRing ↥(pairSubring₂ P) τ_sub _ :=
    Subring.instIsTopologicalRing (pairSubring₂ P)
  rw [@isAdic_iff _ _ _ hring_sub]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [show ((pairIdeal₂ P ^ n : Ideal ↥(pairSubring₂ P)) : Set ↥(pairSubring₂ P)) =
      (pairSubring₂ P).subtype ⁻¹' (tateAlgNhd₂ P n : Set ↥(TateAlgebra₂ A)) from
      (tateAlgNhd₂_preimage_eq P n).symm]
    exact isOpen_induced (tateAlgBasis'₂.openAddSubgroup n).isOpen'
  · rw [nhds_subtype_eq_comap] at hs
    obtain ⟨U, hU, hsU⟩ := Filter.mem_comap.mp hs
    rw [show (0 : ↥(pairSubring₂ P)).val = (0 : ↥(TateAlgebra₂ A)) from rfl] at hU
    obtain ⟨n, -, hn⟩ := tateAlgBasis'₂.hasBasis_nhds_zero.mem_iff.mp hU
    exact ⟨n, (tateAlgNhd₂_preimage_eq P n ▸ Set.preimage_mono hn).trans hsU⟩

/-- A `PairOfDefinition` for `TateAlgebra₂ A` equipped with `tateAlgebra₂Topology'`.
Bivariate analog of `tateAlgebra_pairOfDefinition`. -/
noncomputable def tateAlgebra₂_pairOfDefinition [IsTateRing A] :
    @PairOfDefinition ↥(TateAlgebra₂ A) _
      tateAlgebra₂Topology' := by
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  exact {
    A₀ := pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition
    I := pairIdeal₂ (IsTateRing.principalPair A).toPairOfDefinition
    isOpen := pairSubring₂_principalPair_isOpen'
    fg := pairIdeal₂_fg (IsTateRing.principalPair A).toPairOfDefinition
    isAdic := pairIdeal₂_isAdic_subspace
  }

/-- `algebraMap A (TateAlgebra₂ A)` is continuous from A's topology to
`tateAlgebra₂Topology'`. Bivariate analog of `tateAlgebra_algebraMap_continuous`. -/
theorem tateAlgebra₂_algebraMap_continuous [IsTateRing A] :
    @Continuous _ _ _ tateAlgebra₂Topology'
      (algebraMap A ↥(TateAlgebra₂ A)) := by
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  letI τ : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'_isTopologicalRing
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have hU_nhds : U ∈ @nhds _ τ (algebraMap A _ a) := hU.mem_nhds ha
  obtain ⟨n, -, hn⟩ := (tateAlgBasis'₂.hasBasis_nhds (algebraMap A _ a)).mem_iff.mp hU_nhds
  apply mem_nhds_iff.mpr
  refine ⟨(fun x => x + a) '' (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)), ?_, ?_, ?_⟩
  · rintro x ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    rw [Set.mem_preimage]
    apply hn
    change algebraMap A ↥(TateAlgebra₂ A) ((b : A) + a) -
      algebraMap A ↥(TateAlgebra₂ A) a ∈ tateAlgNhd₂ P n
    rw [map_add, add_sub_cancel_right]
    refine ⟨pairConstantHom₂ P ⟨b, b.property⟩, ?_, ?_⟩
    · rw [show (pairIdeal₂ P) ^ n = Ideal.map (pairConstantHom₂ P) (P.I ^ n) from by
        simp only [pairIdeal₂, ← Ideal.map_pow]]
      exact Ideal.mem_map_of_mem _ hb
    · apply Subtype.ext; rfl
  · have hopen : IsOpen (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) :=
      P.pow_image_isOpen n
    exact (Homeomorph.addRight a).isOpenMap _ hopen
  · exact ⟨0, ⟨0, (P.I ^ n).zero_mem, rfl⟩, by simp⟩

/-- `TateAlgebra₂ A` with `tateAlgebra₂Topology'` is a Tate ring. Bivariate analog
of `tateAlgebra_isTateRing`. -/
theorem tateAlgebra₂_isTateRing [IsTateRing A] :
    @IsTateRing ↥(TateAlgebra₂ A) _ tateAlgebra₂Topology' := by
  letI τ : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  haveI hring : IsTopologicalRing ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'_isTopologicalRing
  exact @IsTateRing.mk _ _ τ
    ⟨⟨tateAlgebra₂_pairOfDefinition⟩⟩
    (by
      obtain ⟨u, hu_nilp⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
      refine ⟨Units.map (algebraMap A ↥(TateAlgebra₂ A) : A →* ↥(TateAlgebra₂ A)) u, ?_⟩
      change @IsTopologicallyNilpotent _ _ τ
        ((Units.map (algebraMap A ↥(TateAlgebra₂ A) : A →* ↥(TateAlgebra₂ A)) u :
          ↥(TateAlgebra₂ A)))
      change Tendsto (fun n => ((Units.map
        (algebraMap A ↥(TateAlgebra₂ A) : A →* ↥(TateAlgebra₂ A)) u :
          ↥(TateAlgebra₂ A)) ^ n)) atTop (@nhds _ τ 0)
      have hval : ∀ n : ℕ, (Units.map
          (algebraMap A ↥(TateAlgebra₂ A) : A →* ↥(TateAlgebra₂ A)) u :
            ↥(TateAlgebra₂ A)) ^ n =
          algebraMap A ↥(TateAlgebra₂ A) ((u : A) ^ n) := by
        intro n
        show ((Units.map
          (algebraMap A ↥(TateAlgebra₂ A) : A →* ↥(TateAlgebra₂ A)) u :
          ↥(TateAlgebra₂ A)) ^ n) = _
        rw [show (Units.map
          (algebraMap A ↥(TateAlgebra₂ A) : A →* ↥(TateAlgebra₂ A)) u :
          ↥(TateAlgebra₂ A)) =
            algebraMap A ↥(TateAlgebra₂ A) (u : A) from rfl, map_pow]
      simp_rw [hval]
      rw [show (0 : ↥(TateAlgebra₂ A)) =
        algebraMap A ↥(TateAlgebra₂ A) 0 from (map_zero _).symm]
      exact tateAlgebra₂_algebraMap_continuous.continuousAt.tendsto.comp hu_nilp)

/-- Every ideal of `TateAlgebra₂ A` is closed under `tateAlgebra₂Topology'`,
given the ring of definition is noetherian (Wedhorn Prop 6.17 applied to
`TateAlgebra₂ A`). Bivariate analog of `tateAlgebra_isClosed_ideal`. -/
theorem tateAlgebra₂_isClosed_ideal [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    [IsNoetherianRing ↥(tateAlgebra₂_pairOfDefinition (A := A)).A₀]
    (J : Ideal ↥(TateAlgebra₂ A)) :
    IsClosed (J : Set ↥(TateAlgebra₂ A)) := by
  haveI hCS : @CompleteSpace _ instUniformSpaceTateAlgebra₂ :=
    tateAlgebra₂Topology'_completeSpace hA_complete
  haveI hTR : @IsTateRing ↥(TateAlgebra₂ A) _ instTopologicalSpaceTateAlgebra₂ :=
    tateAlgebra₂_isTateRing
  suffices h : @IsClosed _ instUniformSpaceTateAlgebra₂.toTopologicalSpace (J : Set _) by
    convert h using 1
  exact @Wedhorn.isClosed_ideal_of_noetherian ↥(TateAlgebra₂ A) _
    instUniformSpaceTateAlgebra₂ instIsUniformAddGroupTateAlgebra₂
    (show @IsTopologicalRing _ instUniformSpaceTateAlgebra₂.toTopologicalSpace _ by
      convert instIsTopologicalRingTateAlgebra₂)
    (show @T2Space _ instUniformSpaceTateAlgebra₂.toTopologicalSpace by
      convert instT2SpaceTateAlgebra₂; exact ‹T2Space A›)
    hCS
    (show @IsTateRing _ _ instUniformSpaceTateAlgebra₂.toTopologicalSpace by
      convert hTR)
    (show @PairOfDefinition _ _ instUniformSpaceTateAlgebra₂.toTopologicalSpace by
      convert tateAlgebra₂_pairOfDefinition) ‹_› J

/-! #### Phase 4: bivariate quotient by the overlap ideal

Given `b : A`, the bivariate ideal `Ideal.span {algebraMap b - X, 1 - algebraMap b · Y}`
is finitely generated, hence closed under `tateAlgebra₂_isClosed_ideal`. The quotient
therefore inherits CompleteSpace + T2 from the analog of Phase 2.5, providing the
target uniform space for `UniformSpace.Completion.extensionHom` in
`LaurentOverlap.lean`. -/

/-- The bivariate overlap ideal `(algebraMap b - X, 1 - algebraMap b · Y)` of
`TateAlgebra₂ A`. -/
noncomputable def bivariateOverlapIdeal (b : A) : Ideal ↥(TateAlgebra₂ A) :=
  Ideal.span {algebraMap A ↥(TateAlgebra₂ A) b - TateAlgebra₂.X,
              1 - algebraMap A ↥(TateAlgebra₂ A) b * TateAlgebra₂.Y}

/-- The quotient topology on `TateAlgebra₂ A ⧸ bivariateOverlapIdeal b`. -/
@[reducible]
noncomputable def quotientBivariateOverlapIdealTopology [IsTateRing A] (b : A) :
    TopologicalSpace (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra₂ _
    (bivariateOverlapIdeal b)

/-- The bivariate overlap quotient is a topological ring. -/
noncomputable instance quotientBivariateOverlapIdealTopology_isTopologicalRing
    [IsTateRing A] (b : A) :
    @IsTopologicalRing (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b)
      (quotientBivariateOverlapIdealTopology b) _ :=
  @topologicalRing_quotient ↥(TateAlgebra₂ A)
    instTopologicalSpaceTateAlgebra₂ _
    (bivariateOverlapIdeal b) (instIsTopologicalRingTateAlgebra₂)

/-- The bivariate overlap quotient has `IsTopologicalAddGroup`. -/
noncomputable instance quotientBivariateOverlapIdealTopology_isTopologicalAddGroup
    [IsTateRing A] (b : A) :
    @IsTopologicalAddGroup (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b)
      (quotientBivariateOverlapIdealTopology b) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (quotientBivariateOverlapIdealTopology b)
    (quotientBivariateOverlapIdealTopology_isTopologicalRing b)

/-- Uniform space on the bivariate overlap quotient. -/
@[reducible, instance]
noncomputable def quotientBivariateOverlapIdealUniformSpace [IsTateRing A] (b : A) :
    UniformSpace (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (quotientBivariateOverlapIdealTopology b)
    (quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b)

/-- `TateAlgebra₂ A` is first-countable. Bivariate analog of the univariate
`instFirstCountableTopologyTateAlgebra`. -/
@[reducible, instance 1000]
noncomputable def instFirstCountableTopologyTateAlgebra₂ [IsTateRing A] :
    FirstCountableTopology ↥(TateAlgebra₂ A) := by
  constructor; intro a
  have h0 := (tateAlgBasis'₂ (A := A)).hasBasis_nhds_zero.isCountablyGenerated
  rw [← map_add_left_nhds_zero a]
  exact Filter.map.isCountablyGenerated _ _

/-- The bivariate overlap ideal is closed (via `tateAlgebra₂_isClosed_ideal`). -/
theorem bivariateOverlapIdeal_isClosed [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition))
    (b : A) :
    IsClosed ((bivariateOverlapIdeal b : Ideal ↥(TateAlgebra₂ A)) :
      Set ↥(TateAlgebra₂ A)) := by
  haveI : IsNoetherianRing ↥(tateAlgebra₂_pairOfDefinition (A := A)).A₀ := hnoeth
  exact tateAlgebra₂_isClosed_ideal hA_complete (bivariateOverlapIdeal b)

/-- The bivariate overlap quotient is T2. -/
theorem quotient_bivariateOverlapIdeal_t2Space [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition))
    (b : A) :
    T2Space (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b) := by
  haveI : IsClosed ((bivariateOverlapIdeal b).toAddSubgroup : Set ↥(TateAlgebra₂ A)) :=
    bivariateOverlapIdeal_isClosed hA_complete hnoeth b
  infer_instance

/-- The bivariate overlap quotient is complete.

Mirror of `quotient_oneSubfXIdeal_completeSpace`: `TateAlgebra₂ A` is first-countable
and complete, the ideal is closed, so `QuotientAddGroup.completeSpace_right'`
(Bourbaki IX.3.1 Prop 4) gives completeness of the quotient. -/
theorem quotient_bivariateOverlapIdeal_completeSpace [IsTateRing A] [T2Space A]
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition))
    (b : A) :
    @CompleteSpace (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b)
      (quotientBivariateOverlapIdealUniformSpace b) := by
  letI τ : TopologicalSpace ↥(TateAlgebra₂ A) := instTopologicalSpaceTateAlgebra₂
  haveI _hring : IsTopologicalRing ↥(TateAlgebra₂ A) := instIsTopologicalRingTateAlgebra₂
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra₂ A) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : FirstCountableTopology ↥(TateAlgebra₂ A) := instFirstCountableTopologyTateAlgebra₂
  haveI hCS : @CompleteSpace ↥(TateAlgebra₂ A)
      (IsTopologicalAddGroup.rightUniformSpace ↥(TateAlgebra₂ A)) :=
    tateAlgebra₂Topology'_completeSpace hA_complete
  haveI : IsClosed ((bivariateOverlapIdeal b).toAddSubgroup : Set ↥(TateAlgebra₂ A)) :=
    bivariateOverlapIdeal_isClosed hA_complete hnoeth b
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra₂ A) _ τ haddgrp ‹_›
    (bivariateOverlapIdeal b).toAddSubgroup inferInstance hCS

/-! #### Phase 4: bivariate power-boundedness helpers

Companion generator-level lemmas enabling consumers to invoke
`locTopology_continuous_lift` on the bivariate quotient: the bivariate X and Y
are power-bounded (since they lie in the bounded ring of definition
`pairSubring₂ P`), and the quotient map preserves boundedness. -/

omit [IsTopologicalRing A] in
/-- `TateAlgebra₂.X` lies in `pairSubring₂ P` for any pair of definition `P`.
Its unique nonzero coefficient is `1` (at `Finsupp.single 0 1`), which lies in
`P.A₀`. Bivariate analog of `TateAlgebra_X_mem_pairSubring`. -/
theorem TateAlgebra₂_X_mem_pairSubring₂ (P : PairOfDefinition A) :
    TateAlgebra₂.X (A := A) ∈ pairSubring₂ P := by
  intro s
  classical
  simp only [TateAlgebra₂.X]
  rw [MvPowerSeries.coeff_X]
  split
  · exact P.A₀.one_mem
  · exact P.A₀.zero_mem

omit [IsTopologicalRing A] in
/-- `TateAlgebra₂.Y` lies in `pairSubring₂ P`. Same proof as `X`, via the
analogous coefficient structure at `Finsupp.single 1 1`. -/
theorem TateAlgebra₂_Y_mem_pairSubring₂ (P : PairOfDefinition A) :
    TateAlgebra₂.Y (A := A) ∈ pairSubring₂ P := by
  intro s
  classical
  simp only [TateAlgebra₂.Y]
  rw [MvPowerSeries.coeff_X]
  split
  · exact P.A₀.one_mem
  · exact P.A₀.zero_mem

/-- `TateAlgebra₂.X` is power-bounded in `TateAlgebra₂ A` under the canonical
bivariate Tate topology. Bivariate analog of `TateAlgebra_X_isPowerBounded`. -/
theorem TateAlgebra₂_X_isPowerBounded [IsTateRing A] :
    @TopologicalRing.IsPowerBounded _ _ instTopologicalSpaceTateAlgebra₂
      (TateAlgebra₂.X (A := A)) := by
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := instTopologicalSpaceTateAlgebra₂
  haveI : IsTopologicalRing ↥(TateAlgebra₂ A) := instIsTopologicalRingTateAlgebra₂
  have hX_in : TateAlgebra₂.X (A := A) ∈
      pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :=
    TateAlgebra₂_X_mem_pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition
  have hpow : ∀ n : ℕ, TateAlgebra₂.X (A := A) ^ n ∈
      pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :=
    fun n => (pairSubring₂ _).pow_mem hX_in n
  have hbd : TopologicalRing.IsBounded
      (pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :
        Set ↥(TateAlgebra₂ A)) :=
    PairOfDefinition.isBounded_A₀
      (A := ↥(TateAlgebra₂ A)) (tateAlgebra₂_pairOfDefinition (A := A))
  exact hbd.subset (by rintro _ ⟨n, rfl⟩; exact hpow n)

/-- `TateAlgebra₂.Y` is power-bounded in `TateAlgebra₂ A`. -/
theorem TateAlgebra₂_Y_isPowerBounded [IsTateRing A] :
    @TopologicalRing.IsPowerBounded _ _ instTopologicalSpaceTateAlgebra₂
      (TateAlgebra₂.Y (A := A)) := by
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := instTopologicalSpaceTateAlgebra₂
  haveI : IsTopologicalRing ↥(TateAlgebra₂ A) := instIsTopologicalRingTateAlgebra₂
  have hY_in : TateAlgebra₂.Y (A := A) ∈
      pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :=
    TateAlgebra₂_Y_mem_pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition
  have hpow : ∀ n : ℕ, TateAlgebra₂.Y (A := A) ^ n ∈
      pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :=
    fun n => (pairSubring₂ _).pow_mem hY_in n
  have hbd : TopologicalRing.IsBounded
      (pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition :
        Set ↥(TateAlgebra₂ A)) :=
    PairOfDefinition.isBounded_A₀
      (A := ↥(TateAlgebra₂ A)) (tateAlgebra₂_pairOfDefinition (A := A))
  exact hbd.subset (by rintro _ ⟨n, rfl⟩; exact hpow n)

/-- The quotient map `TateAlgebra₂ A → TateAlgebra₂ A ⧸ bivariateOverlapIdeal b`
preserves boundedness of subsets. Bivariate analog of `IsBounded_mk_image_of_IsBounded`. -/
theorem IsBounded_mk_image_of_IsBounded_bivariate [IsTateRing A] (b : A)
    {S : Set ↥(TateAlgebra₂ A)} (hS : TopologicalRing.IsBounded S) :
    @TopologicalRing.IsBounded _ _ (quotientBivariateOverlapIdealTopology b)
      ((Ideal.Quotient.mk (bivariateOverlapIdeal b)) '' S) := by
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := instTopologicalSpaceTateAlgebra₂
  letI : IsTopologicalRing ↥(TateAlgebra₂ A) := instIsTopologicalRingTateAlgebra₂
  letI : TopologicalSpace (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b) :=
    quotientBivariateOverlapIdealTopology b
  letI : IsTopologicalRing (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b) :=
    quotientBivariateOverlapIdealTopology_isTopologicalRing b
  intro U hU
  have hcont : @Continuous _ _ instTopologicalSpaceTateAlgebra₂
      (quotientBivariateOverlapIdealTopology b)
      (Ideal.Quotient.mk (bivariateOverlapIdeal b)) :=
    continuous_quotient_mk'
  have hU_pre : (Ideal.Quotient.mk (bivariateOverlapIdeal b)) ⁻¹' U ∈
      @nhds _ instTopologicalSpaceTateAlgebra₂ (0 : ↥(TateAlgebra₂ A)) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)
  obtain ⟨V, hV, hSV⟩ := hS _ hU_pre
  obtain ⟨W, hWV, hW_open, hW_zero⟩ := _root_.mem_nhds_iff.mp hV
  have hmkW_open : IsOpen ((Ideal.Quotient.mk (bivariateOverlapIdeal b)) '' W) :=
    @QuotientRing.isOpenMap_coe _ instTopologicalSpaceTateAlgebra₂ _
      (bivariateOverlapIdeal b) instIsTopologicalRingTateAlgebra₂ _ hW_open
  refine ⟨(Ideal.Quotient.mk (bivariateOverlapIdeal b)) '' W,
    _root_.mem_nhds_iff.mpr ⟨_, le_refl _, hmkW_open, ⟨0, hW_zero, map_zero _⟩⟩, ?_⟩
  rintro _ ⟨_, ⟨s, hs, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
  change (Ideal.Quotient.mk (bivariateOverlapIdeal b)) s *
    (Ideal.Quotient.mk (bivariateOverlapIdeal b)) w ∈ U
  rw [← map_mul]
  exact hSV ⟨s, hs, w, hWV hw, rfl⟩

/-- `mk(TateAlgebra₂.X)` is power-bounded in the bivariate quotient. -/
theorem mk_X_isPowerBounded_in_bivariateOverlap [IsTateRing A] (b : A) :
    @TopologicalRing.IsPowerBounded _ _ (quotientBivariateOverlapIdealTopology b)
      ((Ideal.Quotient.mk (bivariateOverlapIdeal b)) (TateAlgebra₂.X (A := A))) := by
  have hX_pb : @TopologicalRing.IsPowerBounded _ _ instTopologicalSpaceTateAlgebra₂
      (TateAlgebra₂.X (A := A)) := TateAlgebra₂_X_isPowerBounded
  have hrange_eq : (Set.range
        ((Ideal.Quotient.mk (bivariateOverlapIdeal b)) TateAlgebra₂.X ^ · :
          ℕ → ↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b)) =
      (Ideal.Quotient.mk (bivariateOverlapIdeal b)) ''
        Set.range (TateAlgebra₂.X (A := A) ^ · : ℕ → _) := by
    ext y; constructor
    · rintro ⟨n, rfl⟩
      refine ⟨TateAlgebra₂.X ^ n, ⟨n, rfl⟩, ?_⟩
      rw [map_pow]
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_pow]⟩
  change @TopologicalRing.IsBounded _ _ (quotientBivariateOverlapIdealTopology b) _
  rw [hrange_eq]
  exact IsBounded_mk_image_of_IsBounded_bivariate b hX_pb

/-- `mk(TateAlgebra₂.Y)` is power-bounded in the bivariate quotient. -/
theorem mk_Y_isPowerBounded_in_bivariateOverlap [IsTateRing A] (b : A) :
    @TopologicalRing.IsPowerBounded _ _ (quotientBivariateOverlapIdealTopology b)
      ((Ideal.Quotient.mk (bivariateOverlapIdeal b)) (TateAlgebra₂.Y (A := A))) := by
  have hY_pb : @TopologicalRing.IsPowerBounded _ _ instTopologicalSpaceTateAlgebra₂
      (TateAlgebra₂.Y (A := A)) := TateAlgebra₂_Y_isPowerBounded
  have hrange_eq : (Set.range
        ((Ideal.Quotient.mk (bivariateOverlapIdeal b)) TateAlgebra₂.Y ^ · :
          ℕ → ↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b)) =
      (Ideal.Quotient.mk (bivariateOverlapIdeal b)) ''
        Set.range (TateAlgebra₂.Y (A := A) ^ · : ℕ → _) := by
    ext y; constructor
    · rintro ⟨n, rfl⟩
      refine ⟨TateAlgebra₂.Y ^ n, ⟨n, rfl⟩, ?_⟩
      rw [map_pow]
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_pow]⟩
  change @TopologicalRing.IsBounded _ _ (quotientBivariateOverlapIdealTopology b) _
  rw [hrange_eq]
  exact IsBounded_mk_image_of_IsBounded_bivariate b hY_pb

/-- In the bivariate quotient, `mk(algebraMap b) = mk(X)`. -/
theorem quotient_algebraMap_b_eq_X_bivariate [IsTateRing A] (b : A) :
    (Ideal.Quotient.mk (bivariateOverlapIdeal b))
        (algebraMap A ↥(TateAlgebra₂ A) b) =
      (Ideal.Quotient.mk (bivariateOverlapIdeal b)) TateAlgebra₂.X := by
  rw [Ideal.Quotient.eq]
  unfold bivariateOverlapIdeal
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- `mk(algebraMap b)` is power-bounded in the bivariate quotient (via
`mk(algebraMap b) = mk(X)` and `mk_X_isPowerBounded_in_bivariateOverlap`). -/
theorem mk_algebraMap_b_isPowerBounded_in_bivariateOverlap [IsTateRing A] (b : A) :
    @TopologicalRing.IsPowerBounded _ _ (quotientBivariateOverlapIdealTopology b)
      ((Ideal.Quotient.mk (bivariateOverlapIdeal b))
        (algebraMap A ↥(TateAlgebra₂ A) b)) := by
  rw [quotient_algebraMap_b_eq_X_bivariate]
  exact mk_X_isPowerBounded_in_bivariateOverlap b

/-- The composite `mk ∘ algebraMap : A → TateAlgebra₂ A ⧸ bivariateOverlapIdeal b`
is continuous. Bivariate analog of `mk_algebraMap_continuous_plusFSubX`. -/
theorem mk_algebraMap_continuous_bivariateOverlap [IsTateRing A] (b : A) :
    @Continuous _ _ _ (quotientBivariateOverlapIdealTopology b)
      (fun a : A => (Ideal.Quotient.mk (bivariateOverlapIdeal b))
        (algebraMap A ↥(TateAlgebra₂ A) a)) := by
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := instTopologicalSpaceTateAlgebra₂
  have h1 : Continuous (algebraMap A ↥(TateAlgebra₂ A)) :=
    tateAlgebra₂_algebraMap_continuous
  have h2 : @Continuous _ _ _ (quotientBivariateOverlapIdealTopology b)
      (Ideal.Quotient.mk (bivariateOverlapIdeal b)) := continuous_quotient_mk'
  exact h2.comp h1

/-- The canonical bivariate quotient topology is nonarchimedean (quotient of a
nonarchimedean topological ring by an additive subgroup). -/
theorem quotientBivariateOverlapIdealTopology_nonarchimedean [IsTateRing A] (b : A) :
    @NonarchimedeanRing (↥(TateAlgebra₂ A) ⧸ bivariateOverlapIdeal b) _
      (quotientBivariateOverlapIdealTopology b) := by
  haveI hNA_tate : @NonarchimedeanRing ↥(TateAlgebra₂ A) _
      instTopologicalSpaceTateAlgebra₂ :=
    tateAlgBasis'₂.nonarchimedean
  constructor; intro U hU
  have hcont : @Continuous _ _ instTopologicalSpaceTateAlgebra₂
      (quotientBivariateOverlapIdealTopology b)
      (Ideal.Quotient.mk (bivariateOverlapIdeal b)) :=
    continuous_quotient_mk'
  have hU' : (Ideal.Quotient.mk (bivariateOverlapIdeal b)) ⁻¹' (U : Set _) ∈
      @nhds _ instTopologicalSpaceTateAlgebra₂ (0 : ↥(TateAlgebra₂ A)) :=
    hcont.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, hVU⟩ := @NonarchimedeanRing.is_nonarchimedean _ _ _ hNA_tate _ hU'
  exact ⟨{
    toAddSubgroup := V.toAddSubgroup.map
      (Ideal.Quotient.mk (bivariateOverlapIdeal b)).toAddMonoidHom
    isOpen' := @QuotientRing.isOpenMap_coe _ instTopologicalSpaceTateAlgebra₂ _
      (bivariateOverlapIdeal b) instIsTopologicalRingTateAlgebra₂ _ V.isOpen
  }, fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact hVU hy⟩

/-! #### Phase 5: bivariate polynomial density (analog of
`tateAlgebra_polynomials_dense_canonical`)

For the backward-forward round trip of `example638Bivariate_equiv` we need that
finite-support ("polynomial") elements of `TateAlgebra₂ A` are dense in the
canonical bivariate Tate topology. Bivariate analog of the univariate density
`tateAlgebra_polynomials_dense_canonical` in `TopologyComparison.lean`. -/

/-- A bivariate power series whose coefficients vanish outside a finite box
`[0, N) × [0, N)` is restricted. Bivariate analog of
`isRestricted_of_eventually_zero`. -/
private theorem isRestricted₂_of_eventually_zero
    (h : MvPowerSeries (Fin 2) A) (N : ℕ)
    (hh : ∀ l : Fin 2 →₀ ℕ, N ≤ l 0 ∨ N ≤ l 1 → h l = 0) :
    MvPowerSeries.IsRestricted h := by
  change Filter.Tendsto (fun l => h l) Filter.cofinite (nhds 0)
  rw [tendsto_nhds]
  intro U hU h0U
  rw [Filter.mem_cofinite]
  -- `{l | h l ∉ U} ⊆ box {l | l 0 < N ∧ l 1 < N}`.
  -- Embed the box via `(i, j) ↦ Finsupp.single 0 i + Finsupp.single 1 j`.
  classical
  apply Set.Finite.subset
    (((Finset.range N ×ˢ Finset.range N).image
      (fun p : ℕ × ℕ => Finsupp.single (0 : Fin 2) p.1 +
        Finsupp.single (1 : Fin 2) p.2)).finite_toSet)
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Finset.coe_image, Finset.coe_product, Finset.coe_range, Set.mem_image,
    Set.mem_prod, Set.mem_Iio, Prod.exists]
  -- If `s 0 < N ∧ s 1 < N`, then `s` is in the image; exhibit it.
  by_cases h_in_box : s 0 < N ∧ s 1 < N
  · obtain ⟨h0, h1⟩ := h_in_box
    have hs_eq : Finsupp.single (0 : Fin 2) (s 0) +
        Finsupp.single (1 : Fin 2) (s 1) = s := by
      ext i
      fin_cases i <;> simp
    exact ⟨s 0, s 1, ⟨h0, h1⟩, hs_eq⟩
  · -- Otherwise `N ≤ s 0 ∨ N ≤ s 1`, so `h s = 0 ∈ U` contradicts `hs`.
    exfalso
    push Not at h_in_box
    have h_ge : N ≤ s 0 ∨ N ≤ s 1 := by omega
    exact hs (by rw [hh s h_ge]; exact h0U)

/-- The box-truncation of `g ∈ A⟨X, Y⟩` at size `N × N`: keep coefficients at
bivariate indices in `[0, N) × [0, N)`, set the rest to zero. Bivariate analog
of `truncTateC`. -/
private noncomputable def truncTateC₂ (g : ↥(TateAlgebra₂ A)) (N : ℕ) :
    ↥(TateAlgebra₂ A) :=
  ⟨fun l => if l 0 < N ∧ l 1 < N then g.val l else 0,
   isRestricted₂_of_eventually_zero _ N
    (fun l hl => by
      simp only [ite_eq_right_iff, and_imp]
      intro h0 h1
      omega)⟩

private theorem truncTateC₂_val (g : ↥(TateAlgebra₂ A)) (N : ℕ)
    (l : Fin 2 →₀ ℕ) :
    (truncTateC₂ g N).val l = if l 0 < N ∧ l 1 < N then g.val l else 0 := rfl

private theorem truncTateC₂_coeff_outside (g : ↥(TateAlgebra₂ A)) (N : ℕ)
    (l : Fin 2 →₀ ℕ) (hl : N ≤ l 0 ∨ N ≤ l 1) :
    (truncTateC₂ g N).val l = 0 := by
  simp only [truncTateC₂_val, ite_eq_right_iff, and_imp]
  intro h0 h1
  omega

/-- Polynomials (elements with box-finite support) are dense in `TateAlgebra₂ A`
for the canonical bivariate Tate topology. Bivariate analog of
`tateAlgebra_polynomials_dense_canonical`. -/
theorem tateAlgebra₂_polynomials_dense_canonical [IsTateRing A] :
    @Dense ↥(TateAlgebra₂ A) instTopologicalSpaceTateAlgebra₂
      {g | ∃ N : ℕ, ∀ n : Fin 2 →₀ ℕ, N ≤ n 0 ∨ N ≤ n 1 → g.val n = 0} := by
  classical
  let P := (IsTateRing.principalPair A).toPairOfDefinition
  intro g
  rw [@mem_closure_iff _ instTopologicalSpaceTateAlgebra₂]
  intro O hO hgO
  have hO_nhds : O ∈ @nhds _ instTopologicalSpaceTateAlgebra₂ g := hO.mem_nhds hgO
  obtain ⟨n, -, hn⟩ := (tateAlgBasis'₂ (A := A)).hasBasis_nhds g |>.mem_iff.mp hO_nhds
  -- g is restricted: all but finitely many coefficients lie in image(I^n).
  have hfin : ∀ᶠ (l : Fin 2 →₀ ℕ) in Filter.cofinite,
      MvPowerSeries.coeff l g.val ∈
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) :=
    tateAlgebra₂_coeff_eventually_in_pow P g n
  set S : Set (Fin 2 →₀ ℕ) := {l |
    MvPowerSeries.coeff l g.val ∉
      (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A)} with hS_def
  have hS_fin : S.Finite := hfin
  -- Pick N larger than all 0-th and 1-th components of "bad" indices.
  let N := max ((hS_fin.toFinset.image (· 0)).sup id)
               ((hS_fin.toFinset.image (· 1)).sup id) + 1
  refine ⟨truncTateC₂ g N, hn ?_,
    ⟨N, fun m hm => truncTateC₂_coeff_outside g N m hm⟩⟩
  -- Need: truncTateC₂ g N - g ∈ tateAlgNhd₂ P n; equals -(g - truncTateC₂ g N).
  have hdiff_pair : g - truncTateC₂ g N ∈ pairSubring₂ P := by
    intro l
    change (g.val l - (truncTateC₂ g N).val l) ∈ (P.A₀ : Set A)
    rw [truncTateC₂_val]
    by_cases hlt : l 0 < N ∧ l 1 < N
    · rw [if_pos hlt, sub_self]; exact P.A₀.zero_mem
    · rw [if_neg hlt, sub_zero]
      have hl_not_bad : l ∉ S := by
        intro hl
        have hl_fin : l ∈ hS_fin.toFinset := hS_fin.mem_toFinset.mpr hl
        have h0 : l 0 ≤ (hS_fin.toFinset.image (· 0)).sup id :=
          Finset.le_sup (f := id) (Finset.mem_image_of_mem (· 0) hl_fin)
        have h1 : l 1 ≤ (hS_fin.toFinset.image (· 1)).sup id :=
          Finset.le_sup (f := id) (Finset.mem_image_of_mem (· 1) hl_fin)
        push Not at hlt
        have hge := hlt (by omega : l 0 < N)
        omega
      rw [hS_def, Set.mem_setOf_eq, not_not] at hl_not_bad
      obtain ⟨b, _, hb_eq⟩ := hl_not_bad
      rw [show g.val l = (b : A) from hb_eq.symm]; exact b.property
  have hdiff_coeff : ∀ l, ∃ b : P.A₀, b ∈ P.I ^ n ∧
      (b : A) = MvPowerSeries.coeff l (g - truncTateC₂ g N).val := by
    intro l
    change ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = g.val l - (truncTateC₂ g N).val l
    rw [truncTateC₂_val]
    by_cases hlt : l 0 < N ∧ l 1 < N
    · rw [if_pos hlt, sub_self]
      exact ⟨0, (P.I ^ n).zero_mem, rfl⟩
    · rw [if_neg hlt, sub_zero]
      have hl_not_bad : l ∉ S := by
        intro hl
        have hl_fin : l ∈ hS_fin.toFinset := hS_fin.mem_toFinset.mpr hl
        have h0 : l 0 ≤ (hS_fin.toFinset.image (· 0)).sup id :=
          Finset.le_sup (f := id) (Finset.mem_image_of_mem (· 0) hl_fin)
        have h1 : l 1 ≤ (hS_fin.toFinset.image (· 1)).sup id :=
          Finset.le_sup (f := id) (Finset.mem_image_of_mem (· 1) hl_fin)
        push Not at hlt
        have hge := hlt (by omega : l 0 < N)
        omega
      rw [hS_def, Set.mem_setOf_eq, not_not] at hl_not_bad
      exact hl_not_bad
  have hg_diff_mem : g - truncTateC₂ g N ∈ tateAlgNhd₂ P n :=
    tateAlgNhd₂_of_coeff_mem_principal P n
      (IsTateRing.principalPair A).π
      (IsTateRing.principalPair A).I_eq_span
      (IsTateRing.principalPair A).π_isUnit
      hdiff_pair hdiff_coeff
  change truncTateC₂ g N - g ∈ tateAlgNhd₂ P n
  rw [show truncTateC₂ g N - g = -(g - truncTateC₂ g N) from by ring]
  exact neg_mem hg_diff_mem

/-! #### Polynomial decomposition of box-supported restricted series

Bivariate finite-support identity: every `g : TateAlgebra₂ A` with support in
`[0, N) × [0, N)` equals the finite sum of its monomials
`algebraMap(coeff_{i,j} g) * X^i * Y^j` over `(i, j) ∈ range N × range N`.

Used to reduce the `backward ∘ forward = id` round trip of
`example638Bivariate_equiv` to ring-hom agreement on the generators
`algebraMap B`, `TateAlgebra₂.X`, `TateAlgebra₂.Y`. -/

/-- Helper: `(algebraMap A ↥(TateAlgebra₂ A) c).val = MvPowerSeries.C c`. -/
theorem TateAlgebra₂_algebraMap_val (c : A) :
    (algebraMap A ↥(TateAlgebra₂ A) c).val = MvPowerSeries.C c := rfl

/-- Helper: `TateAlgebra₂.X.val = MvPowerSeries.X 0`. -/
theorem TateAlgebra₂_X_val :
    (TateAlgebra₂.X (A := A)).val = MvPowerSeries.X (0 : Fin 2) := rfl

/-- Helper: `TateAlgebra₂.Y.val = MvPowerSeries.X 1`. -/
theorem TateAlgebra₂_Y_val :
    (TateAlgebra₂.Y (A := A)).val = MvPowerSeries.X (1 : Fin 2) := rfl

/-- The monomial `algebraMap A _ c * X^i * Y^j` has MvPowerSeries value equal to
`monomial (single 0 i + single 1 j) c`. -/
theorem TateAlgebra₂_monomial_val (c : A) (i j : ℕ) :
    (algebraMap A ↥(TateAlgebra₂ A) c * TateAlgebra₂.X ^ i * TateAlgebra₂.Y ^ j).val =
      MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) i +
        Finsupp.single (1 : Fin 2) j) c := by
  -- Unfold .val via Subring.subtype (ring hom).
  have hval : (algebraMap A ↥(TateAlgebra₂ A) c * TateAlgebra₂.X ^ i *
        TateAlgebra₂.Y ^ j).val =
      (Subring.subtype (TateAlgebra₂ A))
        (algebraMap A ↥(TateAlgebra₂ A) c * TateAlgebra₂.X ^ i *
          TateAlgebra₂.Y ^ j) := rfl
  rw [hval, map_mul, map_mul, map_pow, map_pow]
  change MvPowerSeries.C c * MvPowerSeries.X (0 : Fin 2) ^ i *
      MvPowerSeries.X (1 : Fin 2) ^ j = _
  -- Rewrite X^k as monomial (single _ k) 1 and C c as monomial 0 c.
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_zero_eq_C_apply (a := c) |>.symm]
  -- Now: monomial 0 c * monomial (single 0 i) 1 * monomial (single 1 j) 1.
  -- Apply monomial_mul_monomial twice (associativity is fine since `*` is left-assoc).
  rw [MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial,
      zero_add, mul_one, mul_one]

/-- Coefficient of a generator-monomial: for `(i, j) ∈ ℕ × ℕ` and `c : A`,
`MvPowerSeries.coeff l (algebraMap c * X^i * Y^j).val = c * [l = single 0 i + single 1 j]`. -/
theorem TateAlgebra₂_monomial_coeff [DecidableEq (Fin 2)] (c : A) (i j : ℕ)
    (l : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff l
        (algebraMap A ↥(TateAlgebra₂ A) c * TateAlgebra₂.X ^ i *
          TateAlgebra₂.Y ^ j).val =
      if l = Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j then c else 0 := by
  rw [TateAlgebra₂_monomial_val, MvPowerSeries.coeff_monomial]

/-- For `l : Fin 2 →₀ ℕ`, `l` always decomposes as `single 0 (l 0) + single 1 (l 1)`. -/
theorem Finsupp_fin2_decomp (l : Fin 2 →₀ ℕ) :
    l = Finsupp.single (0 : Fin 2) (l 0) + Finsupp.single (1 : Fin 2) (l 1) := by
  ext i
  fin_cases i <;> simp

/-- **Polynomial decomposition:** for `g : TateAlgebra₂ A` with coefficients
vanishing outside the box `[0, N) × [0, N)`,
`g = ∑_{(i, j) ∈ range N × range N} algebraMap A _ (coeff_{i,j} g) * X^i * Y^j`. -/
theorem tateAlgebra₂_polynomial_decomp (g : ↥(TateAlgebra₂ A)) (N : ℕ)
    (hN : ∀ l : Fin 2 →₀ ℕ, N ≤ l 0 ∨ N ≤ l 1 → g.val l = 0) :
    g = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        algebraMap A ↥(TateAlgebra₂ A)
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
            Finsupp.single (1 : Fin 2) j) g.val) *
          TateAlgebra₂.X ^ i * TateAlgebra₂.Y ^ j := by
  classical
  apply Subtype.ext
  funext l
  -- Establish: RHS.val = ∑_i ∑_j monomial (single 0 i + single 1 j) c_ij.
  have hRHS_val_eq : ((∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        algebraMap A ↥(TateAlgebra₂ A)
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
            Finsupp.single (1 : Fin 2) j) g.val) *
          TateAlgebra₂.X ^ i * TateAlgebra₂.Y ^ j : ↥(TateAlgebra₂ A)).val) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) i +
          Finsupp.single (1 : Fin 2) j)
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
            Finsupp.single (1 : Fin 2) j) g.val) := by
    change (Subring.subtype _) _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => TateAlgebra₂_monomial_val _ i j
  rw [hRHS_val_eq]
  -- Compute the value at l via Finset.sum_apply' + coeff_monomial.
  -- (∑_i ∑_j monomial_ij c_ij) l = ∑_i ∑_j (monomial_ij c_ij) l
  -- = ∑_i ∑_j (if l = key_ij then c_ij else 0).
  have hsum_val : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) i +
          Finsupp.single (1 : Fin 2) j)
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
            Finsupp.single (1 : Fin 2) j) g.val)) l =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (if l = Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j then
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
            Finsupp.single (1 : Fin 2) j) g.val
        else 0) := by
    -- MvPowerSeries.coeff is a LinearMap; use `map_sum` + `coeff_apply` identity.
    rw [(MvPowerSeries.coeff_apply (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) i +
          Finsupp.single (1 : Fin 2) j)
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
            Finsupp.single (1 : Fin 2) j) g.val)) l).symm, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => MvPowerSeries.coeff_monomial _ _ _
  rw [hsum_val]
  -- Split cases on whether l is in the box.
  by_cases hl : l 0 < N ∧ l 1 < N
  · obtain ⟨h0, h1⟩ := hl
    rw [Finset.sum_eq_single (l 0)]
    · rw [Finset.sum_eq_single (l 1)]
      · rw [if_pos (Finsupp_fin2_decomp l)]
        rw [← Finsupp_fin2_decomp l]
        rfl
      · intros j _ hj
        rw [if_neg]
        intro heq
        apply hj
        have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq
        simp at this
        exact this.symm
      · intro h
        exfalso; exact h (Finset.mem_range.mpr h1)
    · intros i _ hi
      apply Finset.sum_eq_zero
      intros j _
      rw [if_neg]
      intro heq
      apply hi
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
      simp at this
      exact this.symm
    · intro h
      exfalso; exact h (Finset.mem_range.mpr h0)
  · push Not at hl
    have hN_apply : g.val l = 0 := hN l (by omega)
    rw [hN_apply]
    symm
    apply Finset.sum_eq_zero
    intros i hi
    apply Finset.sum_eq_zero
    intros j hj
    rw [if_neg]
    intro heq
    have h_l_i : l 0 = i := by
      simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
    have h_l_j : l 1 = j := by
      simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq
    have h_i_lt : i < N := Finset.mem_range.mp hi
    have h_j_lt : j < N := Finset.mem_range.mp hj
    rw [h_l_i] at hl
    have : N ≤ l 1 := hl h_i_lt
    rw [h_l_j] at this
    exact absurd this (Nat.not_le.mpr h_j_lt)

end TateAlgebra₂Topology

/-! ### Phase 2.6 note

The continuity and dense range theorems for `locToQuotientOneSubfX_gen` with the
canonical topology cannot live in this file due to import dependencies:
`locToQuotientOneSubfX_gen` and `RationalLocData` are defined in
`PresheafIdentification.lean`, which transitively imports this file (via
`TateAlgebraWedhorn`). These theorems are therefore placed in
`TopologyComparison.lean`, which already imports `PresheafIdentification`.

See:
- `locToQuotientOneSubfX_gen_continuous_canonical` in `TopologyComparison.lean`
- `locToQuotientOneSubfX_gen_denseRange_canonical` in `TopologyComparison.lean`
-/

end TateAlgebraNaturalTopology

end TateAlgebra
