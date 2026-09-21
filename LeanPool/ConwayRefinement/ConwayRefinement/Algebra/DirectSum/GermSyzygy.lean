/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.OrdinalGenerators
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.HomogeneousSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermPolynomial

/-!
# Homogeneous tuples over an ordinal-graded algebra

A tuple `u` indexed by `B` is homogeneous of degree `d` relative to degrees `λ_b` when `u_b`
sits in degree `β` for the `β` with `β ⊕ λ_b = d`, and vanishes when
`λ_b \not\preccurlyeq d` in the
algebraic order.

The one substantial statement here is that a homogeneous tuple lying in the span of finitely many
homogeneous tuples has homogeneous coefficients: take the graded component of each coefficient at
the degree forced by the equation. That is bookkeeping about the grading, with nothing about
derivations or about where the entries live, and both the real-exponent development and the
Cantor–Bendixson germ argument uses it.

The ordinal degrees may lie in any universe.
-/

universe u v w z

open DirectSum

public noncomputable section

namespace OrdinalGraded

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]
variable {A : NatOrdinal.{z} → Submodule K R} [GradedAlgebra A]
variable {B : Type w}

variable (A) in
/-- A tuple `u` is homogeneous of degree `d` relative to the degrees `λ_b`: `u_b` sits in degree
`β` for the `β` with `β + λ_b = d`, and is zero when `λ_b` does not precede `d` in the
algebraic order. -/
def IsHomogeneousTuple (lam : B → NatOrdinal.{z}) (u : B → R) (d : NatOrdinal.{z}) : Prop :=
  ∀ b, (∀ β, β + lam b = d → u b ∈ A β) ∧ ((¬ ∃ β, β + lam b = d) → u b = 0)

omit [GradedAlgebra A] in
theorem isHomogeneousTuple_iff {lam : B → NatOrdinal.{z}} {u : B → R} {d : NatOrdinal.{z}} :
    IsHomogeneousTuple A lam u d ↔
      ∀ b, (∀ β, β + lam b = d → u b ∈ A β) ∧
        ((¬ ∃ β, β + lam b = d) → u b = 0) :=
  Iff.rfl

omit [GradedAlgebra A] in
theorem isHomogeneousTuple_zero (lam : B → NatOrdinal.{z}) (d : NatOrdinal.{z}) :
    IsHomogeneousTuple A lam (0 : B → R) d :=
  fun _ ↦ ⟨fun _ _ ↦ zero_mem _, fun _ ↦ rfl⟩

omit [GradedAlgebra A] in
theorem IsHomogeneousTuple.mem {lam : B → NatOrdinal.{z}} {u : B → R} {d : NatOrdinal.{z}}
    (hu : IsHomogeneousTuple A lam u d) {b : B} {β : NatOrdinal.{z}} (hβ : β + lam b = d) :
    u b ∈ A β :=
  (hu b).1 β hβ

omit [GradedAlgebra A] in
theorem IsHomogeneousTuple.eq_zero {lam : B → NatOrdinal.{z}} {u : B → R} {d : NatOrdinal.{z}}
    (hu : IsHomogeneousTuple A lam u d) {b : B} (h : ¬ ∃ β, β + lam b = d) : u b = 0 :=
  (hu b).2 h

/-- **Homogeneous coefficients along homogeneous generators.** A homogeneous tuple `w` of degree
`d` in the span of a finite set `T` of homogeneous tuples is `∑ a_τ • τ` with each `a_τ`
homogeneous of the degree forced by the equation, and zero when there is none. -/
theorem exists_eq_sum_smul_of_mem_span {lam : B → NatOrdinal.{z}} {T : Finset (B → R)}
    {eT : (B → R) → NatOrdinal.{z}} (hT : ∀ τ ∈ T, IsHomogeneousTuple A lam τ (eT τ))
    {w : B → R} {d : NatOrdinal.{z}} (hw : IsHomogeneousTuple A lam w d)
    (hwN : w ∈ Submodule.span R (T : Set (B → R))) :
    ∃ a : (B → R) → R,
      (∀ τ ∈ T, (∀ ρ, ρ + eT τ = d → a τ ∈ A ρ) ∧
        ((¬ ∃ ρ, ρ + eT τ = d) → a τ = 0)) ∧
      w = ∑ τ ∈ T, a τ • τ := by
  classical
  obtain ⟨r, _, hr⟩ := Submodule.mem_span_finset.mp hwN
  refine ⟨fun τ ↦ if h : ∃ ρ, ρ + eT τ = d then
      (decompose A (r τ) (Classical.choose h) : R) else 0,
    fun τ _ ↦ ⟨fun ρ hρ ↦ ?_, fun h ↦ dif_neg h⟩, ?_⟩
  · have h : ∃ ρ, ρ + eT τ = d := ⟨ρ, hρ⟩
    have hρ' : ∀ h' : ∃ ρ, ρ + eT τ = d, Classical.choose h' = ρ := fun h' ↦
      add_right_cancel ((Classical.choose_spec h').trans hρ.symm)
    beta_reduce
    rw [dif_pos h, hρ']
    exact (decompose A (r τ) ρ).2
  · funext b
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hb : ∃ β, β + lam b = d
    · obtain ⟨β, hβ⟩ := hb
      -- take the degree-`β` component of `w b = ∑ r τ * τ b`
      have hwb : w b = (decompose A (w b) β : R) := (decompose_of_mem_same _ (hw.mem hβ)).symm
      rw [hwb, ← hr, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← GradedRing.proj_apply, map_sum]
      refine Finset.sum_congr rfl fun τ hτ ↦ ?_
      rw [GradedRing.proj_apply]
      by_cases hτb : ∃ β', β' + lam b = eT τ
      · obtain ⟨β', hβ'⟩ := hτb
        have hmem : τ b ∈ A β' := (hT τ hτ).mem hβ'
        rw [mul_comm, OrdinalGraded.coe_decompose_mul_of_left_mem hmem (r τ) β]
        -- `ρ + β' = β` exactly when `ρ + e_τ = d`
        have hiff : (∃ ρ, ρ + β' = β) ↔ ∃ ρ, ρ + eT τ = d := by
          constructor
          · rintro ⟨ρ, hρ⟩
            exact ⟨ρ, by rw [← hβ', ← add_assoc, hρ, hβ]⟩
          · rintro ⟨ρ, hρ⟩
            refine ⟨ρ, add_right_cancel (b := lam b) ?_⟩
            rw [add_assoc, hβ', hρ, hβ]
        by_cases h1 : ∃ ρ, ρ + β' = β
        · have h2 : ∃ ρ, ρ + eT τ = d := hiff.mp h1
          have hch : Classical.choose h1 = Classical.choose h2 := by
            refine add_right_cancel (b := β') ?_
            rw [Classical.choose_spec h1]
            refine add_right_cancel (b := lam b) ?_
            rw [add_assoc, hβ', Classical.choose_spec h2, hβ]
          rw [dif_pos h1, dif_pos h2, hch, mul_comm]
        · have h2 : ¬ ∃ ρ, ρ + eT τ = d := fun h ↦ h1 (hiff.mpr h)
          rw [dif_neg h1, dif_neg h2, zero_mul]
      · rw [(hT τ hτ).eq_zero hτb, mul_zero, ← GradedRing.proj_apply, map_zero, mul_zero]
    · -- no degree is forced: both sides vanish
      rw [hw.eq_zero hb]
      symm
      refine Finset.sum_eq_zero fun τ hτ ↦ ?_
      by_cases hτb : ∃ β', β' + lam b = eT τ
      · obtain ⟨β', hβ'⟩ := hτb
        have h2 : ¬ ∃ ρ, ρ + eT τ = d := fun ⟨ρ, hρ⟩ ↦
          hb ⟨ρ + β', by rw [add_assoc, hβ', hρ]⟩
        beta_reduce
        rw [dif_neg h2, zero_mul]
      · rw [(hT τ hτ).eq_zero hτb, mul_zero]

section Induction

variable {T : Type*} {l : Filter T} {Δ : Derivation K R (Filter.Germ l R)}
variable {B : Type w} [Fintype B] {c : B → R} {lam : B → NatOrdinal.{z}}

open Filter

/-- The germ of a pointwise finite sum is the sum of the germs. -/
theorem germ_coe_sum {ι' : Type*} (s : Finset ι') (f : ι' → T → R) :
    ((fun t ↦ ∑ i ∈ s, f i t : T → R) : Germ l R) =
      ∑ i ∈ s, ((f i : T → R) : Germ l R) := by
  have hfun : (fun t ↦ ∑ i ∈ s, f i t : T → R) = ∑ i ∈ s, f i := by
    ext t
    simp only [Finset.sum_apply]
  rw [hfun]
  exact map_sum (Filter.Germ.coeRingHom l) f s

variable (A Δ lam) in
/-- What the successor induction needs from the setting. A homogeneous tuple of successor degree
has a derivative representative supported on some set, homogeneous one degree lower; and values
prescribed homogeneously on that set are themselves derivatives, vanishing off it.

Over the real line this is the `ω`-sequence of cutoffs together with the image theorem for
derivatives; for the Cantor–Bendixson construction it is an exact-rank set together with the
theorem integrating prescribed homogeneous classes on that set. Both are proved by their own
construction, so this remains a hypothesis of the abstract theorem.

What the Cantor–Bendixson instance supplies. The set here is shared by every entry of the tuple,
while a derivative representative is supported on the exact-rank level of its own series, so the
candidate is the union of those levels. The integration theorem requires a discrete set, and a
union of discrete sets is not discrete in general—but it is near zero, which is the only place the
germs detect. Past its own cutoff a level stays away from the points it misses, finitely many
cutoffs have a largest, and above that the union is discrete
(`exists_isDiscrete_iUnion_rankLevelSet`). The integration construction then runs over it
(`exists_prescribed_components_on_set_of_isDiscrete`), and the representatives may be cut off
below the common bound without changing their germs. -/
def HasSyzygyIntegration : Prop :=
  ∀ {d : NatOrdinal.{z}}, 0 < d.constantCoeff → ∀ {u : B → R},
    IsHomogeneousTuple A lam u d →
    ∃ (S : Set T) (D : B → T → R),
      (∀ b, Δ (u b) = ((D b : T → R) : Germ l R)) ∧
      (∀ t, IsHomogeneousTuple A lam (fun b ↦ D b t) (d.removeNat 1)) ∧
      (∀ b, ∀ t ∉ S, D b t = 0) ∧
      ∀ {ρ : NatOrdinal.{z}} (a : T → R), (∀ t, a t ∈ A ρ) →
        ∃ s : R, s ∈ A (ρ + 1) ∧ ∃ G : T → R, Δ s = (G : Germ l R) ∧
          (∀ t ∈ S, G t = a t) ∧ (∀ t ∉ S, G t = 0)

omit [GradedAlgebra A] [Fintype B] in
/-- Characterization of the successor syzygy-integration interface. -/
theorem hasSyzygyIntegration_iff : HasSyzygyIntegration A Δ lam (T := T) ↔
    ∀ {d : NatOrdinal.{z}}, 0 < d.constantCoeff → ∀ {u : B → R},
      IsHomogeneousTuple A lam u d →
      ∃ (S : Set T) (D : B → T → R),
        (∀ b, Δ (u b) = ((D b : T → R) : Germ l R)) ∧
        (∀ t, IsHomogeneousTuple A lam (fun b ↦ D b t) (d.removeNat 1)) ∧
        (∀ b, ∀ t ∉ S, D b t = 0) ∧
        ∀ {ρ : NatOrdinal.{z}} (a : T → R), (∀ t, a t ∈ A ρ) →
          ∃ s : R, s ∈ A (ρ + 1) ∧ ∃ G : T → R, Δ s = (G : Germ l R) ∧
            (∀ t ∈ S, G t = a t) ∧ (∀ t ∉ S, G t = 0) :=
  Iff.rfl

/-- **The induction on syzygies.** Let the `c_b` be homogeneous of degrees that are zero or limits,
let `T` be a finite set of homogeneous syzygies of `(c_b)` annihilated by the derivation, and `N`
the submodule it spans. If every homogeneous syzygy of degree below `δ` with finite part zero lies
in `N`, then every homogeneous syzygy of degree at most `δ` lies in `N`.

The induction is on the finite part of the degree. A syzygy of successor degree has a derivative
representative that is again a syzygy one degree lower, hence in `N`; decomposing it along the
generators and integrating the coefficients produces a candidate whose difference from the original
has zero derivative, so injectivity in successor degree finishes. -/
theorem mem_span_of_isHomogeneousTuple_of_sum_eq_zero
    (hΔ : GermPolynomial.IsLoweringDerivation A Δ)
    (hc : ∀ b, c b ∈ A (lam b)) (hlam : ∀ b, (lam b).constantCoeff = 0)
    (hint : HasSyzygyIntegration A Δ lam (T := T))
    (T' : Finset (B → R)) (eT : (B → R) → NatOrdinal.{z})
    (hT : ∀ τ ∈ T', IsHomogeneousTuple A lam τ (eT τ))
    (hTd : ∀ τ ∈ T', ∀ b, Δ (τ b) = 0)
    {δ : NatOrdinal.{z}} (hδ : 0 < δ.constantCoeff)
    (hbase : ∀ d < δ, d.constantCoeff = 0 → ∀ u : B → R, IsHomogeneousTuple A lam u d →
      ∑ b, c b * u b = 0 → u ∈ Submodule.span R (T' : Set (B → R))) :
    ∀ d ≤ δ, ∀ u : B → R, IsHomogeneousTuple A lam u d → ∑ b, c b * u b = 0 →
      u ∈ Submodule.span R (T' : Set (B → R)) := by
  classical
  suffices h : ∀ n : ℕ, ∀ d, d.constantCoeff = n → d ≤ δ → ∀ u : B → R,
      IsHomogeneousTuple A lam u d → ∑ b, c b * u b = 0 →
      u ∈ Submodule.span R (T' : Set (B → R)) from
    fun d hd u hu hsyz ↦ h _ d rfl hd u hu hsyz
  intro n
  induction n with
  | zero =>
    intro d hd hdδ u hu hsyz
    refine hbase d (lt_of_le_of_ne hdδ fun h ↦ ?_) hd u hu hsyz
    rw [h] at hd
    omega
  | succ n ih =>
    intro d hd hdδ u hu hsyz
    have hdpos : 0 < d.constantCoeff := by rw [hd]; omega
    obtain ⟨d', hd'def⟩ : ∃ d', d' = d.removeNat 1 := ⟨_, rfl⟩
    have hd'1 : d' + 1 = d := by
      have hstep := NatOrdinal.removeNat_add_natCast (a := d) (n := 1) hdpos
      rw [Nat.cast_one] at hstep
      rw [hd'def]
      exact hstep
    have hd'c : d'.constantCoeff = n := by
      rw [hd'def, NatOrdinal.constantCoeff_removeNat, hd]
      omega
    have hd'lt : d' < δ := lt_of_lt_of_le (lt_of_lt_of_eq (lt_add_one d') hd'1) hdδ
    -- the derivative representative and its prescription set
    obtain ⟨S, D, hD, hDhom, hDoff, hintS⟩ := hint hdpos hu
    -- the derivative tuple is a syzygy on a set of the filter
    have hDsyz : ∀ᶠ t in l, ∑ b, c b * D b t = 0 := by
      have hzero := congrArg Δ hsyz
      rw [map_zero, map_sum] at hzero
      have hterm : ∀ b, Δ (c b * u b) = ((fun t ↦ c b * D b t : T → R) : Germ l R) := by
        intro b
        rw [GermPolynomial.derivation_leibniz, hΔ.eq_zero (hlam b) (hc b),
          zero_mul, zero_add, hD]
        rfl
      simp only [hterm] at hzero
      have hsum : ((fun t ↦ ∑ b, c b * D b t : T → R) : Germ l R) =
          ((fun _ ↦ (0 : R) : T → R) : Germ l R) := by
        rw [germ_coe_sum]
        exact hzero
      exact Germ.coe_eq.mp hsum
    obtain ⟨V, hV, hVsub⟩ := eventually_iff_exists_mem.mp hDsyz
    -- cut the representative down to that set, so its values lie in the span everywhere
    obtain ⟨W, hWon, hWoff⟩ : ∃ W : T → B → R, (∀ t ∈ V, W t = fun b ↦ D b t) ∧
        ∀ t ∉ V, W t = 0 :=
      ⟨fun t ↦ if t ∈ V then (fun b ↦ D b t) else 0,
        fun t ht ↦ if_pos ht, fun t ht ↦ if_neg ht⟩
    have hWhom : ∀ t, IsHomogeneousTuple A lam (W t) d' := fun t ↦ by
      by_cases ht : t ∈ V
      · rw [hWon t ht, hd'def]
        exact hDhom t
      · rw [hWoff t ht]
        exact isHomogeneousTuple_zero lam d'
    have hWN : ∀ t, W t ∈ Submodule.span R (T' : Set (B → R)) := fun t ↦ by
      by_cases ht : t ∈ V
      · rw [hWon t ht]
        refine ih d' hd'c hd'lt.le _ ?_ (hVsub t ht)
        rw [hd'def]
        exact hDhom t
      · rw [hWoff t ht]
        exact zero_mem _
    obtain ⟨a, ha, hasum⟩ : ∃ a : T → (B → R) → R,
        (∀ t, ∀ τ ∈ T', (∀ ρ, ρ + eT τ = d' → a t τ ∈ A ρ) ∧
          ((¬ ∃ ρ, ρ + eT τ = d') → a t τ = 0)) ∧
        ∀ t, W t = ∑ τ ∈ T', a t τ • τ := by
      choose a ha hasum using fun t ↦ exists_eq_sum_smul_of_mem_span hT (hWhom t) (hWN t)
      exact ⟨a, ha, hasum⟩
    -- integrate each coefficient family
    obtain ⟨s, hs, hs0, G, hG, hGon, hGoff⟩ : ∃ s : (B → R) → R,
        (∀ τ ∈ T', ∀ ρ, ρ + eT τ = d' → s τ ∈ A (ρ + 1)) ∧
        (∀ τ ∈ T', (¬ ∃ ρ, ρ + eT τ = d') → s τ = 0) ∧
        ∃ G : (B → R) → T → R,
          (∀ τ ∈ T', Δ (s τ) = ((G τ : T → R) : Germ l R)) ∧
          (∀ τ ∈ T', ∀ t ∈ S, G τ t = a t τ) ∧
          (∀ τ ∈ T', ∀ t ∉ S, G τ t = 0) := by
      have hone : ∀ τ ∈ T', ∃ sτ : R, (∀ ρ, ρ + eT τ = d' → sτ ∈ A (ρ + 1)) ∧
          ((¬ ∃ ρ, ρ + eT τ = d') → sτ = 0) ∧
          ∃ Gτ : T → R, Δ sτ = ((Gτ : T → R) : Germ l R) ∧
            (∀ t ∈ S, Gτ t = a t τ) ∧ (∀ t ∉ S, Gτ t = 0) := by
        intro τ hτ
        by_cases hρ : ∃ ρ, ρ + eT τ = d'
        · obtain ⟨ρ, hρ⟩ := hρ
          obtain ⟨sτ, hsτ, Gτ, hGτ, hGon', hGoff'⟩ :=
            hintS (ρ := ρ) (fun t ↦ a t τ) (fun t ↦ (ha t τ hτ).1 ρ hρ)
          refine ⟨sτ, fun ρ' hρ' ↦ ?_, fun hn ↦ absurd ⟨ρ, hρ⟩ hn, Gτ, hGτ,
            hGon', hGoff'⟩
          rwa [add_right_cancel (hρ'.trans hρ.symm)]
        · exact ⟨0, fun ρ hρ' ↦ absurd ⟨ρ, hρ'⟩ hρ, fun _ ↦ rfl, fun _ ↦ 0,
            by rw [map_zero]; rfl, fun t _ ↦ ((ha t τ hτ).2 hρ).symm, fun _ _ ↦ rfl⟩
      choose! sf hsf hsf0 Gf hGf hGon' hGoff' using hone
      exact ⟨sf, hsf, hsf0, Gf, hGf, hGon', hGoff'⟩
    -- the difference has zero derivative in every entry, hence vanishes
    have hy : ∀ b, u b - ∑ τ ∈ T', s τ * τ b = 0 := by
      intro b
      by_cases hb : ∃ β, β + lam b = d
      · obtain ⟨β, hβ⟩ := hb
        have hβpos : 0 < β.constantCoeff := by
          have hc1 := congrArg NatOrdinal.constantCoeff hβ
          rw [NatOrdinal.constantCoeff_add, hlam b, add_zero, hd] at hc1
          omega
        have hβ' : β.removeNat 1 + lam b = d' := by
          have hstep := NatOrdinal.removeNat_add_right β (lam b) hβpos
          rw [hβ, ← hd'def] at hstep
          exact hstep.symm
        have hβ1 : β.removeNat 1 + 1 = β := by
          have hstep := NatOrdinal.removeNat_add_natCast (a := β) (n := 1) hβpos
          rwa [Nat.cast_one] at hstep
        have hmem : u b - ∑ τ ∈ T', s τ * τ b ∈ A β := by
          refine sub_mem (hu.mem hβ) (sum_mem fun τ hτ ↦ ?_)
          by_cases hτb : ∃ β', β' + lam b = eT τ
          · obtain ⟨β', hβ'b⟩ := hτb
            by_cases hρ : ∃ ρ, ρ + eT τ = d'
            · obtain ⟨ρ, hρ⟩ := hρ
              have h1 : ρ + β' = β.removeNat 1 :=
                add_right_cancel (b := lam b) (by rw [add_assoc, hβ'b, hρ, hβ'])
              have h2 : (ρ + 1) + β' = β := by rw [add_right_comm, h1, hβ1]
              rw [← h2]
              exact SetLike.mul_mem_graded (hs τ hτ ρ hρ) ((hT τ hτ).mem hβ'b)
            · rw [hs0 τ hτ hρ, zero_mul]
              exact zero_mem _
          · rw [(hT τ hτ).eq_zero hτb, mul_zero]
            exact zero_mem _
        refine hΔ.injective hβpos hmem ?_
        have hΔs : Δ (∑ τ ∈ T', s τ * τ b) =
            ((fun t ↦ ∑ τ ∈ T', G τ t * τ b : T → R) : Germ l R) := by
          rw [map_sum]
          have hterm : ∀ τ ∈ T', Δ (s τ * τ b) =
              ((fun t ↦ G τ t * τ b : T → R) : Germ l R) := by
            intro τ hτ
            rw [GermPolynomial.derivation_leibniz, hTd τ hτ b, mul_zero, add_zero, hG τ hτ]
            rfl
          rw [Finset.sum_congr rfl hterm, germ_coe_sum]
        rw [map_sub, hD, hΔs, ← Germ.coe_sub]
        refine Germ.coe_eq.mpr ?_
        filter_upwards [hV] with t ht
        simp only [Pi.sub_apply]
        by_cases hSt : t ∈ S
        · have hdec := congrFun (hasum t) b
          rw [hWon t ht, Finset.sum_apply] at hdec
          simp only [Pi.smul_apply, smul_eq_mul] at hdec
          rw [hdec, sub_eq_zero]
          exact Finset.sum_congr rfl fun τ hτ ↦ by rw [hGon τ hτ t hSt]
        · rw [hDoff b t hSt, Finset.sum_eq_zero fun τ hτ ↦ by
            rw [hGoff τ hτ t hSt, zero_mul], sub_zero]
      · rw [hu.eq_zero hb, Finset.sum_eq_zero, sub_zero]
        intro τ hτ
        by_cases hτb : ∃ β', β' + lam b = eT τ
        · obtain ⟨β', hβ'b⟩ := hτb
          have hρ : ¬ ∃ ρ, ρ + eT τ = d' := fun ⟨ρ, hρ⟩ ↦ hb ⟨ρ + β' + 1, by
            calc ρ + β' + 1 + lam b = ρ + (β' + lam b) + 1 := by abel
              _ = d := by rw [hβ'b, hρ, hd'1]⟩
          rw [hs0 τ hτ hρ, zero_mul]
        · rw [(hT τ hτ).eq_zero hτb, mul_zero]
    have hueq : u = ∑ τ ∈ T', s τ • τ := by
      funext b
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact sub_eq_zero.mp (hy b)
    rw [hueq]
    exact Submodule.sum_mem _ fun τ hτ ↦ Submodule.smul_mem _ _ (Submodule.subset_span hτ)

end Induction

end OrdinalGraded

end
