/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.SumLexOrder
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InvolutionCard
public import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjSubsetSplit
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonExistence

/-!
# The disjoint-union factorization of the corrected value

The corrected constrained partition value of a disjoint union at a
boundary state factors as the product of the componentwise values
at the restricted states, with the lexicographic label order on
the union.  This part supplies the subset and transition-system
half; `B.lean` splits the colourings and the summand, and `C.lean`
migrates canonical data.

The route reindexes the Eulerian subset sum along the
componentwise splitting of `DisjSubsetSplit`, restricts and
multiplies boundary-relative transition systems componentwise,
adds circuit counts (each component's orbit data is even: the
edge-pairing reversal is a fixed-point-free involution on walk
orbits), and splits the through product and the colouring sums.
-/

@[expose] public section

namespace RS



/-! ## Membership characterizations (any fragment) -/

open scoped Classical in
private theorem mem_throughFlags_iff {γ : Type} {W : Fragment γ}
    {F : EdgeSubset W} {f : W.Flag} :
    f ∈ F.throughFlags ↔ f ∈ F.flags ∧
      ((∃ i : γ, W.attach f = Sum.inr i) ∧
        ∃ j : γ, W.attach (W.pairing f) = Sum.inr j) :=
  Finset.mem_filter

section SumToolbox

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}

/-! ## Attachment over the union (mirrors `DisjSubsetSplit`) -/

/-- A left flag attaches to a left vertex over the union exactly
when it attaches to that vertex in its own component. -/
theorem attach_inl_eq_inl {f : W₁.Flag} {v : W₁.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inl f) = Sum.inl (Sum.inl v) ↔
      W₁.attach f = Sum.inl v := by
  change (W₁.attach f).map Sum.inl Sum.inl = Sum.inl (Sum.inl v) ↔
    W₁.attach f = Sum.inl v
  constructor
  · intro h
    rcases hA : W₁.attach f with w | ℓ <;> rw [hA] at h
    · simp only [Sum.map_inl, Sum.inl.injEq] at h
      rw [h]
    · simp only [Sum.map_inr] at h
      exact absurd h (by simp)
  · intro h
    simp [h]

/-- The right analogue. -/
theorem attach_inr_eq_inr {f : W₂.Flag} {v : W₂.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inr f) = Sum.inl (Sum.inr v) ↔
      W₂.attach f = Sum.inl v := by
  change (W₂.attach f).map Sum.inr Sum.inr = Sum.inl (Sum.inr v) ↔
    W₂.attach f = Sum.inl v
  constructor
  · intro h
    rcases hA : W₂.attach f with w | ℓ <;> rw [hA] at h
    · simp only [Sum.map_inl, Sum.inl.injEq, Sum.inr.injEq] at h
      rw [h]
    · simp only [Sum.map_inr] at h
      exact absurd h (by simp)
  · intro h
    simp [h]

/-- A right flag never attaches to a left vertex. -/
theorem attach_inr_ne_inl {f : W₂.Flag} {v : W₁.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inr f) ≠ Sum.inl (Sum.inl v) := by
  change (W₂.attach f).map Sum.inr Sum.inr ≠ Sum.inl (Sum.inl v)
  rcases W₂.attach f with w | ℓ <;> simp

/-- A left flag never attaches to a right vertex. -/
theorem attach_inl_ne_inr {f : W₁.Flag} {v : W₂.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inl f) ≠ Sum.inl (Sum.inr v) := by
  change (W₁.attach f).map Sum.inl Sum.inl ≠ Sum.inl (Sum.inr v)
  rcases W₁.attach f with w | ℓ <;> simp

/-- A left flag is internally attached in the union exactly when it
is internally attached in the left component. -/
theorem attach_inl_vertex_iff {g : W₁.Flag} :
    (∃ v : (W₁.disjUnion W₂).Vertex,
        (W₁.disjUnion W₂).attach (Sum.inl g) = Sum.inl v) ↔
      ∃ w : W₁.Vertex, W₁.attach g = Sum.inl w := by
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl w => exact ⟨w, attach_inl_eq_inl.mp hv⟩
    | inr w => exact absurd hv attach_inl_ne_inr
  · rintro ⟨w, hw⟩
    exact ⟨Sum.inl w, attach_inl_eq_inl.mpr hw⟩

/-- A right flag is internally attached in the union exactly when it
is internally attached in the right component. -/
theorem attach_inr_vertex_iff {g : W₂.Flag} :
    (∃ v : (W₁.disjUnion W₂).Vertex,
        (W₁.disjUnion W₂).attach (Sum.inr g) = Sum.inl v) ↔
      ∃ w : W₂.Vertex, W₂.attach g = Sum.inl w := by
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl w => exact absurd hv attach_inr_ne_inl
    | inr w => exact ⟨w, attach_inr_eq_inr.mp hv⟩
  · rintro ⟨w, hw⟩
    exact ⟨Sum.inr w, attach_inr_eq_inr.mpr hw⟩

/-- A left flag is boundary over the union exactly when it is
boundary in its own component. -/
theorem attach_inl_label_iff {g : W₁.Flag} :
    (∃ i : α ⊕ β,
        (W₁.disjUnion W₂).attach (Sum.inl g) = Sum.inr i) ↔
      ∃ i₀ : α, W₁.attach g = Sum.inr i₀ := by
  change (∃ i, (W₁.attach g).map Sum.inl Sum.inl = Sum.inr i) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    rcases hA : W₁.attach g with w | i₀ <;> rw [hA] at hi
    · simp at hi
    · exact ⟨i₀, rfl⟩
  · rintro ⟨i₀, hi⟩
    exact ⟨Sum.inl i₀, by rw [hi]; rfl⟩

/-- The right analogue. -/
theorem attach_inr_label_iff {g : W₂.Flag} :
    (∃ i : α ⊕ β,
        (W₁.disjUnion W₂).attach (Sum.inr g) = Sum.inr i) ↔
      ∃ i₀ : β, W₂.attach g = Sum.inr i₀ := by
  change (∃ i, (W₂.attach g).map Sum.inr Sum.inr = Sum.inr i) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    rcases hA : W₂.attach g with w | i₀ <;> rw [hA] at hi
    · simp at hi
    · exact ⟨i₀, rfl⟩
  · rintro ⟨i₀, hi⟩
    exact ⟨Sum.inr i₀, by rw [hi]; rfl⟩

/-- The union's edge pairing on a left flag is the left component's,
injected. -/
theorem pairing_inl (g : W₁.Flag) :
    (W₁.disjUnion W₂).pairing (Sum.inl g) =
      Sum.inl (W₁.pairing g) := rfl

/-- The right analogue. -/
theorem pairing_inr (g : W₂.Flag) :
    (W₁.disjUnion W₂).pairing (Sum.inr g) =
      Sum.inr (W₂.pairing g) := rfl

/-! ## The component edge subsets -/

/-- The left component of an edge subset of a disjoint union. -/
noncomputable def leftSub (F : EdgeSubset (W₁.disjUnion W₂)) : EdgeSubset W₁ :=
  ⟨leftPart F.flags, fun f hf => mem_leftPart.mpr (by
    have h := F.pairing_mem _ (mem_leftPart.mp hf)
    rwa [pairing_inl] at h)⟩

/-- The right component of an edge subset of a disjoint union. -/
noncomputable def rightSub (F : EdgeSubset (W₁.disjUnion W₂)) : EdgeSubset W₂ :=
  ⟨rightPart F.flags, fun f hf => mem_rightPart.mpr (by
    have h := F.pairing_mem _ (mem_rightPart.mp hf)
    rwa [pairing_inr] at h)⟩

/-- Membership in the left component subset. -/
theorem mem_leftSub_flags {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₁.Flag} : g ∈ (leftSub F).flags ↔ Sum.inl g ∈ F.flags :=
  mem_leftPart

/-- Membership in the right component subset. -/
theorem mem_rightSub_flags {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₂.Flag} : g ∈ (rightSub F).flags ↔ Sum.inr g ∈ F.flags :=
  mem_rightPart

/-- Internality is componentwise on the left. -/
theorem inl_mem_internal {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₁.Flag} :
    (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags ↔
      g ∈ (leftSub F).internalFlags := by
  constructor
  · intro h
    obtain ⟨hf, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp h
    exact EdgeSubset.mem_internalFlags_iff.mpr
      ⟨mem_leftSub_flags.mpr hf, attach_inl_vertex_iff.mp hv⟩
  · intro h
    obtain ⟨hf, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp h
    exact EdgeSubset.mem_internalFlags_iff.mpr
      ⟨mem_leftSub_flags.mp hf, attach_inl_vertex_iff.mpr hv⟩

/-- Internality is componentwise on the right. -/
theorem inr_mem_internal {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₂.Flag} :
    (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags ↔
      g ∈ (rightSub F).internalFlags := by
  constructor
  · intro h
    obtain ⟨hf, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp h
    exact EdgeSubset.mem_internalFlags_iff.mpr
      ⟨mem_rightSub_flags.mpr hf, attach_inr_vertex_iff.mp hv⟩
  · intro h
    obtain ⟨hf, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp h
    exact EdgeSubset.mem_internalFlags_iff.mpr
      ⟨mem_rightSub_flags.mp hf, attach_inr_vertex_iff.mpr hv⟩

/-- Being a core flag is componentwise on the left. -/
theorem inl_mem_core {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₁.Flag} :
    (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.coreFlags ↔
      g ∈ (leftSub F).coreFlags := by
  constructor
  · intro hh
    obtain ⟨hf, hor⟩ := F.mem_coreFlags_iff.mp hh
    refine (leftSub F).mem_coreFlags_iff.mpr
      ⟨mem_leftSub_flags.mpr hf, ?_⟩
    rcases hor with h | h
    · exact Or.inl (attach_inl_vertex_iff.mp h)
    · rw [pairing_inl] at h
      exact Or.inr (attach_inl_vertex_iff.mp h)
  · intro hh
    obtain ⟨hf, hor⟩ := (leftSub F).mem_coreFlags_iff.mp hh
    refine F.mem_coreFlags_iff.mpr ⟨mem_leftSub_flags.mp hf, ?_⟩
    rcases hor with h | h
    · exact Or.inl (attach_inl_vertex_iff.mpr h)
    · refine Or.inr ?_
      rw [pairing_inl]
      exact attach_inl_vertex_iff.mpr h

/-- Being a core flag is componentwise on the right. -/
theorem inr_mem_core {F : EdgeSubset (W₁.disjUnion W₂)}
    {g : W₂.Flag} :
    (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.coreFlags ↔
      g ∈ (rightSub F).coreFlags := by
  constructor
  · intro hh
    obtain ⟨hf, hor⟩ := F.mem_coreFlags_iff.mp hh
    refine (rightSub F).mem_coreFlags_iff.mpr
      ⟨mem_rightSub_flags.mpr hf, ?_⟩
    rcases hor with h | h
    · exact Or.inl (attach_inr_vertex_iff.mp h)
    · rw [pairing_inr] at h
      exact Or.inr (attach_inr_vertex_iff.mp h)
  · intro hh
    obtain ⟨hf, hor⟩ := (rightSub F).mem_coreFlags_iff.mp hh
    refine F.mem_coreFlags_iff.mpr ⟨mem_rightSub_flags.mp hf, ?_⟩
    rcases hor with h | h
    · exact Or.inl (attach_inr_vertex_iff.mpr h)
    · refine Or.inr ?_
      rw [pairing_inr]
      exact attach_inr_vertex_iff.mpr h

end SumToolbox

/-! ## Parity of the open orbit data

The edge pairing reverses walk orbits: it is a fixed-point-free
involution of the periodic flags conjugating the walk permutation
to its inverse.  Consequently both the nontrivial cycles and the
fixed points of the walk permutation pair up, and the orbit total
entering `openCircuitCount` is even. -/

section Parity

open EdgeSubset

variable {γ : Type} {W : Fragment γ} {F : EdgeSubset W}

/-- The periodic walk permutation has an even number of fixed points:
the edge-pairing reversal is a fixed-point-free involution on them. -/
private theorem even_card_fixedPoints (κ : F.RelTransitionSystem) :
    Even (Fintype.card
      (Function.fixedPoints κ.walkPermPeriodic)) := by
  have hfix : ∀ x : Function.fixedPoints κ.walkPermPeriodic,
      revPerm κ x.val ∈ Function.fixedPoints κ.walkPermPeriodic := by
    intro x
    have hx : κ.walkPermPeriodic x.val = x.val := x.prop
    change κ.walkPermPeriodic (revPerm κ x.val) = revPerm κ x.val
    conv_lhs => rw [← hx]
    have h := congrArg (fun q => q x.val)
      (walkPerm_revPerm_walkPerm κ)
    exact h
  refine even_fintypeCard_of_involution
    (fun x => ⟨revPerm κ x.val, hfix x⟩) ?_ ?_
  · intro x
    refine Subtype.ext (Subtype.ext ?_)
    change W.pairing (W.pairing x.val.val) = x.val.val
    exact W.pairing_invol x.val.val
  · intro x heq
    exact W.pairing_ne x.val.val
      (congrArg (fun z => z.val.val) heq)

/-- The periodic walk permutation has an even number of cycles: the
reversal conjugates it to its inverse, pairing its cycle factors off
without fixing one. -/
private theorem even_card_cycleType (κ : F.RelTransitionSystem) :
    Even (Multiset.card κ.walkPermPeriodic.cycleType) := by
  classical
  -- ═══════ SETUP: THE REVERSAL CONJUGATES THE WALK TO ITS INVERSE ═══════
  set P := κ.walkPermPeriodic with hPdef
  set R := revPerm κ with hRdef
  have hPRP : P * R * P = R := walkPerm_revPerm_walkPerm κ
  have hRR : R * R = 1 := revPerm_mul_self κ
  have hRinv : R⁻¹ = R := revPerm_inv κ
  have hPR : P * R = R * P⁻¹ := by
    have h := congrArg (fun q => q * P⁻¹) hPRP
    simpa [mul_assoc] using h
  have hRPR : R * P * R = P⁻¹ := by
    rw [mul_assoc, hPR, ← mul_assoc, hRR, one_mul]
  have hRPiR : R * P⁻¹ * R = P := by
    have h := congrArg (fun q => q⁻¹) hRPR
    simp only [mul_inv_rev, hRinv, inv_inv] at h
    rw [mul_assoc]
    exact h
  -- ═══════ STAGE 1: `c ↦ R c⁻¹ R` ACTS ON THE CYCLE FACTORS ═══════
  have hRRapp : ∀ x, R (R x) = x := fun x =>
    congrArg (fun q => q x) hRR
  have hmemmap : ∀ c ∈ P.cycleFactorsFinset,
      R * c⁻¹ * R ∈ P.cycleFactorsFinset := by
    intro c hc
    obtain ⟨hcyc, hsupp⟩ :=
      Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
    refine Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨?_, ?_⟩
    · have h := (hcyc.inv).conj (g := R)
      rwa [hRinv] at h
    · intro a ha
      have hb_ne : c⁻¹ (R a) ≠ R a := by
        intro h
        apply Equiv.Perm.mem_support.mp ha
        calc (R * c⁻¹ * R) a = R (c⁻¹ (R a)) := rfl
          _ = R (R a) := by rw [h]
          _ = a := hRRapp a
      have hcinv_supp : c⁻¹ (R a) ∈ c.support := by
        rw [← Equiv.Perm.support_inv]
        exact Equiv.Perm.apply_mem_support.mpr
          (Equiv.Perm.mem_support.mpr hb_ne)
      have h1 := hsupp _ hcinv_supp
      have h2 : P (c⁻¹ (R a)) = R a := by
        rw [← h1]
        exact Equiv.apply_symm_apply c (R a)
      have h3 : c⁻¹ (R a) = P⁻¹ (R a) := by
        have h := congrArg (fun z => P⁻¹ z) h2
        simpa [Equiv.Perm.inv_def] using h
      calc (R * c⁻¹ * R) a = R (c⁻¹ (R a)) := rfl
        _ = R (P⁻¹ (R a)) := by rw [h3]
        _ = P a := congrArg (fun q => q a) hRPiR
  have hinv_i : ∀ c : Equiv.Perm {f : W.Flag // f ∈ κ.periodicFlags},
      R * (R * c⁻¹ * R)⁻¹ * R = c := by
    intro c
    simp only [mul_inv_rev, hRinv, inv_inv]
    calc R * (R * c * R) * R
        = (R * R) * c * (R * R) := by
          simp only [mul_assoc]
      _ = c := by rw [hRR, one_mul, mul_one]
  -- ═══════ STAGE 2: THAT INVOLUTION HAS NO FIXED CYCLE ═══════
  have hne_i : ∀ c ∈ P.cycleFactorsFinset, R * c⁻¹ * R ≠ c := by
    intro c hc heq
    obtain ⟨hcyc, hsupp⟩ :=
      Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
    have hconj : R * c * R = c⁻¹ := by
      have h := congrArg (fun q => q⁻¹) heq
      simp only [mul_inv_rev, hRinv, inv_inv] at h
      rw [← h, mul_assoc]
    -- conjugation sends powers of `c` to inverse powers
    have hpow : ∀ (t : ℕ) (x), R ((c ^ t) (R x)) = (c ^ t)⁻¹ x := by
      intro t x
      have h : R * c ^ t * R = (c ^ t)⁻¹ := by
        have h0 : R * c * R⁻¹ = c⁻¹ := by rw [hRinv]; exact hconj
        have h1 := congrArg (fun q => q ^ t) h0
        simp only [conj_pow] at h1
        rw [hRinv] at h1
        rw [h1, inv_pow]
      exact congrArg (fun q => q x) h
    have hcyc' := hcyc
    obtain ⟨y₀, hy₀, -⟩ := hcyc
    have hRy₀ : c (R y₀) ≠ R y₀ := by
      intro h
      have happ := congrArg (fun q => q (R y₀)) heq
      have happ' : R (c⁻¹ y₀) = c (R y₀) := by
        calc R (c⁻¹ y₀) = R (c⁻¹ (R (R y₀))) := by rw [hRRapp]
          _ = (R * c⁻¹ * R) (R y₀) := rfl
          _ = c (R y₀) := happ
      rw [h] at happ'
      have hfix : c⁻¹ y₀ = y₀ := by
        have := congrArg (fun z => R z) happ'
        rwa [hRRapp, hRRapp] at this
      have h5 : y₀ = c y₀ := by
        have h6 := congrArg (fun z => c z) hfix
        simpa using h6
      exact hy₀ h5.symm
    obtain ⟨m, hm⟩ := hcyc'.exists_pow_eq hy₀ hRy₀
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- even period offset: a pairing-fixed flag
      have hu : R ((c ^ t) y₀) = (c ^ t) y₀ := by
        calc R ((c ^ t) y₀) = R ((c ^ t) (R (R y₀))) := by
              rw [hRRapp]
          _ = (c ^ t)⁻¹ (R y₀) := hpow t (R y₀)
          _ = (c ^ t)⁻¹ ((c ^ m) y₀) := by rw [hm]
          _ = (c ^ t)⁻¹ ((c ^ t) ((c ^ t) y₀)) := by
              rw [show m = t + t from ht, pow_add,
                Equiv.Perm.mul_apply]
          _ = (c ^ t) y₀ := Equiv.symm_apply_apply (c ^ t) _
      exact W.pairing_ne ((c ^ t) y₀).val
        (congrArg Subtype.val hu)
    · -- odd period offset: a matching-fixed flag
      have hu : R ((c ^ t) y₀) = (c ^ (t + 1)) y₀ := by
        calc R ((c ^ t) y₀) = R ((c ^ t) (R (R y₀))) := by
              rw [hRRapp]
          _ = (c ^ t)⁻¹ (R y₀) := hpow t (R y₀)
          _ = (c ^ t)⁻¹ ((c ^ m) y₀) := by rw [hm]
          _ = (c ^ t)⁻¹ ((c ^ t) ((c ^ (t + 1)) y₀)) := by
              rw [show m = t + (t + 1) from by omega, pow_add,
                Equiv.Perm.mul_apply]
          _ = (c ^ (t + 1)) y₀ := Equiv.symm_apply_apply (c ^ t) _
      have husupp : (c ^ t) y₀ ∈ c.support :=
        Equiv.Perm.pow_apply_mem_support.mpr
          (Equiv.Perm.mem_support.mpr hy₀)
      have hcu : c ((c ^ t) y₀) = P ((c ^ t) y₀) := hsupp _ husupp
      have hRu : R ((c ^ t) y₀) = P ((c ^ t) y₀) := by
        rw [hu, ← hcu, pow_succ', Equiv.Perm.mul_apply]
      -- vals: the matching fixes the pairing of a periodic flag
      have hval := congrArg Subtype.val hRu
      have hmatch : κ.match_ (W.pairing ((c ^ t) y₀).val) =
          W.pairing ((c ^ t) y₀).val := by
        exact hval.symm
      have hint : W.pairing ((c ^ t) y₀).val ∈ F.internalFlags :=
        all_pairings_internal_of_periodic κ
          (κ.mem_periodicFlags.mp ((c ^ t) y₀).prop) 0
      exact κ.match_ne _ hint hmatch
  -- ═══════ ASSEMBLY: SO THE CYCLES PAIR OFF ═══════
  have heven := even_card_of_involution P.cycleFactorsFinset
    (fun c => R * c⁻¹ * R) hmemmap (fun c _ => hinv_i c) hne_i
  rw [Equiv.Perm.cycleType_def, Multiset.card_map]
  exact heven

end Parity

/-! ## Componentwise relative transition systems -/

section ProdSystems

open EdgeSubset

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}
  {F : EdgeSubset (W₁.disjUnion W₂)}

/-! ### Restriction to the components -/

/-- Restrict a union matching to a left flag, fixing it if the image lies on the right. -/
noncomputable def leftDescend (κ : F.RelTransitionSystem)
    (g : W₁.Flag) : W₁.Flag :=
  Sum.elim id (fun _ => g) (κ.match_ (Sum.inl g))

/-- Restrict a union matching to a right flag, fixing it if the image lies on the left. -/
noncomputable def rightDescend (κ : F.RelTransitionSystem)
    (g : W₂.Flag) : W₂.Flag :=
  Sum.elim (fun _ => g) id (κ.match_ (Sum.inr g))

/-- On an internal left flag, the union system's match is the left
descent, injected. -/
theorem leftDescend_spec (κ : F.RelTransitionSystem)
    {g : W₁.Flag} (hg : g ∈ (leftSub F).internalFlags) :
    κ.match_ (Sum.inl g) = Sum.inl (leftDescend κ g) := by
  have hgU : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags :=
    inl_mem_internal.mpr hg
  obtain ⟨w, hw⟩ := (leftSub F).attach_internal_of_mem hg
  have hvert := κ.match_vertex _ hgU (Sum.inl w)
    (attach_inl_eq_inl.mpr hw)
  rcases hm : κ.match_ (Sum.inl g) with g' | g'
  · unfold leftDescend
    rw [hm]
    rfl
  · rw [hm] at hvert
    exact absurd hvert attach_inr_ne_inl

/-- On an internal right flag, the union system's match is the right
descent, injected. -/
theorem rightDescend_spec (κ : F.RelTransitionSystem)
    {g : W₂.Flag} (hg : g ∈ (rightSub F).internalFlags) :
    κ.match_ (Sum.inr g) = Sum.inr (rightDescend κ g) := by
  have hgU : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags :=
    inr_mem_internal.mpr hg
  obtain ⟨w, hw⟩ := (rightSub F).attach_internal_of_mem hg
  have hvert := κ.match_vertex _ hgU (Sum.inr w)
    (attach_inr_eq_inr.mpr hw)
  rcases hm : κ.match_ (Sum.inr g) with g' | g'
  · rw [hm] at hvert
    exact absurd hvert attach_inl_ne_inr
  · unfold rightDescend
    rw [hm]
    rfl

/-- The left descent of an internal left flag is again internal. -/
theorem leftDescend_mem (κ : F.RelTransitionSystem)
    {g : W₁.Flag} (hg : g ∈ (leftSub F).internalFlags) :
    leftDescend κ g ∈ (leftSub F).internalFlags := by
  have h := κ.match_mem _ (inl_mem_internal.mpr hg)
  rw [leftDescend_spec κ hg] at h
  exact inl_mem_internal.mp h

/-- The right descent of an internal right flag is again internal. -/
theorem rightDescend_mem (κ : F.RelTransitionSystem)
    {g : W₂.Flag} (hg : g ∈ (rightSub F).internalFlags) :
    rightDescend κ g ∈ (rightSub F).internalFlags := by
  have h := κ.match_mem _ (inr_mem_internal.mpr hg)
  rw [rightDescend_spec κ hg] at h
  exact inr_mem_internal.mp h

/-- The restriction of a transition system on the union to its left
component: the matching never crosses between components, so it
restricts. -/
noncomputable def leftRel (κ : F.RelTransitionSystem) :
    (leftSub F).RelTransitionSystem where
  match_ := leftDescend κ
  match_invol g hg := by
    have h := κ.match_invol _ (inl_mem_internal.mpr hg)
    rw [leftDescend_spec κ hg,
      leftDescend_spec κ (leftDescend_mem κ hg)] at h
    exact Sum.inl.inj h
  match_ne g hg heq := by
    have h := κ.match_ne _ (inl_mem_internal.mpr hg)
    rw [leftDescend_spec κ hg, heq] at h
    exact h rfl
  match_mem g hg := by exact leftDescend_mem κ hg
  match_vertex g hg v hv := by
    have h := κ.match_vertex _ (inl_mem_internal.mpr hg)
      (Sum.inl v) (attach_inl_eq_inl.mpr hv)
    rw [leftDescend_spec κ hg] at h
    exact attach_inl_eq_inl.mp h

/-- The restriction to the right component. -/
noncomputable def rightRel (κ : F.RelTransitionSystem) :
    (rightSub F).RelTransitionSystem where
  match_ := rightDescend κ
  match_invol g hg := by
    have h := κ.match_invol _ (inr_mem_internal.mpr hg)
    rw [rightDescend_spec κ hg,
      rightDescend_spec κ (rightDescend_mem κ hg)] at h
    exact Sum.inr.inj h
  match_ne g hg heq := by
    have h := κ.match_ne _ (inr_mem_internal.mpr hg)
    rw [rightDescend_spec κ hg, heq] at h
    exact h rfl
  match_mem g hg := by exact rightDescend_mem κ hg
  match_vertex g hg v hv := by
    have h := κ.match_vertex _ (inr_mem_internal.mpr hg)
      (Sum.inr v) (attach_inr_eq_inr.mpr hv)
    rw [rightDescend_spec κ hg] at h
    exact attach_inr_eq_inr.mp h

/-! ### The product system -/

/-- The product of two componentwise transition systems: a system on
the union, inverse to the two restrictions. -/
noncomputable def prodRel (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) :
    F.RelTransitionSystem where
  match_ := Sum.map κ₁.match_ κ₂.match_
  match_invol f hf := by
    cases f with
    | inl g =>
      change Sum.inl (κ₁.match_ (κ₁.match_ g)) = Sum.inl g
      rw [κ₁.match_invol g (inl_mem_internal.mp hf)]
    | inr g =>
      change Sum.inr (κ₂.match_ (κ₂.match_ g)) = Sum.inr g
      rw [κ₂.match_invol g (inr_mem_internal.mp hf)]
  match_ne f hf heq := by
    cases f with
    | inl g =>
      exact κ₁.match_ne g (inl_mem_internal.mp hf) (Sum.inl.inj heq)
    | inr g =>
      exact κ₂.match_ne g (inr_mem_internal.mp hf) (Sum.inr.inj heq)
  match_mem f hf := by
    cases f with
    | inl g =>
      exact inl_mem_internal.mpr
        (κ₁.match_mem g (inl_mem_internal.mp hf))
    | inr g =>
      exact inr_mem_internal.mpr
        (κ₂.match_mem g (inr_mem_internal.mp hf))
  match_vertex f hf v hv := by
    cases f with
    | inl g =>
      cases v with
      | inl w =>
        exact attach_inl_eq_inl.mpr (κ₁.match_vertex g
          (inl_mem_internal.mp hf) w (attach_inl_eq_inl.mp hv))
      | inr w => exact absurd hv attach_inl_ne_inr
    | inr g =>
      cases v with
      | inl w => exact absurd hv attach_inr_ne_inl
      | inr w =>
        exact attach_inr_eq_inr.mpr (κ₂.match_vertex g
          (inr_mem_internal.mp hf) w (attach_inr_eq_inr.mp hv))

/-- The product of two componentwise orientations. -/
noncomputable def prodOrient {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    (prodRel (F := F) κ₁ κ₂).Orientation where
  isOut := Sum.elim o₁.isOut o₂.isOut
  match_flip f hf := by
    cases f with
    | inl g =>
      change o₁.isOut (κ₁.match_ g) = !o₁.isOut g
      exact o₁.match_flip g (inl_mem_internal.mp hf)
    | inr g =>
      change o₂.isOut (κ₂.match_ g) = !o₂.isOut g
      exact o₂.match_flip g (inr_mem_internal.mp hf)
  pairing_flip f hf hp := by
    cases f with
    | inl g =>
      change o₁.isOut (W₁.pairing g) = !o₁.isOut g
      exact o₁.pairing_flip g (inl_mem_internal.mp hf)
        (inl_mem_internal.mp hp)
    | inr g =>
      change o₂.isOut (W₂.pairing g) = !o₂.isOut g
      exact o₂.pairing_flip g (inr_mem_internal.mp hf)
        (inr_mem_internal.mp hp)

/-! ### Circuit count additivity -/

/-- A walk of the product system started at a left flag stays left
and tracks the left component's walk. -/
theorem iterWalk_prodRel_inl (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    (g : W₁.Flag) (n : ℕ) :
    iterWalk (prodRel (F := F) κ₁ κ₂) (Sum.inl g) n =
      Sum.inl (iterWalk κ₁ g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterWalk_succ (prodRel (F := F) κ₁ κ₂) (Sum.inl g) n, ih,
      iterWalk_succ κ₁ g n]
    rfl

/-- The right analogue. -/
theorem iterWalk_prodRel_inr (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    (g : W₂.Flag) (n : ℕ) :
    iterWalk (prodRel (F := F) κ₁ κ₂) (Sum.inr g) n =
      Sum.inr (iterWalk κ₂ g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterWalk_succ (prodRel (F := F) κ₁ κ₂) (Sum.inr g) n, ih,
      iterWalk_succ κ₂ g n]
    rfl

/-- A left flag is periodic for the product system exactly when it is
periodic for the left factor: the walk never crosses components. -/
theorem inl_mem_periodic {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem} {g : W₁.Flag} :
    (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈
        (prodRel (F := F) κ₁ κ₂).periodicFlags ↔
      g ∈ κ₁.periodicFlags := by
  constructor
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      (prodRel κ₁ κ₂).mem_periodicFlags.mp h
    refine κ₁.mem_periodicFlags.mpr
      ⟨inl_mem_internal.mp hint, n, hn1, ?_, ?_⟩
    · intro j hj
      have hc := hcont j hj
      rw [iterWalk_prodRel_inl κ₁ κ₂ g j, pairing_inl] at hc
      exact inl_mem_internal.mp hc
    · have hh := hper
      rw [iterWalk_prodRel_inl κ₁ κ₂ g n] at hh
      exact Sum.inl.inj hh
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      κ₁.mem_periodicFlags.mp h
    refine (prodRel κ₁ κ₂).mem_periodicFlags.mpr
      ⟨inl_mem_internal.mpr hint, n, hn1, ?_, ?_⟩
    · intro j hj
      rw [iterWalk_prodRel_inl κ₁ κ₂ g j, pairing_inl]
      exact inl_mem_internal.mpr (hcont j hj)
    · rw [iterWalk_prodRel_inl κ₁ κ₂ g n, hper]

/-- A right flag is periodic for the product system exactly when it is
periodic for the right factor. -/
theorem inr_mem_periodic {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem} {g : W₂.Flag} :
    (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈
        (prodRel (F := F) κ₁ κ₂).periodicFlags ↔
      g ∈ κ₂.periodicFlags := by
  constructor
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      (prodRel κ₁ κ₂).mem_periodicFlags.mp h
    refine κ₂.mem_periodicFlags.mpr
      ⟨inr_mem_internal.mp hint, n, hn1, ?_, ?_⟩
    · intro j hj
      have hc := hcont j hj
      rw [iterWalk_prodRel_inr κ₁ κ₂ g j, pairing_inr] at hc
      exact inr_mem_internal.mp hc
    · have hh := hper
      rw [iterWalk_prodRel_inr κ₁ κ₂ g n] at hh
      exact Sum.inr.inj hh
  · intro h
    obtain ⟨hint, n, hn1, hcont, hper⟩ :=
      κ₂.mem_periodicFlags.mp h
    refine (prodRel κ₁ κ₂).mem_periodicFlags.mpr
      ⟨inr_mem_internal.mpr hint, n, hn1, ?_, ?_⟩
    · intro j hj
      rw [iterWalk_prodRel_inr κ₁ κ₂ g j, pairing_inr]
      exact inr_mem_internal.mpr (hcont j hj)
    · rw [iterWalk_prodRel_inr κ₁ κ₂ g n, hper]

/-- The product system's periodic flags are the disjoint sum of the
two factors' periodic flags. -/
noncomputable def periodicSumEquiv
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) :
    {f : (W₁.disjUnion W₂).Flag //
        f ∈ (prodRel (F := F) κ₁ κ₂).periodicFlags} ≃
      ({g : W₁.Flag // g ∈ κ₁.periodicFlags} ⊕
        {g : W₂.Flag // g ∈ κ₂.periodicFlags}) where
  toFun x :=
    match x with
    | ⟨Sum.inl g, h⟩ => Sum.inl ⟨g, inl_mem_periodic.mp h⟩
    | ⟨Sum.inr g, h⟩ => Sum.inr ⟨g, inr_mem_periodic.mp h⟩
  invFun x :=
    match x with
    | Sum.inl ⟨g, h⟩ => ⟨Sum.inl g, inl_mem_periodic.mpr h⟩
    | Sum.inr ⟨g, h⟩ => ⟨Sum.inr g, inr_mem_periodic.mpr h⟩
  left_inv x := by
    rcases x with ⟨f, h⟩
    cases f <;> rfl
  right_inv x := by
    rcases x with ⟨g, h⟩ | ⟨g, h⟩ <;> rfl

/-- Under that identification the product system's walk permutation is
the sum of the two factors' walk permutations. -/
theorem walkPermPeriodic_prodRel (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) :
    (prodRel (F := F) κ₁ κ₂).walkPermPeriodic =
      (periodicSumEquiv κ₁ κ₂).symm.permCongr
        (Equiv.sumCongr κ₁.walkPermPeriodic κ₂.walkPermPeriodic) := by
  ext ⟨f, hf⟩
  cases f with
  | inl g => rfl
  | inr g => rfl

/-- **Circuit counts add**: the product system's open circuit count
is the sum of the two components'.  Each component's orbit data is
even, so no halving correction survives the split. -/
theorem openCircuitCount_prodRel (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem) :
    (prodRel (F := F) κ₁ κ₂).openCircuitCount =
      κ₁.openCircuitCount + κ₂.openCircuitCount := by
  classical
  obtain ⟨a, ha⟩ := even_card_cycleType κ₁
  obtain ⟨b, hb⟩ := even_card_fixedPoints κ₁
  unfold RelTransitionSystem.openCircuitCount
  rw [walkPermPeriodic_prodRel κ₁ κ₂, cycleType_permCongr,
    cycleType_sumCongr, Multiset.card_add,
    card_fixedPoints_permCongr, card_fixedPoints_sumCongr]
  omega

end ProdSystems

/-! ## The through-product factorization -/

section ThroughSplit

open EdgeSubset

variable {α β : Type}

end ThroughSplit

end RS
