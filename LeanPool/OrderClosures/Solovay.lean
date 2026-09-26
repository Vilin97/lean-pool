/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass


/-!
# Solovay's complete Boolean algebra construction

This file formalizes the construction in Robert M. Solovay's *New Proof of a
Theorem of Gaifman and Hales*.  It realizes the resulting complete Boolean
algebra as the clopen algebra of its Stone space and develops the analytic
facts needed for the Gao--Leung counterexample.
-/

@[expose] public section

open Set

noncomputable section

namespace OrderClosures

universe u


/-- The regular-open completion of the open-set Boolean algebra, used as the
complete Boolean algebra in Solovay's construction. -/
abbrev RegularOpen (X : Type u) [TopologicalSpace X] :=
  Heyting.Regular (TopologicalSpace.Opens X)

/-- Supplies arbitrary suprema and infima on regular open sets; required for
complete-generation arguments below. -/
noncomputable instance regularOpenCompleteLattice
    (X : Type u) [TopologicalSpace X] : CompleteLattice (RegularOpen X) :=
  Heyting.Regular.gi.liftCompleteLattice

/-- Bundles the complete Boolean-algebra structure of regular open sets; used
as the algebra whose Stone spectrum forms the counterexample. -/
noncomputable instance regularOpenCompleteBooleanAlgebra
    (X : Type u) [TopologicalSpace X] : CompleteBooleanAlgebra (RegularOpen X) where
  __ := Heyting.Regular.instBooleanAlgebra
  __ := regularOpenCompleteLattice X

/-- Regards a clopen set as a regular open element; used to turn finite
cylinders into Boolean-algebra generators. -/
def regularOpenOfClopen {X : Type u} [TopologicalSpace X]
    (s : Set X) (hs : IsClopen s) : RegularOpen X := by
  let U : TopologicalSpace.Opens X := ⟨s, hs.2⟩
  let V : TopologicalSpace.Opens X := ⟨sᶜ, hs.1.isOpen_compl⟩
  have hUV : IsCompl U V := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff]
      apply TopologicalSpace.Opens.ext
      simp [U, V]
    · rw [codisjoint_iff]
      apply TopologicalSpace.Opens.ext
      simp [U, V]
  exact ⟨U, (congrArg (fun W ↦ Wᶜ) hUV.compl_eq).trans hUV.symm.compl_eq⟩

@[simp] theorem coe_regularOpenOfClopen {X : Type u} [TopologicalSpace X]
    (s : Set X) (hs : IsClopen s) :
    (((regularOpenOfClopen s hs : RegularOpen X) :
      TopologicalSpace.Opens X) : Set X) = s := rfl

/-- Reduces equality of regular open sets to equality of carriers; used to
simplify Boolean-algebra computations in the Solovay construction. -/
theorem regularOpen_ext {X : Type u} [TopologicalSpace X]
    {U V : RegularOpen X}
    (h : (((U : TopologicalSpace.Opens X) : Set X)) =
      (((V : TopologicalSpace.Opens X) : Set X))) : U = V := by
  apply Heyting.Regular.coe_injective
  exact TopologicalSpace.Opens.ext h

/-- Makes the regular-open constructor respect equality of clopen carriers;
used when rewriting cylinder identities. -/
theorem regularOpenOfClopen_congr {X : Type u} [TopologicalSpace X]
    {s t : Set X} (hs : IsClopen s) (ht : IsClopen t) (h : s = t) :
    regularOpenOfClopen s hs = regularOpenOfClopen t ht := by
  apply regularOpen_ext
  simpa only [coe_regularOpenOfClopen] using h

/-- Computes intersections of clopen sets inside the regular-open algebra;
used for finite cylinder meets and Boolean subalgebras. -/
theorem regularOpenOfClopen_inf {X : Type u} [TopologicalSpace X]
    (s t : Set X) (hs : IsClopen s) (ht : IsClopen t) :
    regularOpenOfClopen (s ∩ t) (hs.inter ht) =
      regularOpenOfClopen s hs ⊓ regularOpenOfClopen t ht := by
  apply regularOpen_ext
  rfl

/-- Computes complements of clopen sets inside the regular-open algebra;
used to show the cylinder-generated family is a Boolean subalgebra. -/
theorem regularOpenOfClopen_compl {X : Type u} [TopologicalSpace X]
    (s : Set X) (hs : IsClopen s) :
    regularOpenOfClopen sᶜ hs.compl = (regularOpenOfClopen s hs)ᶜ := by
  apply regularOpen_ext
  change sᶜ =
    ((((⟨s, hs.2⟩ : TopologicalSpace.Opens X)ᶜ :
      TopologicalSpace.Opens X)) : Set X)
  let U : TopologicalSpace.Opens X := ⟨s, hs.2⟩
  let V : TopologicalSpace.Opens X := ⟨sᶜ, hs.1.isOpen_compl⟩
  have hUV : IsCompl U V := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff]
      apply TopologicalSpace.Opens.ext
      simp [U, V]
    · rw [codisjoint_iff]
      apply TopologicalSpace.Opens.ext
      simp [U, V]
  rw [show (⟨s, hs.2⟩ : TopologicalSpace.Opens X) = U from rfl,
    hUV.compl_eq]
  rfl

/-- Expresses a clopen union as a supremum of regular-open elements; used to
derive the explicit Solovay generator formulas. -/
theorem regularOpenOfClopen_eq_sSup {X : Type u} [TopologicalSpace X]
    (S : Set (RegularOpen X)) (t : Set X) (ht : IsClopen t)
    (hunion : t = ⋃ U ∈ S,
      ((((U : RegularOpen X) : TopologicalSpace.Opens X) : Set X))) :
    regularOpenOfClopen t ht = sSup S := by
  apply le_antisymm
  · change (⟨t, ht.2⟩ : TopologicalSpace.Opens X) ≤
      ((sSup S : RegularOpen X) : TopologicalSpace.Opens X)
    intro x hx
    change x ∈ t at hx
    rw [hunion] at hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨U, hUS, hxU⟩
    exact (show U ≤ sSup S from le_sSup hUS) hxU
  · apply sSup_le
    intro U hUS
    change (U : TopologicalSpace.Opens X) ≤ ⟨t, ht.2⟩
    intro x hx
    change x ∈ t
    rw [hunion]
    simp only [Set.mem_iUnion]
    exact ⟨U, hUS, hx⟩

/-- Recovers a regular open set as the supremum of a family whose union is
dense in it; used in the proof that the Solovay generators are complete. -/
theorem regularOpen_eq_sSup_of_union {X : Type u} [TopologicalSpace X]
    (U : RegularOpen X) (S : Set (RegularOpen X))
    (hunion : (((U : TopologicalSpace.Opens X) : Set X)) = ⋃ V ∈ S,
      ((((V : RegularOpen X) : TopologicalSpace.Opens X) : Set X))) :
    U = sSup S := by
  apply le_antisymm
  · change (U : TopologicalSpace.Opens X) ≤
      ((sSup S : RegularOpen X) : TopologicalSpace.Opens X)
    intro x hx
    have hx' : x ∈ (((U : TopologicalSpace.Opens X) : Set X)) := hx
    rw [hunion] at hx'
    simp only [Set.mem_iUnion] at hx'
    rcases hx' with ⟨V, hVS, hxV⟩
    exact (show V ≤ sSup S from le_sSup hVS) hxV
  · apply sSup_le
    intro V hVS
    change (V : TopologicalSpace.Opens X) ≤
      (U : TopologicalSpace.Opens X)
    intro x hx
    have hx' : x ∈ ⋃ W ∈ S,
        ((((W : RegularOpen X) : TopologicalSpace.Opens X) : Set X)) := by
      simp only [Set.mem_iUnion]
      exact ⟨V, hVS, hx⟩
    rw [← hunion] at hx'
    exact hx'

section Solovay

variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]

/-- The countable product of the well-ordered index type on which the Solovay
cylinder algebra is constructed. -/
abbrev SolovayProduct := ℕ → Gamma

/-- The basic Solovay generator comparing coordinate `n` with `eta`; these
generators will completely generate the regular-open algebra. -/
def solovayA (n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f n = eta}
    ((isClopen_discrete {eta}).preimage (continuous_apply n))

/-- The finite-coordinate cylinder through `g`; used as the topological basis
recovered from the Solovay generators. -/
def solovayCylinderSet (F : Finset ℕ) (g : SolovayProduct Gamma) :
    Set (SolovayProduct Gamma) :=
  ⋂ i ∈ F, {f | f i = g i}

omit [LinearOrder Gamma] in
/-- Shows that every finite-coordinate Solovay cylinder is clopen; this allows
it to define an element of the regular-open Boolean algebra. -/
theorem isClopen_solovayCylinderSet (F : Finset ℕ)
    (g : SolovayProduct Gamma) : IsClopen (solovayCylinderSet Gamma F g) := by
  apply isClopen_biInter_finset
  intro i hi
  exact (isClopen_discrete {g i}).preimage (continuous_apply i)

/-- The regular-open element associated with a finite cylinder; used to prove
complete generation of every regular open set. -/
def solovayCylinder (F : Finset ℕ) (g : SolovayProduct Gamma) :
    RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen (solovayCylinderSet Gamma F g)
    (isClopen_solovayCylinderSet Gamma F g)

omit [LinearOrder Gamma] [TopologicalSpace Gamma] [DiscreteTopology Gamma] in
@[simp] theorem mem_solovayCylinderSet (F : Finset ℕ)
    (g f : SolovayProduct Gamma) :
    f ∈ solovayCylinderSet Gamma F g ↔ ∀ i ∈ F, f i = g i := by
  simp [solovayCylinderSet]

/-- Auxiliary coordinate-comparison element used to recover finite cylinders
from the basic `solovayA` generators. -/
def solovayB (m n : ℕ) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m ≤ f n}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 ≤ p.2})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))

/-- The regular-open event that coordinate `n` is strictly below `eta`; used
in the Boolean identities for the generators. -/
def solovayLT (n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f n < eta}
    ((isClopen_discrete {xi : Gamma | xi < eta}).preimage (continuous_apply n))

/-- The regular-open event that coordinate `n` is at most `eta`; used in the
well-founded recovery of exact coordinate values. -/
def solovayLE (n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f n ≤ eta}
    ((isClopen_discrete {xi : Gamma | xi ≤ eta}).preimage (continuous_apply n))

/-- Auxiliary comparison element combining two coordinates and a threshold;
used in the recursive cylinder-generation identities. -/
def solovayC (m n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m < f n → f m < eta}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 < p.2 → p.1 < eta})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))

/-- The strict comparison event between two coordinates; isolated for reuse
in the formulas for `solovayC` and `solovayBad`. -/
def solovayStrict (m n : ℕ) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m < f n}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 < p.2})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))

/-- The complement of a strict coordinate bound; used in exact-coordinate
cylinder formulas. -/
def solovayNotLT (m : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | ¬ f m < eta}
    ((isClopen_discrete {xi : Gamma | ¬ xi < eta}).preimage (continuous_apply m))

/-- The exceptional part of a coordinate comparison; separated so it can be
eliminated in the well-founded generator induction. -/
def solovayBad (m n : ℕ) (eta : Gamma) : RegularOpen (SolovayProduct Gamma) :=
  regularOpenOfClopen {f | f m < f n ∧ ¬ f m < eta}
    (by
      change IsClopen
        ((fun f : SolovayProduct Gamma ↦ (f m, f n)) ⁻¹'
          {p : Gamma × Gamma | p.1 < p.2 ∧ ¬ p.1 < eta})
      exact (isClopen_discrete _).preimage
        ((continuous_apply m).prodMk (continuous_apply n)))

/-- Closure predicate for a Boolean subalgebra under arbitrary suprema; used
to formulate complete generation by the Solovay family. -/
def IsCompleteBooleanSubalgebra {B : Type u} [CompleteBooleanAlgebra B]
    (L : BooleanSubalgebra B) : Prop :=
  ∀ S : Set B, S ⊆ L → sSup S ∈ L

/-- Derives closure under arbitrary infima from closure under arbitrary
suprema and complement; used repeatedly for the generated Boolean algebra. -/
theorem IsCompleteBooleanSubalgebra.sInf_mem {B : Type u}
    [CompleteBooleanAlgebra B] {L : BooleanSubalgebra B}
    (hL : IsCompleteBooleanSubalgebra L) (S : Set B) (hSL : S ⊆ L) :
    sInf S ∈ L := by
  have hcomp : Compl.compl '' S ⊆ L := by
    rintro _ ⟨x, hxS, rfl⟩
    exact L.compl_mem (hSL hxS)
  have hmem := L.compl_mem (hL _ hcomp)
  convert hmem using 1
  rw [compl_sSup']
  congr 1
  ext x
  simp

/-- Expresses the strict-order event as a supremum of basic generators; used
to place it in every complete subalgebra containing `solovayA`. -/
theorem solovayLT_eq_sSup (n : ℕ) (eta : Gamma) :
    solovayLT Gamma n eta =
      sSup (solovayA Gamma n '' Set.Iio eta) := by
  apply regularOpenOfClopen_eq_sSup
  ext f
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Iio, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨solovayA Gamma n (f n), ⟨f n, h, rfl⟩, rfl⟩
  · rintro ⟨U, ⟨eta', hη, rfl⟩, hf⟩
    change f n = eta' at hf
    exact hf ▸ hη

/-- Computes the event that one coordinate is strictly below another; used in
the recursive recovery of finite cylinders. -/
theorem solovayStrict_eq (m n : ℕ) :
    solovayStrict Gamma m n = (solovayB Gamma n m)ᶜ := by
  unfold solovayB
  rw [← regularOpenOfClopen_compl]
  apply regularOpenOfClopen_congr
  ext f
  simp

/-- Computes the complementary order event; used to build exact coordinate
conditions from the Solovay generators. -/
theorem solovayNotLT_eq (m : ℕ) (eta : Gamma) :
    solovayNotLT Gamma m eta = (solovayLT Gamma m eta)ᶜ := by
  unfold solovayLT
  rw [← regularOpenOfClopen_compl]
  apply regularOpenOfClopen_congr
  ext f
  simp

/-- Decomposes the exceptional comparison event into previously generated
pieces; used in the induction recovering cylinder elements. -/
theorem solovayBad_eq (m n : ℕ) (eta : Gamma) :
    solovayBad Gamma m n eta =
      solovayStrict Gamma m n ⊓ solovayNotLT Gamma m eta := by
  unfold solovayStrict solovayNotLT
  rw [← regularOpenOfClopen_inf]
  apply regularOpenOfClopen_congr
  rfl

/-- Gives the Boolean formula for the auxiliary comparison element `solovayC`;
used to derive the non-strict order event. -/
theorem solovayC_eq (m n : ℕ) (eta : Gamma) :
    solovayC Gamma m n eta = (solovayBad Gamma m n eta)ᶜ := by
  unfold solovayBad
  rw [← regularOpenOfClopen_compl]
  apply regularOpenOfClopen_congr
  ext f
  simp

/-- Expresses a non-strict coordinate bound as an infimum of comparison
elements; used in the well-founded generator induction. -/
theorem solovayLE_eq_sInf (n : ℕ) (eta : Gamma) :
    solovayLE Gamma n eta = sInf (Set.range fun m ↦ solovayC Gamma m n eta) := by
  apply le_antisymm
  · apply le_sInf
    intro U hU
    rcases hU with ⟨m, rfl⟩
    change (⟨{f : SolovayProduct Gamma | f n ≤ eta}, _⟩ :
      TopologicalSpace.Opens (SolovayProduct Gamma)) ≤
        ⟨{f : SolovayProduct Gamma | f m < f n → f m < eta}, _⟩
    intro f hf hmn
    exact hmn.trans_le hf
  · let W : TopologicalSpace.Opens (SolovayProduct Gamma) :=
      (sInf (Set.range fun m ↦ solovayC Gamma m n eta) :
        RegularOpen (SolovayProduct Gamma))
    change W ≤ ⟨{f : SolovayProduct Gamma | f n ≤ eta}, _⟩
    intro g hg
    change g n ≤ eta
    by_contra hgn
    have hetagn : eta < g n := lt_of_not_ge hgn
    rcases isOpen_pi_iff.mp W.2 g hg with ⟨F, v, hv, hvW⟩
    obtain ⟨m, hm⟩ := (insert n F).exists_nat_subset_range
    have hmF : m ∉ F := by
      intro hmF
      exact (Nat.lt_irrefl m)
        (Finset.mem_range.mp (hm (Finset.mem_insert_of_mem hmF)))
    have hmn : m ≠ n := by
      intro hmn
      subst n
      exact (Nat.lt_irrefl m)
        (Finset.mem_range.mp (hm (Finset.mem_insert_self m F)))
    let h : SolovayProduct Gamma := fun i ↦ if i = m then eta else g i
    have hhF : h ∈ (F : Set ℕ).pi v := by
      intro i hi
      rw [show h i = g i by simp [h, ne_of_mem_of_not_mem hi hmF]]
      exact (hv i (Finset.mem_coe.mp hi)).2
    have hhW : h ∈ W := hvW hhF
    have hhC : h ∈ (solovayC Gamma m n eta :
        TopologicalSpace.Opens (SolovayProduct Gamma)) :=
      (show sInf (Set.range fun k ↦ solovayC Gamma k n eta) ≤
          solovayC Gamma m n eta from sInf_le (Set.mem_range_self m)) hhW
    change h m < h n → h m < eta at hhC
    have hhm : h m = eta := by simp [h]
    have hhn : h n = g n := by simp [h, hmn.symm]
    have hhless : h m < h n := by simpa only [hhm, hhn] using hetagn
    have hout := hhC hhless
    rw [hhm] at hout
    exact (lt_irrefl eta) hout

/-- Gives the fundamental Boolean identity for a Solovay generator; used to
recover exact coordinate cylinders. -/
theorem solovayA_eq (n : ℕ) (eta : Gamma) :
    solovayA Gamma n eta =
      solovayLE Gamma n eta ⊓ (solovayLT Gamma n eta)ᶜ := by
  rw [← solovayNotLT_eq]
  unfold solovayLE solovayNotLT
  rw [← regularOpenOfClopen_inf]
  apply regularOpenOfClopen_congr
  ext f
  simp [le_antisymm_iff]

/-- Performs the well-founded step placing all `solovayA` elements in a
complete subalgebra generated by the basic family. -/
theorem solovayA_mem_of_generators [WellFoundedLT Gamma]
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hcomplete : IsCompleteBooleanSubalgebra L)
    (hB : ∀ m n, solovayB Gamma m n ∈ L) :
    ∀ eta n, solovayA Gamma n eta ∈ L := by
  intro eta
  induction eta using WellFoundedLT.induction with
  | ind eta ih =>
      intro n
      have hLT : ∀ k, solovayLT Gamma k eta ∈ L := by
        intro k
        rw [solovayLT_eq_sSup]
        apply hcomplete
        rintro U ⟨theta, htheta, rfl⟩
        exact ih theta htheta k
      have hC : ∀ m, solovayC Gamma m n eta ∈ L := by
        intro m
        rw [solovayC_eq, solovayBad_eq, solovayStrict_eq,
          solovayNotLT_eq]
        exact L.compl_mem (L.inf_mem (L.compl_mem (hB n m))
          (L.compl_mem (hLT m)))
      have hLE : solovayLE Gamma n eta ∈ L := by
        rw [solovayLE_eq_sInf]
        apply hcomplete.sInf_mem
        rintro U ⟨m, rfl⟩
        exact hC m
      rw [solovayA_eq]
      exact L.inf_mem hLE (L.compl_mem (hLT n))

omit [LinearOrder Gamma] in
/-- Splits a finite cylinder after inserting one coordinate; used for the
induction showing all finite cylinders are generated. -/
theorem solovayCylinder_insert (i : ℕ) (F : Finset ℕ)
    (g : SolovayProduct Gamma) :
    solovayCylinder Gamma (insert i F) g =
      solovayA Gamma i (g i) ⊓ solovayCylinder Gamma F g := by
  apply regularOpen_ext
  change solovayCylinderSet Gamma (insert i F) g =
    {f | f i = g i} ∩ solovayCylinderSet Gamma F g
  ext f
  simp [solovayCylinderSet]

omit [LinearOrder Gamma] in
/-- Places every finite Solovay cylinder in a complete subalgebra containing
the generators; used to recover arbitrary regular open sets. -/
theorem solovayCylinder_mem
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hA : ∀ n eta, solovayA Gamma n eta ∈ L) :
    ∀ F g, solovayCylinder Gamma F g ∈ L := by
  intro F
  induction F using Finset.induction_on with
  | empty =>
      intro g
      have htop : solovayCylinder Gamma ∅ g = ⊤ := by
        apply regularOpen_ext
        simp [solovayCylinder, solovayCylinderSet]
      rw [htop]
      exact L.top_mem
  | @insert i F hi ih =>
      intro g
      rw [solovayCylinder_insert]
      exact L.inf_mem (hA i (g i)) (ih g)

/-- The basic cylinders lying below a regular open element; their supremum is
used to reconstruct that element. -/
def solovayCylindersBelow (U : RegularOpen (SolovayProduct Gamma)) :
    Set (RegularOpen (SolovayProduct Gamma)) :=
  {V | ∃ F g, V = solovayCylinder Gamma F g ∧
    ((((V : RegularOpen (SolovayProduct Gamma)) :
      TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma))) ⊆
      (((U : TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma)))}

omit [LinearOrder Gamma] in
/-- Represents the points of a regular open set by cylinders lying below it;
used to express that set as a supremum of generated cylinder elements. -/
theorem solovay_union_cylinders_below
    (U : RegularOpen (SolovayProduct Gamma)) :
    (((U : TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma))) =
      ⋃ V ∈ solovayCylindersBelow Gamma U,
        ((((V : RegularOpen (SolovayProduct Gamma)) :
          TopologicalSpace.Opens (SolovayProduct Gamma)) :
            Set (SolovayProduct Gamma))) := by
  ext x
  constructor
  · intro hxU
    rcases isOpen_pi_iff.mp
        (U : TopologicalSpace.Opens (SolovayProduct Gamma)).2 x hxU with
      ⟨F, v, hv, hvU⟩
    let V := solovayCylinder Gamma F x
    have hVU :
        ((((V : RegularOpen (SolovayProduct Gamma)) :
          TopologicalSpace.Opens (SolovayProduct Gamma)) :
            Set (SolovayProduct Gamma))) ⊆
          (((U : TopologicalSpace.Opens (SolovayProduct Gamma)) :
            Set (SolovayProduct Gamma))) := by
      intro y hy
      apply hvU
      intro i hi
      have hyi : y i = x i := by
        apply (mem_solovayCylinderSet Gamma F x y).mp
          (show y ∈ solovayCylinderSet Gamma F x by exact hy)
        exact Finset.mem_coe.mp hi
      rw [hyi]
      exact (hv i (Finset.mem_coe.mp hi)).2
    have hVS : V ∈ solovayCylindersBelow Gamma U :=
      ⟨F, x, rfl, hVU⟩
    simp only [Set.mem_iUnion]
    refine ⟨V, hVS, ?_⟩
    exact (mem_solovayCylinderSet Gamma F x x).mpr fun _ _ ↦ rfl
  · simp only [Set.mem_iUnion]
    rintro ⟨V, ⟨F, g, rfl, hVU⟩, hxV⟩
    exact hVU hxV

omit [LinearOrder Gamma] in
/-- Shows every regular open element belongs to any complete subalgebra
containing the Solovay generators; this proves generation of the full algebra. -/
theorem solovay_every_regularOpen_mem
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hcomplete : IsCompleteBooleanSubalgebra L)
    (hA : ∀ n eta, solovayA Gamma n eta ∈ L)
    (U : RegularOpen (SolovayProduct Gamma)) : U ∈ L := by
  rw [regularOpen_eq_sSup_of_union U (solovayCylindersBelow Gamma U)
    (solovay_union_cylinders_below Gamma U)]
  apply hcomplete
  intro V hV
  rcases hV with ⟨F, g, rfl, hsub⟩
  exact solovayCylinder_mem Gamma L hA F g

/-- Packages the preceding membership argument as complete generation of the
regular-open Boolean algebra; used in the Gao counterexample. -/
theorem solovay_generates_regularOpen [WellFoundedLT Gamma]
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hcomplete : IsCompleteBooleanSubalgebra L)
    (hB : ∀ m n, solovayB Gamma m n ∈ L) : L = ⊤ := by
  apply BooleanSubalgebra.ext
  intro U
  simp only [BooleanSubalgebra.mem_top, iff_true]
  apply solovay_every_regularOpen_mem Gamma L hcomplete
  exact fun n eta ↦ solovayA_mem_of_generators Gamma L hcomplete hB eta n

/-- Shows one coordinate layer of Solovay generators is injectively indexed;
used for the density-character lower bound. -/
theorem solovayA_injective (n : ℕ) : Function.Injective (solovayA Gamma n) := by
  intro eta theta h
  by_contra hne
  have hsets := congrArg
    (fun U : RegularOpen (SolovayProduct Gamma) ↦
      (((U : TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma)))) h
  change {f : SolovayProduct Gamma | f n = eta} = {f | f n = theta} at hsets
  let f : SolovayProduct Gamma := fun _ ↦ eta
  have hf : f ∈ {g : SolovayProduct Gamma | g n = eta} := rfl
  rw [hsets] at hf
  exact hne hf

end Solovay

section BooleanStone

variable (B : Type u) [BooleanAlgebra B]

/-- The bounded-lattice equations defining a two-valued Stone point; used to
realize the Stone spectrum as a closed Cantor-cube subspace. -/
def IsBooleanStonePoint (f : B → Bool) : Prop :=
  f ⊥ = ⊥ ∧ f ⊤ = ⊤ ∧
    (∀ a b, f (a ⊓ b) = f a ⊓ f b) ∧
    (∀ a b, f (a ⊔ b) = f a ⊔ f b)

/-- The Stone spectrum of a Boolean algebra, represented by its two-valued
bounded-lattice homomorphisms. -/
abbrev BooleanStone := {f : B → Bool // IsBooleanStonePoint B f}

/-- Proves that the Boolean-homomorphism equations define a closed subset of
the Cantor cube; used to obtain compactness of the Stone spectrum. -/
theorem isClosed_isBooleanStonePoint :
    IsClosed {f : B → Bool | IsBooleanStonePoint B f} := by
  unfold IsBooleanStonePoint
  repeat' apply IsClosed.inter
  · exact isClosed_eq (continuous_apply ⊥) continuous_const
  · exact isClosed_eq (continuous_apply ⊤) continuous_const
  · change IsClosed ({f : B → Bool | ∀ a b, f (a ⊓ b) = f a ⊓ f b} :
      Set (B → Bool))
    rw [show {f : B → Bool | ∀ a b, f (a ⊓ b) = f a ⊓ f b} =
        ⋂ a, ⋂ b, {f : B → Bool | f (a ⊓ b) = f a ⊓ f b} by
      ext f
      simp]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a ⊓ b))
        (show Continuous (fun f : B → Bool ↦ f a ⊓ f b) by fun_prop)
  · change IsClosed ({f : B → Bool | ∀ a b, f (a ⊔ b) = f a ⊔ f b} :
      Set (B → Bool))
    rw [show {f : B → Bool | ∀ a b, f (a ⊔ b) = f a ⊔ f b} =
        ⋂ a, ⋂ b, {f : B → Bool | f (a ⊔ b) = f a ⊔ f b} by
      ext f
      simp]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a ⊔ b))
        (show Continuous (fun f : B → Bool ↦ f a ⊔ f b) by fun_prop)

/-- Compactness inherited from the closed realization inside the Cantor cube;
used throughout the continuous-function construction. -/
noncomputable instance booleanStoneCompactSpace : CompactSpace (BooleanStone B) :=
  isCompact_iff_compactSpace.mp (isClosed_isBooleanStonePoint B).isCompact

/-- The Stone spectrum is Hausdorff as a subspace of a product of discrete
two-point spaces. -/
instance booleanStoneT2Space : T2Space (BooleanStone B) := inferInstance

/-- The clopen set of Stone points evaluating a Boolean element to true; used
for the faithful Stone representation. -/
def booleanStoneClopen (b : B) : Set (BooleanStone B) :=
  {x | x.1 b = true}

/-- Shows that evaluation at a Boolean element defines a clopen subset of the
Stone spectrum; used for the clopen representation and its indicators. -/
theorem isClopen_booleanStoneClopen (b : B) :
    IsClopen (booleanStoneClopen B b) :=
  (isClopen_discrete {true}).preimage
    ((continuous_apply b).comp continuous_subtype_val)

/-- Bundles a Stone point as a bounded-lattice homomorphism; used to access
its algebraic laws uniformly. -/
def booleanStoneHom (x : BooleanStone B) : BoundedLatticeHom B Bool where
  toFun := x.1
  map_inf' := x.2.2.2.1
  map_sup' := x.2.2.2.2
  map_top' := x.2.2.1
  map_bot' := x.2.1

@[simp] theorem booleanStone_apply_bot (x : BooleanStone B) : x.1 ⊥ = false :=
  x.2.1

@[simp] theorem booleanStone_apply_top (x : BooleanStone B) : x.1 ⊤ = true :=
  x.2.2.1

@[simp] theorem booleanStone_apply_inf (x : BooleanStone B) (a b : B) :
    x.1 (a ⊓ b) = x.1 a ⊓ x.1 b := x.2.2.2.1 a b

@[simp] theorem booleanStone_apply_sup (x : BooleanStone B) (a b : B) :
    x.1 (a ⊔ b) = x.1 a ⊔ x.1 b := x.2.2.2.2 a b

@[simp] theorem booleanStone_apply_compl (x : BooleanStone B) (a : B) :
    x.1 aᶜ = (x.1 a)ᶜ := by
  exact map_compl' (booleanStoneHom B x) a

/-- Constructs the Stone point associated with a prime ideal; used to separate
Boolean elements when an order relation fails. -/
noncomputable def booleanStonePointOfPrime (J : Order.Ideal B)
    (hJ : Order.Ideal.IsPrime J) : BooleanStone B := by
  classical
  exact ⟨fun b ↦ decide (b ∉ J), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [J.bot_mem]
    · simp [hJ.toIsProper.top_notMem]
    · intro a b
      by_cases ha : a ∈ J
      · have hab : a ⊓ b ∈ J := J.lower inf_le_left ha
        simp [ha, hab]
      · by_cases hb : b ∈ J
        · have hab : a ⊓ b ∈ J := J.lower inf_le_right hb
          simp [ha, hb, hab]
        · have hab : a ⊓ b ∉ J := fun h ↦ (hJ.mem_or_mem h).elim ha hb
          simp [ha, hb, hab]
    · intro a b
      by_cases ha : a ∈ J
      · by_cases hb : b ∈ J
        · have hab : a ⊔ b ∈ J := J.sup_mem ha hb
          simp [ha, hb, hab]
        · have hab : a ⊔ b ∉ J := by
            simp [Order.Ideal.sup_mem_iff, ha, hb]
          simp [ha, hb, hab]
      · have hab : a ⊔ b ∉ J := by
          simp [Order.Ideal.sup_mem_iff, ha]
        simp [ha, hab]⟩

/-- Separates a failed Boolean inequality by a Stone point; used to prove
faithfulness of the clopen representation. -/
theorem exists_booleanStonePoint_of_not_le {a b : B} (hab : ¬ a ≤ b) :
    ∃ x : BooleanStone B, x.1 a = true ∧ x.1 b = false := by
  let F : Order.PFilter B := Order.PFilter.principal a
  let I : Order.Ideal B := Order.Ideal.principal b
  have hFI : Disjoint (F : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro c hcF hcI
    exact hab ((Order.PFilter.mem_principal.mp hcF).trans
      (Order.Ideal.mem_principal.mp hcI))
  rcases DistribLattice.prime_ideal_of_disjoint_filter_ideal hFI with
    ⟨J, hJ, hIJ, hFJ⟩
  have hbJ : b ∈ J := hIJ Order.Ideal.mem_principal_self
  have haJ : a ∉ J := by
    intro haJ
    exact Set.disjoint_left.mp hFJ (Order.PFilter.mem_principal.mpr le_rfl) haJ
  refine ⟨booleanStonePointOfPrime B J hJ, ?_, ?_⟩
  · simp [booleanStonePointOfPrime, haJ]
  · simp [booleanStonePointOfPrime, hbJ]

/-- Identifies Boolean order with inclusion of the corresponding Stone
clopens; used for injectivity and order computations. -/
theorem booleanStoneClopen_subset_iff {a b : B} :
    booleanStoneClopen B a ⊆ booleanStoneClopen B b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    rcases exists_booleanStonePoint_of_not_le B hab with ⟨x, hxa, hxb⟩
    exact Bool.false_ne_true (hxb.symm.trans (h hxa))
  · intro hab x hxa
    change x.1 b = true
    have hmap : x.1 a ≤ x.1 b :=
      OrderHomClass.monotone (booleanStoneHom B x) hab
    rw [hxa] at hmap
    exact top_unique hmap

/-- Proves injectivity of the Stone clopen representation; used to embed the
complete Boolean algebra into continuous functions. -/
theorem booleanStoneClopen_injective :
    Function.Injective (booleanStoneClopen B) := by
  intro a b hab
  apply le_antisymm
  · exact booleanStoneClopen_subset_iff B |>.mp (by rw [hab])
  · exact booleanStoneClopen_subset_iff B |>.mp (by rw [hab])

@[simp] theorem booleanStoneClopen_top :
    booleanStoneClopen B ⊤ = Set.univ := by
  ext x
  simp [booleanStoneClopen]

@[simp] theorem booleanStoneClopen_inf (a b : B) :
    booleanStoneClopen B (a ⊓ b) =
      booleanStoneClopen B a ∩ booleanStoneClopen B b := by
  ext x
  simp [booleanStoneClopen]

@[simp] theorem booleanStoneClopen_compl (a : B) :
    booleanStoneClopen B aᶜ = (booleanStoneClopen B a)ᶜ := by
  ext x
  simp [booleanStoneClopen]

/-- Selects `b` or its complement according to a Stone coordinate; used to
encode signed finite cylinders as Boolean elements. -/
def booleanStoneSignedCoordinate (x : BooleanStone B) (b : B) : B :=
  if x.1 b = true then b else bᶜ

/-- Evaluates membership in a signed-coordinate cylinder through its Boolean
element; used to translate finite Cantor cylinders to Stone clopens. -/
theorem booleanStoneClopen_signedCoordinate (x : BooleanStone B) (b : B) :
    booleanStoneClopen B (booleanStoneSignedCoordinate B x b) =
      {y | y.1 b = x.1 b} := by
  ext y
  by_cases hx : x.1 b = true
  · simp [booleanStoneSignedCoordinate, hx, booleanStoneClopen]
  · simp [booleanStoneSignedCoordinate, hx, booleanStoneClopen]

/-- The finite meet encoding the Cantor cylinder through a Stone point; used
to produce represented clopen neighborhood bases. -/
def booleanStoneCylinderElement (F : Finset B) (x : BooleanStone B) : B :=
  F.inf (booleanStoneSignedCoordinate B x)

/-- Identifies a finite Stone-space cylinder with the clopen represented by
its Boolean cylinder element; used to prove the clopen basis theorem. -/
theorem booleanStoneClopen_cylinderElement (F : Finset B)
    (x : BooleanStone B) :
    booleanStoneClopen B (booleanStoneCylinderElement B F x) =
      {y | ∀ b ∈ F, y.1 b = x.1 b} := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [booleanStoneCylinderElement]
  | @insert b F hb ih =>
      unfold booleanStoneCylinderElement
      change booleanStoneClopen B (F.inf (booleanStoneSignedCoordinate B x)) =
        {y | ∀ b ∈ F, y.1 b = x.1 b} at ih
      rw [Finset.inf_insert, booleanStoneClopen_inf,
        booleanStoneClopen_signedCoordinate, ih]
      ext y
      simp

/-- Refines every neighborhood of a Stone point to a represented clopen;
used in extremal disconnectedness and point-separation arguments. -/
theorem booleanStone_clopen_basis {U : Set (BooleanStone B)}
    (hU : IsOpen U) {x : BooleanStone B} (hxU : x ∈ U) :
    ∃ b : B, x ∈ booleanStoneClopen B b ∧ booleanStoneClopen B b ⊆ U := by
  rcases isOpen_induced_iff.mp hU with ⟨V, hV, hVU⟩
  have hxV : x.1 ∈ V := by
    have : x ∈ Subtype.val ⁻¹' V := by simpa [hVU] using hxU
    exact this
  rcases isOpen_pi_iff.mp hV x.1 hxV with ⟨F, v, hv, hvV⟩
  refine ⟨booleanStoneCylinderElement B F x, ?_, ?_⟩
  · rw [booleanStoneClopen_cylinderElement]
    exact fun _ _ ↦ rfl
  · intro y hy
    have hycoord : ∀ b ∈ F, y.1 b = x.1 b := by
      rwa [booleanStoneClopen_cylinderElement] at hy
    have hyV : y.1 ∈ V := by
      apply hvV
      intro b hb
      rw [hycoord b (Finset.mem_coe.mp hb)]
      exact (hv b (Finset.mem_coe.mp hb)).2
    have : y ∈ Subtype.val ⁻¹' V := hyV
    rwa [hVU] at this

end BooleanStone

section CompleteBooleanStone

variable (B : Type u) [CompleteBooleanAlgebra B]

/-- Supplies extremal disconnectedness from completeness of the Boolean
algebra; needed for continuous suprema in `C(BooleanStone B, ℝ)`. -/
noncomputable instance booleanStoneExtremallyDisconnected :
    ExtremallyDisconnected (BooleanStone B) where
  open_closure U hU := by
    let S : Set B := {b | booleanStoneClopen B b ⊆ U}
    let c : B := sSup S
    have hUc : U ⊆ booleanStoneClopen B c := by
      intro x hxU
      rcases booleanStone_clopen_basis B hU hxU with ⟨b, hxb, hbU⟩
      have hbS : b ∈ S := hbU
      exact (booleanStoneClopen_subset_iff B).mpr (le_sSup hbS) hxb
    have hclosure_le : closure U ⊆ booleanStoneClopen B c :=
      closure_minimal hUc (isClopen_booleanStoneClopen B c).1
    have hc_le : booleanStoneClopen B c ⊆ closure U := by
      intro x hxc
      by_contra hxclosure
      have hxopen : x ∈ (closure U)ᶜ := hxclosure
      rcases booleanStone_clopen_basis B (isOpen_compl_iff.mpr isClosed_closure)
          hxopen with ⟨d, hxd, hd⟩
      have hcd : c ≤ dᶜ := by
        apply sSup_le
        intro b hbS
        apply (booleanStoneClopen_subset_iff B).mp
        intro y hyb
        rw [booleanStoneClopen_compl]
        intro hyd
        have hyU : y ∈ U := hbS hyb
        have hyclosure : y ∈ closure U := subset_closure hyU
        exact (hd hyd) hyclosure
      have hxccompl : x ∈ booleanStoneClopen B dᶜ :=
        (booleanStoneClopen_subset_iff B).mpr hcd hxc
      rw [booleanStoneClopen_compl] at hxccompl
      exact hxccompl hxd
    rw [Set.Subset.antisymm hclosure_le hc_le]
    exact (isClopen_booleanStoneClopen B c).2

end CompleteBooleanStone

section OrderCompleteCofK

variable (K : Type u) [TopologicalSpace K] [ExtremallyDisconnected K]

/-- The union of strict rational upper-level sets of a function family; used
as the raw level set for the continuous supremum. -/
def continuousFamilyLevelOpen (A : Set C(K, ℝ)) (q : ℚ) : Set K :=
  ⋃ f ∈ A, f ⁻¹' Set.Ioi (q : ℝ)

omit [ExtremallyDisconnected K] in
/-- Shows that a rational strict upper-level set of a continuous family is
open; used to regularize level sets in the supremum construction. -/
theorem isOpen_continuousFamilyLevelOpen (A : Set C(K, ℝ)) (q : ℚ) :
    IsOpen (continuousFamilyLevelOpen K A q) := by
  apply isOpen_iUnion
  intro f
  apply isOpen_iUnion
  intro hf
  exact isOpen_Ioi.preimage f.continuous

/-- The closure of a family level set, made clopen by extremal disconnectedness;
used to define pointwise rational cuts. -/
def continuousFamilyRegularizedLevel (A : Set C(K, ℝ)) (q : ℚ) : Set K :=
  closure (continuousFamilyLevelOpen K A q)

/-- Uses extremal disconnectedness to make regularized family level sets
clopen; needed to assemble a continuous supremum. -/
theorem isClopen_continuousFamilyRegularizedLevel
    (A : Set C(K, ℝ)) (q : ℚ) :
    IsClopen (continuousFamilyRegularizedLevel K A q) :=
  ⟨isClosed_closure, ExtremallyDisconnected.open_closure _
    (isOpen_continuousFamilyLevelOpen K A q)⟩

/-- Rational thresholds whose regularized level contains `x`; their supremum
defines the candidate least upper bound. -/
def continuousFamilyCutValues (A : Set C(K, ℝ)) (x : K) : Set ℝ :=
  ((fun q : ℚ ↦ (q : ℝ)) ''
    {q | x ∈ continuousFamilyRegularizedLevel K A q})

/-- The real supremum of the rational cut values at a point; later shown
continuous and bundled as `continuousFamilySup`. -/
noncomputable def continuousFamilySupValue (A : Set C(K, ℝ)) (x : K) : ℝ :=
  sSup (continuousFamilyCutValues K A x)

omit [ExtremallyDisconnected K] in
/-- Shows that regularized upper-level sets decrease with the threshold; used
to prove consistency of the cut-value construction. -/
theorem continuousFamilyRegularizedLevel_antitone (A : Set C(K, ℝ)) :
    Antitone (continuousFamilyRegularizedLevel K A) := by
  intro q r hqr
  apply closure_mono
  intro x hx
  simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_Ioi] at hx ⊢
  rcases hx with ⟨f, hfA, hrfx⟩
  exact ⟨f, hfA, (Rat.cast_le.mpr hqr).trans_lt hrfx⟩

omit [ExtremallyDisconnected K] in
/-- Supplies rational cut values at each point for a nonempty family; needed
to define the pointwise cut supremum. -/
theorem continuousFamilyCutValues_nonempty {A : Set C(K, ℝ)}
    (hA : A.Nonempty) (x : K) : (continuousFamilyCutValues K A x).Nonempty := by
  rcases hA with ⟨f, hfA⟩
  rcases exists_rat_lt (f x) with ⟨q, hq⟩
  refine ⟨(q : ℝ), ⟨q, ?_, rfl⟩⟩
  apply subset_closure
  simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_Ioi]
  exact ⟨f, hfA, hq⟩

omit [ExtremallyDisconnected K] in
/-- Bounds the rational cut values using a common upper bound of the family;
used to make their real supremum well-defined. -/
theorem continuousFamilyCutValues_bddAbove {A : Set C(K, ℝ)}
    {h : C(K, ℝ)} (hh : h ∈ upperBounds A) (x : K) :
    BddAbove (continuousFamilyCutValues K A x) := by
  refine ⟨h x, ?_⟩
  rintro r ⟨q, hxq, rfl⟩
  have hopen_le : continuousFamilyLevelOpen K A q ⊆
      h ⁻¹' Set.Ici (q : ℝ) := by
    intro y hy
    simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_Ioi] at hy
    rcases hy with ⟨f, hfA, hqf⟩
    exact le_of_lt (hqf.trans_le (hh hfA y))
  have hclosed : IsClosed (h ⁻¹' Set.Ici (q : ℝ)) :=
    isClosed_Ici.preimage h.continuous
  exact (closure_minimal hopen_le hclosed hxq)

omit [ExtremallyDisconnected K] in
/-- Bounds every cut value by any continuous upper bound of the family; used
to prove minimality of the constructed supremum. -/
theorem continuousFamilyCutValue_le_upperBound {A : Set C(K, ℝ)}
    (hA : A.Nonempty) {h : C(K, ℝ)} (hh : h ∈ upperBounds A) (x : K) :
    continuousFamilySupValue K A x ≤ h x := by
  apply csSup_le (continuousFamilyCutValues_nonempty K hA x)
  rintro r ⟨q, hxq, rfl⟩
  have hopen_le : continuousFamilyLevelOpen K A q ⊆
      h ⁻¹' Set.Ici (q : ℝ) := by
    intro y hy
    simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_Ioi] at hy
    rcases hy with ⟨f, hfA, hqf⟩
    exact le_of_lt (hqf.trans_le (hh hfA y))
  exact closure_minimal hopen_le (isClosed_Ici.preimage h.continuous) hxq

/-- Proves continuity of the cut-defined supremum value; this allows it to be
bundled as `continuousFamilySup`. -/
theorem continuous_continuousFamilySupValue {A : Set C(K, ℝ)}
    (hA : A.Nonempty) (hAbdd : BddAbove A) :
    Continuous (continuousFamilySupValue K A) := by
  rcases hAbdd with ⟨h, hh⟩
  apply continuous_iff_lower_upperSemicontinuous.mpr
  constructor
  · rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro a
    rw [show continuousFamilySupValue K A ⁻¹' Set.Ioi a =
        ⋃ q : ℚ, ⋃ (_ : a < (q : ℝ)),
          continuousFamilyRegularizedLevel K A q by
      ext x
      constructor
      · intro hx
        have hbdd := continuousFamilyCutValues_bddAbove K hh x
        have hne := continuousFamilyCutValues_nonempty K hA x
        rcases (lt_csSup_iff hbdd hne).mp hx with ⟨r, hr, har⟩
        rcases hr with ⟨q, hxq, rfl⟩
        simp only [Set.mem_iUnion]
        exact ⟨q, har, hxq⟩
      · simp only [Set.mem_iUnion]
        rintro ⟨q, haq, hxq⟩
        exact haq.trans_le (le_csSup
          (continuousFamilyCutValues_bddAbove K hh x) ⟨q, hxq, rfl⟩)]
    apply isOpen_iUnion
    intro q
    apply isOpen_iUnion
    intro haq
    exact (isClopen_continuousFamilyRegularizedLevel K A q).2
  · rw [upperSemicontinuous_iff_isOpen_preimage]
    intro a
    rw [show continuousFamilySupValue K A ⁻¹' Set.Iio a =
        ⋃ q : ℚ, ⋃ (_ : (q : ℝ) < a),
          (continuousFamilyRegularizedLevel K A q)ᶜ by
      ext x
      constructor
      · intro hx
        change continuousFamilySupValue K A x < a at hx
        rcases exists_rat_btwn hx with ⟨q, hgq, hqa⟩
        simp only [Set.mem_iUnion, Set.mem_compl_iff]
        refine ⟨q, hqa, ?_⟩
        intro hxq
        have hqg : (q : ℝ) ≤ continuousFamilySupValue K A x :=
          le_csSup (continuousFamilyCutValues_bddAbove K hh x)
            ⟨q, hxq, rfl⟩
        exact (not_le_of_gt hgq) hqg
      · simp only [Set.mem_iUnion, Set.mem_compl_iff]
        rintro ⟨q, hqa, hxq⟩
        have hgq : continuousFamilySupValue K A x ≤ (q : ℝ) := by
          apply csSup_le (continuousFamilyCutValues_nonempty K hA x)
          rintro r ⟨q', hxq', rfl⟩
          by_contra hq'q
          have hqq' : q < q' := Rat.cast_lt.mp (lt_of_not_ge hq'q)
          exact hxq (continuousFamilyRegularizedLevel_antitone K A
            (le_of_lt hqq') hxq')
        exact hgq.trans_lt hqa]
    apply isOpen_iUnion
    intro q
    apply isOpen_iUnion
    intro hqa
    exact (isClopen_continuousFamilyRegularizedLevel K A q).1.isOpen_compl

/-- Bundles the cut-defined pointwise supremum as a continuous function; used
to prove order completeness of the continuous-function lattice. -/
noncomputable def continuousFamilySup (A : Set C(K, ℝ))
    (hA : A.Nonempty) (hAbdd : BddAbove A) : C(K, ℝ) :=
  ⟨continuousFamilySupValue K A,
    continuous_continuousFamilySupValue K hA hAbdd⟩

/-- Verifies that the constructed continuous function is the least upper bound
of the family; used to prove order completeness of `C(K, ℝ)`. -/
theorem continuousFamilySup_isLUB (A : Set C(K, ℝ))
    (hA : A.Nonempty) (hAbdd : BddAbove A) :
    IsLUB A (continuousFamilySup K A hA hAbdd) := by
  rcases hAbdd with ⟨h, hh⟩
  constructor
  · intro f hfA x
    change f x ≤ continuousFamilySupValue K A x
    by_contra hfg
    have hgf : continuousFamilySupValue K A x < f x := lt_of_not_ge hfg
    rcases exists_rat_btwn hgf with ⟨q, hgq, hqf⟩
    have hxq : x ∈ continuousFamilyRegularizedLevel K A q := by
      apply subset_closure
      simp only [continuousFamilyLevelOpen, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_Ioi]
      exact ⟨f, hfA, hqf⟩
    have hqg : (q : ℝ) ≤ continuousFamilySupValue K A x :=
      le_csSup (continuousFamilyCutValues_bddAbove K hh x)
        ⟨q, hxq, rfl⟩
    exact (not_le_of_gt hgq) hqg
  · intro k hk x
    exact continuousFamilyCutValue_le_upperBound K hA hk x

/-- Packages the continuous-family supremum construction as order completeness
of continuous real functions on an extremally disconnected compact space. -/
theorem isOrderComplete_continuousMap : IsOrderComplete C(K, ℝ) := by
  intro A hA hAbdd
  exact ⟨continuousFamilySup K A hA hAbdd,
    continuousFamilySup_isLUB K A hA hAbdd⟩

end OrderCompleteCofK

section ClopenIndicators

variable (K : Type u) [TopologicalSpace K]

/-- The continuous zero-one indicator of a clopen set; used to embed Boolean
clopens into the vector lattice of continuous functions. -/
noncomputable def clopenIndicator (s : Set K) (hs : IsClopen s) : C(K, ℝ) where
  toFun := s.indicator 1
  continuous_toFun :=
    continuous_indicator (by simp [hs]) continuous_const.continuousOn

@[simp] theorem clopenIndicator_apply_mem (s : Set K) (hs : IsClopen s)
    {x : K} (hx : x ∈ s) : clopenIndicator K s hs x = 1 := by
  simp [clopenIndicator, hx]

@[simp] theorem clopenIndicator_apply_notMem (s : Set K) (hs : IsClopen s)
    {x : K} (hx : x ∉ s) : clopenIndicator K s hs x = 0 := by
  simp [clopenIndicator, hx]

@[simp] theorem clopenIndicator_empty :
    clopenIndicator K ∅ isClopen_empty = 0 := by
  ext x
  simp [clopenIndicator]

/-- Computes the infimum of two clopen indicators; used to make Boolean
indicators compatible with lattice operations. -/
theorem clopenIndicator_inter (s t : Set K) (hs : IsClopen s) (ht : IsClopen t) :
    clopenIndicator K (s ∩ t) (hs.inter ht) =
      clopenIndicator K s hs ⊓ clopenIndicator K t ht := by
  ext x
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
    simp [clopenIndicator, hxs, hxt]

/-- Computes the supremum of two clopen indicators; used in the Boolean-to-
vector-sublattice transfer. -/
theorem clopenIndicator_union (s t : Set K) (hs : IsClopen s) (ht : IsClopen t) :
    clopenIndicator K (s ∪ t) (hs.union ht) =
      clopenIndicator K s hs ⊔ clopenIndicator K t ht := by
  ext x
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
    simp [clopenIndicator, hxs, hxt]

/-- Computes the indicator of a clopen complement; used to recover Boolean
complements inside a vector sublattice. -/
theorem clopenIndicator_compl (s : Set K) (hs : IsClopen s) :
    clopenIndicator K sᶜ hs.compl = 1 - clopenIndicator K s hs := by
  ext x
  by_cases hxs : x ∈ s <;> simp [clopenIndicator, hxs]

end ClopenIndicators

section BooleanStoneIndicators

variable (B : Type u) [CompleteBooleanAlgebra B]

/-- The continuous indicator associated with a Boolean element under Stone
duality; used as the Boolean generator inside the vector lattice. -/
noncomputable def booleanStoneIndicator (b : B) : C(BooleanStone B, ℝ) :=
  clopenIndicator (BooleanStone B) (booleanStoneClopen B b)
    (isClopen_booleanStoneClopen B b)

@[simp] theorem booleanStoneIndicator_apply (b : B) (x : BooleanStone B) :
    booleanStoneIndicator B b x = if x.1 b = true then 1 else 0 := by
  by_cases hxb : x.1 b = true
  · simp [booleanStoneIndicator, booleanStoneClopen, hxb]
  · simp [booleanStoneIndicator, booleanStoneClopen, hxb]

@[simp] theorem booleanStoneIndicator_bot : booleanStoneIndicator B ⊥ = 0 := by
  ext x
  simp [booleanStoneIndicator_apply]

@[simp] theorem booleanStoneIndicator_inf (a b : B) :
    booleanStoneIndicator B (a ⊓ b) =
      booleanStoneIndicator B a ⊓ booleanStoneIndicator B b := by
  ext x
  by_cases ha : x.1 a = true <;> by_cases hb : x.1 b = true <;>
    simp [booleanStoneIndicator_apply, ha, hb]

@[simp] theorem booleanStoneIndicator_sup (a b : B) :
    booleanStoneIndicator B (a ⊔ b) =
      booleanStoneIndicator B a ⊔ booleanStoneIndicator B b := by
  ext x
  by_cases ha : x.1 a = true <;> by_cases hb : x.1 b = true <;>
    simp [booleanStoneIndicator_apply, ha, hb]

@[simp] theorem booleanStoneIndicator_compl (a : B) :
    booleanStoneIndicator B aᶜ = 1 - booleanStoneIndicator B a := by
  ext x
  by_cases ha : x.1 a = true <;> simp [booleanStoneIndicator_apply, ha]

/-- Shows that arbitrary Boolean suprema correspond to closures of unions of
Stone clopens; used to transfer completeness into vector sublattices. -/
theorem booleanStoneClopen_sSup (S : Set B) :
    booleanStoneClopen B (sSup S) =
      closure (⋃ b ∈ S, booleanStoneClopen B b) := by
  apply Set.Subset.antisymm
  · intro x hxs
    by_contra hxclosure
    have hxopen : x ∈ (closure (⋃ b ∈ S, booleanStoneClopen B b))ᶜ :=
      hxclosure
    rcases booleanStone_clopen_basis B (isOpen_compl_iff.mpr isClosed_closure)
        hxopen with ⟨d, hxd, hd⟩
    have hsd : sSup S ≤ dᶜ := by
      apply sSup_le
      intro b hbS
      apply (booleanStoneClopen_subset_iff B).mp
      intro y hyb
      rw [booleanStoneClopen_compl]
      intro hyd
      have hyunion : y ∈ ⋃ c ∈ S, booleanStoneClopen B c := by
        simp only [Set.mem_iUnion]
        exact ⟨b, hbS, hyb⟩
      exact (hd hyd) (subset_closure hyunion)
    have hxcomp : x ∈ booleanStoneClopen B dᶜ :=
      (booleanStoneClopen_subset_iff B).mpr hsd hxs
    rw [booleanStoneClopen_compl] at hxcomp
    exact hxcomp hxd
  · apply closure_minimal
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨b, hbS, hxb⟩
      exact (booleanStoneClopen_subset_iff B).mpr (le_sSup hbS) hxb
    · exact (isClopen_booleanStoneClopen B (sSup S)).1

/-- Transfers Boolean order to order between indicator functions; used in
order-convergence and sublattice generation arguments. -/
theorem booleanStoneIndicator_mono {a b : B} (hab : a ≤ b) :
    booleanStoneIndicator B a ≤ booleanStoneIndicator B b := by
  intro x
  by_cases hxa : x ∈ booleanStoneClopen B a
  · have hxb : x ∈ booleanStoneClopen B b :=
      (booleanStoneClopen_subset_iff B).mpr hab hxa
    simp [booleanStoneIndicator, hxa, hxb]
  · have hnonneg : (0 : ℝ) ≤ booleanStoneIndicator B b x := by
      by_cases hxb : x ∈ booleanStoneClopen B b <;>
        simp [booleanStoneIndicator, hxb]
    simpa [booleanStoneIndicator, hxa] using hnonneg

/-- Records positivity of Boolean Stone indicators; used when constructing
monotone order-convergent families. -/
theorem booleanStoneIndicator_nonneg (a : B) :
    (0 : C(BooleanStone B, ℝ)) ≤ booleanStoneIndicator B a := by
  intro x
  by_cases hxa : x ∈ booleanStoneClopen B a <;>
    simp [booleanStoneIndicator, hxa]

/-- Boolean elements whose Stone indicators lie in a fixed vector sublattice;
used to transfer complete Boolean generation to vector-lattice generation. -/
noncomputable def booleanSubalgebraInVectorSublattice
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z) : BooleanSubalgebra B where
  carrier := {b | booleanStoneIndicator B b ∈ Z}
  supClosed' := by
    intro a ha b hb
    change booleanStoneIndicator B a ∈ Z at ha
    change booleanStoneIndicator B b ∈ Z at hb
    change booleanStoneIndicator B (a ⊔ b) ∈ Z
    rw [booleanStoneIndicator_sup]
    exact Z.sup_mem ha hb
  infClosed' := by
    intro a ha b hb
    change booleanStoneIndicator B a ∈ Z at ha
    change booleanStoneIndicator B b ∈ Z at hb
    change booleanStoneIndicator B (a ⊓ b) ∈ Z
    rw [booleanStoneIndicator_inf]
    exact Z.inf_mem ha hb
  compl_mem' := by
    intro a ha
    change booleanStoneIndicator B a ∈ Z at ha
    change booleanStoneIndicator B aᶜ ∈ Z
    rw [booleanStoneIndicator_compl]
    exact Z.sub_mem hOne ha
  bot_mem' := by
    change booleanStoneIndicator B ⊥ ∈ Z
    rw [booleanStoneIndicator_bot]
    exact Z.zero_mem

/-- Shows that Boolean elements whose indicators lie in a vector sublattice
form a complete Boolean subalgebra; used with Solovay generation for maximality. -/
theorem booleanSubalgebraInVectorSublattice_complete
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hZclosed : IsOrderClosed (Z : Set C(BooleanStone B, ℝ))) :
    IsCompleteBooleanSubalgebra
      (booleanSubalgebraInVectorSublattice B Z hOne) := by
  intro S hS
  by_cases hSne : S.Nonempty
  · classical
    let I := {F : Finset S // F.Nonempty}
    let b₀ : S := ⟨hSne.some, hSne.some_mem⟩
    let F₀ : I := ⟨{b₀}, Finset.singleton_nonempty b₀⟩
    let : Nonempty I := ⟨F₀⟩
    let : IsDirected I (· ≤ ·) := ⟨fun F G ↦
      ⟨⟨F.1 ∪ G.1, F.2.mono Finset.subset_union_left⟩,
        Finset.subset_union_left, Finset.subset_union_right⟩⟩
    let u : I → C(BooleanStone B, ℝ) := fun F ↦
      F.1.sup' F.2 (fun b ↦ booleanStoneIndicator B b.1)
    have huZ : ∀ F, u F ∈ Z := by
      intro F
      apply Finset.sup'_mem (Z : Set C(BooleanStone B, ℝ))
        (fun _ hx _ hy ↦ Z.sup_mem hx hy) F.1 F.2
      intro b hb
      exact hS b.2
    have humono : Monotone u := by
      intro F G hFG
      change F.1.sup' F.2 (fun b ↦ booleanStoneIndicator B b.1) ≤
        G.1.sup' G.2 (fun b ↦ booleanStoneIndicator B b.1)
      exact Finset.sup'_mono
        (f := fun b : S ↦ booleanStoneIndicator B b.1)
        (s₁ := F.1) (s₂ := G.1) hFG F.2
    have hlub : IsLUB (Set.range u) (booleanStoneIndicator B (sSup S)) := by
      constructor
      · rintro _ ⟨F, rfl⟩
        apply Finset.sup'_le
        intro b hb
        exact booleanStoneIndicator_mono B (le_sSup b.2)
      · intro k hk
        have hkzero : (0 : C(BooleanStone B, ℝ)) ≤ k := by
          have hF₀k : u F₀ ≤ k := hk ⟨F₀, rfl⟩
          exact (booleanStoneIndicator_nonneg B b₀.1).trans (by
            simpa [u, F₀] using hF₀k)
        intro x
        by_cases hxs : x ∈ booleanStoneClopen B (sSup S)
        · have hxclosure : x ∈ closure
              (⋃ b ∈ S, booleanStoneClopen B b) := by
            rwa [← booleanStoneClopen_sSup]
          have hclosed : IsClosed {y : BooleanStone B | (1 : ℝ) ≤ k y} :=
            isClosed_le continuous_const k.continuous
          have hunion : (⋃ b ∈ S, booleanStoneClopen B b) ⊆
              {y : BooleanStone B | (1 : ℝ) ≤ k y} := by
            intro y hy
            simp only [Set.mem_iUnion] at hy
            rcases hy with ⟨b, hbS, hyb⟩
            let bs : S := ⟨b, hbS⟩
            let Fs : I := ⟨{bs}, Finset.singleton_nonempty bs⟩
            have hbind : booleanStoneIndicator B b ≤ k := by
              have hk' := hk ⟨Fs, rfl⟩
              simpa [u, Fs, bs] using hk'
            have := hbind y
            simpa [booleanStoneIndicator, hyb] using this
          have hxone : (1 : ℝ) ≤ k x :=
            closure_minimal hunion hclosed hxclosure
          simpa [booleanStoneIndicator, hxs] using hxone
        · have hxzero := hkzero x
          simpa [booleanStoneIndicator, hxs] using hxzero
    have hconv : OrderConvergesTo u (booleanStoneIndicator B (sSup S)) :=
      orderConvergesTo_of_monotone_isLUB humono hlub
    apply hZclosed
    exact ⟨I, inferInstance, inferInstance, inferInstance, u, huZ, hconv⟩
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    subst S
    simp

end BooleanStoneIndicators

end OrderClosures

namespace OrderClosures

universe u v

section ClosedOrderSublattices

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

/-- Converts uniform convergence with a summable error bound into order
convergence; used to show order-closed sublattices are norm closed. -/
theorem continuousMap_orderConvergesTo_of_tendsto
    {ι : Type v} [Preorder ι] {f : ι → C(K, ℝ)} {x : C(K, ℝ)}
    (hfx : Filter.Tendsto f Filter.atTop (nhds x)) :
    OrderConvergesTo f x := by
  let r : ℕ → C(K, ℝ) := fun n ↦
    ContinuousMap.const K (((n : ℝ) + 1)⁻¹)
  have hranti : Antitone r := by
    intro m n hmn y
    simp only [r]
    exact inv_anti₀ (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hrnonneg : ∀ n, (0 : C(K, ℝ)) ≤ r n := by
    intro n y
    simp only [r]
    exact inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  have hscalar : Filter.Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹))
      Filter.atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hrglb : IsGLB (Set.range r) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact hrnonneg n
    · intro z hz y
      apply ge_of_tendsto' hscalar
      intro n
      simpa [r] using hz ⟨n, rfl⟩ y
  let κ := ULift.{u} ℕ
  let r' : κ → C(K, ℝ) := fun n ↦ r n.down
  have hrange : Set.range r' = Set.range r := by
    ext z
    simp only [Set.mem_range, r']
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.down, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨ULift.up n, rfl⟩
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r', ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact hranti hmn
  · intro n
    exact hrnonneg n.down
  · rw [hrange]
    exact hrglb
  intro k
  have hkpos : 0 < (((k.down : ℝ) + 1)⁻¹) := by positivity
  have hevent : ∀ᶠ n in Filter.atTop,
      f n ∈ Metric.ball x (((k.down : ℝ) + 1)⁻¹) :=
    hfx (Metric.ball_mem_nhds x hkpos)
  filter_upwards [hevent] with n hn
  intro y
  have hnorm : ‖f n - x‖ < (((k.down : ℝ) + 1)⁻¹) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hn
  calc
    |(f n - x) y| ≤ ‖f n - x‖ := by
      simpa only [Real.norm_eq_abs] using
        (ContinuousMap.norm_coe_le_norm (f n - x) y)
    _ ≤ (((k.down : ℝ) + 1)⁻¹) := hnorm.le
    _ = r' k y := by simp [r', r]

/-- Derives norm closedness of a vector sublattice from order closedness; used
to compare the closed separable sublattice with larger order-closed ones. -/
theorem isClosed_of_isOrderClosed_vectorSublattice
    (Z : VectorSublattice C(K, ℝ))
    (hZ : IsOrderClosed (Z : Set C(K, ℝ))) :
    IsClosed (Z : Set C(K, ℝ)) := by
  apply IsSeqClosed.isClosed
  intro f x hfZ hfx
  apply hZ
  let ι := ULift.{u} ℕ
  let f' : ι → C(K, ℝ) := fun n ↦ f n.down
  have hdown : Filter.Tendsto (fun n : ι ↦ n.down)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun n ↦ ?_
    filter_upwards [Filter.eventually_ge_atTop (ULift.up n)] with m hm
    exact hm
  have hf'tend : Filter.Tendsto f' Filter.atTop (nhds x) := by
    exact hfx.comp hdown
  exact ⟨ι, inferInstance, inferInstance, inferInstance, f',
    (fun n ↦ hfZ n.down), continuousMap_orderConvergesTo_of_tendsto hf'tend⟩

end ClosedOrderSublattices

section BooleanIndicatorsGenerate

variable (B : Type u) [CompleteBooleanAlgebra B]

/-- Produces a Boolean indicator separating two distinct Stone points; used
in the lattice Stone--Weierstrass argument. -/
theorem booleanStoneIndicators_separateStrongly
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hIndicator : ∀ b, booleanStoneIndicator B b ∈ Z) :
    (Z : Set C(BooleanStone B, ℝ)).SeparatesPointsStrongly := by
  intro v x y
  by_cases hxy : x = y
  · subst y
    refine ⟨v x • (1 : C(BooleanStone B, ℝ)),
      Z.toSubmodule.smul_mem (v x) hOne, ?_, ?_⟩
    all_goals simp
  · have hxyfun : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hxyfun
    cases hxb : x.1 b <;> cases hyb : y.1 b
    · exact False.elim (hb (by simp [hxb, hyb]))
    · let g := (v y - v x) • booleanStoneIndicator B b +
          v x • (1 : C(BooleanStone B, ℝ))
      refine ⟨g, Z.add_mem
        (Z.toSubmodule.smul_mem (v y - v x) (hIndicator b))
        (Z.toSubmodule.smul_mem (v x) hOne), ?_, ?_⟩
      · simp [g, booleanStoneIndicator_apply, hxb]
      · simp [g, booleanStoneIndicator_apply, hyb]
    · let g := (v x - v y) • booleanStoneIndicator B b +
          v y • (1 : C(BooleanStone B, ℝ))
      refine ⟨g, Z.add_mem
        (Z.toSubmodule.smul_mem (v x - v y) (hIndicator b))
        (Z.toSubmodule.smul_mem (v y) hOne), ?_, ?_⟩
      · simp [g, booleanStoneIndicator_apply, hxb]
      · simp [g, booleanStoneIndicator_apply, hyb]
    · exact False.elim (hb (by simp [hxb, hyb]))

/-- Shows that a closed vector sublattice containing every Boolean indicator
is all of `C(K, ℝ)`; used to prove maximality of the Solovay sublattice. -/
theorem vectorSublattice_eq_top_of_booleanStoneIndicators
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hIndicator : ∀ b, booleanStoneIndicator B b ∈ Z)
    (hZorder : IsOrderClosed (Z : Set C(BooleanStone B, ℝ))) :
    Z = ⊤ := by
  have hZclosed : IsClosed (Z : Set C(BooleanStone B, ℝ)) :=
    isClosed_of_isOrderClosed_vectorSublattice Z hZorder
  have hclosure : closure (Z : Set C(BooleanStone B, ℝ)) = ⊤ :=
    ContinuousMap.sublattice_closure_eq_top (Z : Set C(BooleanStone B, ℝ))
      ⟨0, Z.zero_mem⟩
      (fun f hf g hg ↦ Z.inf_mem hf hg)
      (fun f hf g hg ↦ Z.sup_mem hf hg)
      (booleanStoneIndicators_separateStrongly B Z hOne hIndicator)
  refine le_antisymm
    (show Z ≤ (⊤ : VectorSublattice C(BooleanStone B, ℝ)) from
      fun _ _ ↦ trivial) ?_
  intro f hf
  have hfclosure : f ∈ closure (Z : Set C(BooleanStone B, ℝ)) := by
    rw [hclosure]
    trivial
  rwa [hZclosed.closure_eq] at hfclosure

end BooleanIndicatorsGenerate

section DensityCharacter

/-- Bounds density character below by the cardinality of a one-separated
family; used for the Stone-space continuous-function density estimate. -/
theorem cardinalMk_le_densityCharacter_of_oneSeparated
    {A : Type u} {X : Type u} [PseudoMetricSpace X]
    (e : A → X) (hsep : ∀ a b, a ≠ b → (1 : ℝ) ≤ dist (e a) (e b)) :
    Cardinal.mk A ≤ densityCharacter X := by
  unfold densityCharacter
  apply le_csInf
  · exact ⟨Cardinal.mk (Set.univ : Set X), Set.univ, dense_univ, rfl⟩
  · intro c hc
    rcases hc with ⟨D, hDdense, rfl⟩
    have hthird : (0 : ℝ) < 1 / 3 := by norm_num
    choose d hdD hdclose using fun a ↦ hDdense.exists_dist_lt (e a) hthird
    let φ : A → D := fun a ↦ ⟨d a, hdD a⟩
    apply Cardinal.mk_le_of_injective (f := φ)
    intro a b hab
    by_contra hne
    have hval : d a = d b := congrArg Subtype.val hab
    have hone : (1 : ℝ) ≤ dist (e a) (e b) := hsep a b hne
    have hlt : dist (e a) (e b) < 1 := by
      calc
        dist (e a) (e b) ≤ dist (e a) (d a) + dist (d a) (e b) :=
          dist_triangle _ _ _
        _ = dist (e a) (d a) + dist (e b) (d b) := by
          rw [hval, dist_comm (d b) (e b)]
        _ < 1 / 3 + 1 / 3 := add_lt_add (hdclose a) (hdclose b)
        _ < 1 := by norm_num
    exact (not_lt_of_ge hone) hlt

/-- Shows distinct Boolean elements give indicators at distance at least one;
used to obtain a large separated family. -/
theorem one_le_dist_booleanStoneIndicator
    (B : Type u) [CompleteBooleanAlgebra B] {a b : B} (hab : a ≠ b) :
    (1 : ℝ) ≤ dist (booleanStoneIndicator B a) (booleanStoneIndicator B b) := by
  rw [dist_eq_norm]
  by_cases hle : a ≤ b
  · have hnle : ¬ b ≤ a := fun hba ↦ hab (le_antisymm hle hba)
    rcases exists_booleanStonePoint_of_not_le B hnle with ⟨x, hxb, hxa⟩
    calc
      (1 : ℝ) = ‖(booleanStoneIndicator B a - booleanStoneIndicator B b) x‖ := by
        simp [booleanStoneIndicator_apply, hxa, hxb]
      _ ≤ ‖booleanStoneIndicator B a - booleanStoneIndicator B b‖ :=
        ContinuousMap.norm_coe_le_norm _ _
  · rcases exists_booleanStonePoint_of_not_le B hle with ⟨x, hxa, hxb⟩
    calc
      (1 : ℝ) = ‖(booleanStoneIndicator B a - booleanStoneIndicator B b) x‖ := by
        simp [booleanStoneIndicator_apply, hxa, hxb]
      _ ≤ ‖booleanStoneIndicator B a - booleanStoneIndicator B b‖ :=
        ContinuousMap.norm_coe_le_norm _ _

/-- Transfers the size of a Boolean algebra to a lower bound on the density
character of its continuous-function lattice. -/
theorem cardinalMk_le_densityCharacter_booleanStoneContinuousMap
    (B : Type u) [CompleteBooleanAlgebra B] :
    Cardinal.mk B ≤ densityCharacter C(BooleanStone B, ℝ) :=
  cardinalMk_le_densityCharacter_of_oneSeparated (booleanStoneIndicator B)
    (fun _ _ ↦ one_le_dist_booleanStoneIndicator B)

end DensityCharacter

section SolovayVectorSublattice

variable (Gamma : Type u) [LinearOrder Gamma] [WellFoundedLT Gamma]
  [TopologicalSpace Gamma] [DiscreteTopology Gamma]

/-- A countable selection of Boolean Stone indicators generating the Solovay
vector sublattice used in the Gao counterexample. -/
noncomputable def solovayVectorGenerators :
    Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ) :=
  Set.range (fun p : ℕ × ℕ ↦
    booleanStoneIndicator (RegularOpen (SolovayProduct Gamma))
      (solovayB Gamma p.1 p.2)) ∪ {1}

/-- The closed vector sublattice generated by the selected Solovay indicators;
this is the separable maximal order-closed witness. -/
noncomputable def solovayVectorSublattice :
    VectorSublattice C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ) :=
  VectorSublattice.topologicalClosure
    (VectorSublattice.generated (solovayVectorGenerators Gamma))

omit [WellFoundedLT Gamma] in
/-- Records countability of the selected vector generators; used to prove
separability of their closed generated sublattice. -/
theorem solovayVectorGenerators_countable :
    (solovayVectorGenerators Gamma).Countable := by
  exact Set.countable_range _ |>.union (Set.countable_singleton _)

omit [WellFoundedLT Gamma] in
/-- Places each selected generator in the Solovay vector sublattice; used to
show that any containing sublattice contains the generated Boolean algebra. -/
theorem solovayVectorGenerator_mem
    {f : C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)}
    (hf : f ∈ solovayVectorGenerators Gamma) :
    f ∈ solovayVectorSublattice Gamma := by
  exact
    (VectorSublattice.generated
      (solovayVectorGenerators Gamma)).toSubmodule.le_topologicalClosure
        (VectorSublattice.subset_generated (solovayVectorGenerators Gamma) hf)

omit [WellFoundedLT Gamma] in
/-- Records closedness of the generated Solovay vector sublattice; this is one
of the properties required by `gao_counterexample`. -/
theorem isClosed_solovayVectorSublattice :
    IsClosed (solovayVectorSublattice Gamma :
      Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)) := by
  unfold solovayVectorSublattice VectorSublattice.topologicalClosure
  exact Submodule.isClosed_topologicalClosure _

omit [WellFoundedLT Gamma] in
/-- Derives separability from the countable generator family; this supplies
the separable sublattice in `gao_counterexample`. -/
theorem isSeparable_solovayVectorSublattice :
    TopologicalSpace.IsSeparable (solovayVectorSublattice Gamma :
      Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)) := by
  let : TopologicalSpace.SeparableSpace
      (solovayVectorSublattice Gamma).toSubmodule :=
    VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
      (solovayVectorGenerators_countable Gamma)
  exact TopologicalSpace.IsSeparable.of_subtype
    (solovayVectorSublattice Gamma :
      Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))

/-- Shows that every order-closed vector sublattice containing the Solovay
sublattice is the whole continuous-function lattice. -/
theorem solovayVectorSublattice_maximalOrderClosed
    (Z : VectorSublattice
      C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))
    (hYZ : solovayVectorSublattice Gamma ≤ Z)
    (hZorder : IsOrderClosed
      (Z : Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))) :
    Z = ⊤ := by
  let B := RegularOpen (SolovayProduct Gamma)
  have hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z := by
    apply hYZ
    apply solovayVectorGenerator_mem Gamma
    exact Or.inr (Set.mem_singleton _)
  let L : BooleanSubalgebra B :=
    booleanSubalgebraInVectorSublattice B Z hOne
  have hLcomplete : IsCompleteBooleanSubalgebra L :=
    booleanSubalgebraInVectorSublattice_complete B Z hOne hZorder
  have hLgen : ∀ m n, solovayB Gamma m n ∈ L := by
    intro m n
    change booleanStoneIndicator B (solovayB Gamma m n) ∈ Z
    apply hYZ
    apply solovayVectorGenerator_mem Gamma
    exact Or.inl ⟨(m, n), rfl⟩
  have hLtop : L = ⊤ :=
    solovay_generates_regularOpen Gamma L hLcomplete hLgen
  have hAllIndicators : ∀ b : B, booleanStoneIndicator B b ∈ Z := by
    intro b
    change b ∈ L
    rw [hLtop]
    trivial
  exact vectorSublattice_eq_top_of_booleanStoneIndicators B Z hOne
    hAllIndicators hZorder

end SolovayVectorSublattice

end OrderClosures
