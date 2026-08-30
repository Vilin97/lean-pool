/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import LeanPool.UlmsTheorem.PGroups.Morphisms
import LeanPool.UlmsTheorem.PGroups.Socle

/-!
# Pure subgroups and height-preserving partial maps

This file contains the basic hard-direction infrastructure for Ulm's theorem:
ordinal height, p-order, purity, and height-preserving maps on subgroups.
-/

namespace UlmsTheorem

open Ordinal

universe u

variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-- The ordinal Ulm height of an element. -/
noncomputable def ulmHeight (x : G) : WithTop Ordinal.{0} :=
  ⨆ (α : Ordinal.{0}) (_ : x ∈ ulmSubgroup p α (G := G)), (α : WithTop Ordinal.{0})

/-- `x` is proper with respect to `S` when its height is maximal in the coset `x + S`. -/
def IsProper (S : AddSubgroup G) (x : G) : Prop :=
  ∀ s : S, ulmHeight p x ≥ ulmHeight p (x + s)

/-- Filtration-membership domination implies domination of ordinal Ulm heights. -/
lemma ulmHeight_le_of_mem_imp (x y : G)
    (h : ∀ α : Ordinal.{0},
      x ∈ ulmSubgroup p α (G := G) → y ∈ ulmSubgroup p α (G := G)) :
    ulmHeight p x ≤ ulmHeight p y :=
  iSup₂_le fun α hx ↦ le_iSup_of_le α (le_iSup_of_le (h α hx) le_rfl)

/-- Membership in `G_α` gives the corresponding lower bound on Ulm height. -/
lemma coe_le_ulmHeight_of_mem (x : G) (α : Ordinal.{0})
    (hx : x ∈ ulmSubgroup p α (G := G)) :
    (α : WithTop Ordinal.{0}) ≤ ulmHeight p x :=
  le_iSup_of_le α (le_iSup_of_le hx le_rfl)

/-- Failure of membership at the successor of `α` bounds the Ulm height by `α`.

Unlike the exact-height lemma below, this does not assume membership in `G_α`.
It is useful when properness rules out a higher representative in a coset. -/
lemma ulmHeight_le_of_not_mem_succ (x : G) (α : Ordinal.{0})
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    ulmHeight p x ≤ (α : WithTop Ordinal.{0}) :=
  iSup₂_le fun β hxβ ↦ WithTop.coe_le_coe.mpr (by
    by_contra hβα
    exact hxs (ulmSubgroup_antitone p (Order.succ_le_iff.mpr (lt_of_not_ge hβα)) hxβ))

/-- **The converse of `coe_le_ulmHeight_of_mem`.**  A lower bound on the Ulm
height is membership in the filtration: if `γ ≤ h(x)` then `x ∈ G_γ`.

The supremum defining `ulmHeight` is therefore attained whenever it is bounded by
an ordinal, so `h(x) ≥ γ` and `x ∈ G_γ` are interchangeable.  This is the bridge
that lets a height condition stated with `ulmHeight` be used as a filtration
hypothesis.

The three cases are genuinely different: at `0` the filtration is everything, at a
successor the previous lemma bounds the height strictly below, and at a limit the
inductive hypothesis supplies membership at every smaller level, which is exactly
the intersection defining `G_γ`. -/
theorem mem_ulmSubgroup_of_le_ulmHeight (x : G) (γ : Ordinal.{0})
    (h : (γ : WithTop Ordinal.{0}) ≤ ulmHeight p x) :
    x ∈ ulmSubgroup p γ (G := G) := by
  induction γ using Ordinal.limitRecOn with
  | zero => simp
  | add_one δ _ih =>
      by_contra hx
      have hle : ulmHeight p x ≤ (δ : WithTop Ordinal.{0}) :=
        ulmHeight_le_of_not_mem_succ p x δ hx
      have : ((Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0})
          ≤ (δ : WithTop Ordinal.{0}) := le_trans h hle
      exact absurd (WithTop.coe_le_coe.mp this) (not_le_of_gt (Order.lt_succ δ))
  | limit δ hlim ih =>
      rw [mem_ulmSubgroup_limit_iff (p := p) (G := G) hlim]
      intro β hβ
      refine ih β hβ (le_trans ?_ h)
      exact WithTop.coe_le_coe.mpr (le_of_lt hβ)

/-- Membership in the filtration and a lower bound on the Ulm height are the same
statement. -/
theorem mem_ulmSubgroup_iff_le_ulmHeight (x : G) (γ : Ordinal.{0}) :
    x ∈ ulmSubgroup p γ (G := G) ↔ (γ : WithTop Ordinal.{0}) ≤ ulmHeight p x :=
  ⟨coe_le_ulmHeight_of_mem p x γ, mem_ulmSubgroup_of_le_ulmHeight p x γ⟩

/-- An element in `G_α` but not `G_(α+1)` has Ulm height exactly `α`. -/
lemma ulmHeight_eq_of_mem_not_mem_succ (x : G) (α : Ordinal.{0})
    (hx : x ∈ ulmSubgroup p α (G := G))
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    ulmHeight p x = (α : WithTop Ordinal.{0}) :=
  le_antisymm (ulmHeight_le_of_not_mem_succ p x α hxs) (coe_le_ulmHeight_of_mem p x α hx)

/-- For an element of exact height `α`, properness over `S` says exactly that no
`S`-translate reaches `G_(α+1)`.

Both Kaplansky target constructions establish properness by ruling out a higher
translate and consume it the same way, so this is the form they share. -/
lemma isProper_iff_forall_not_mem_succ (S : AddSubgroup G) {x : G}
    {α : Ordinal.{0}} (hx : x ∈ ulmSubgroup p α (G := G))
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    IsProper p S x ↔ ∀ c : S, x + (c : G) ∉ ulmSubgroup p (Order.succ α) (G := G) := by
  have hheight := ulmHeight_eq_of_mem_not_mem_succ p x α hx hxs
  constructor
  · exact fun hproper c hc ↦ absurd
      (((coe_le_ulmHeight_of_mem p _ _ hc).trans (hproper c)).trans_eq hheight)
      (not_le_of_gt (WithTop.coe_lt_coe.mpr (Order.lt_succ α)))
  · intro h c
    change ulmHeight p (x + (c : G)) ≤ ulmHeight p x
    rw [hheight]
    exact ulmHeight_le_of_not_mem_succ p (x + (c : G)) α (h c)

/-- In a reduced `p`-group, every nonzero element has an attained ordinal
Ulm height.

Reducedness supplies a stage missing the element.  The least such stage
cannot be zero or a limit stage, so it is a successor `α+1`; minimality then
puts the element in `G_α` but not in `G_(α+1)`. -/
lemma exists_ulmHeight_eq_of_ne_zero
    (hG : IsReducedPGroup p G) {x : G} (hx0 : x ≠ 0) :
    ∃ α : Ordinal.{0},
      x ∈ ulmSubgroup p α (G := G) ∧
      x ∉ ulmSubgroup p (Order.succ α) (G := G) := by
  obtain ⟨γ, hγ⟩ := hG.reduced
  have hxγ : x ∉ ulmSubgroup p γ (G := G) := by
    rw [hγ]
    simpa using hx0
  obtain ⟨δ, hδmin⟩ :=
    exists_minimal_of_wellFoundedLT
      (fun β : Ordinal.{0} ↦ x ∉ ulmSubgroup p β (G := G)) ⟨γ, hxγ⟩
  rcases Ordinal.zero_or_succ_or_isSuccLimit δ with hδ0 | ⟨α, rfl⟩ | hδlim
  · subst δ
    exact False.elim (hδmin.1 (by simp))
  · refine ⟨α, ?_, hδmin.1⟩
    by_contra hxα
    exact hδmin.not_prop_of_lt (Order.lt_succ α) hxα
  · have hnotall :
        ¬ ∀ β < δ, x ∈ ulmSubgroup p β (G := G) := by
      simpa [mem_ulmSubgroup_limit_iff p hδlim x] using hδmin.1
    push Not at hnotall
    obtain ⟨β, hβδ, hxβ⟩ := hnotall
    exact False.elim (hδmin.not_prop_of_lt hβδ hxβ)

/-- Height-preserving map between full groups. -/
def IsHeightPreserving (φ : G →+ H) : Prop :=
  ∀ (x : G) (α : Ordinal.{0}),
    x ∈ ulmSubgroup p α (G := G) ↔ φ x ∈ ulmSubgroup p α (G := H)

/-- Height-preserving map between subgroups `A ≤ G` and `B ≤ H`. -/
def IsHeightPresOn {A : AddSubgroup G} {B : AddSubgroup H} (φ : A →+ B) : Prop :=
  ∀ (a : A) (α : Ordinal.{0}),
    (a : G) ∈ ulmSubgroup p α (G := G) ↔ (φ a : H) ∈ ulmSubgroup p α (G := H)

/-- The `p`-order of an element: the least `n` such that `p^n • x = 0`,
or `⊤` if no such `n` exists. -/
noncomputable def pOrder (x : G) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : p ^ n • x = 0), (n : ℕ∞)

@[simp] lemma pOrder_zero : pOrder p (0 : G) = 0 :=
  le_antisymm (iInf_le_of_le 0 <| iInf_le_of_le (by simp) le_rfl) bot_le

lemma smul_eq_zero_iff_le_pOrder (x : G) (n : ℕ) :
    p ^ n • x = 0 ↔ pOrder p x ≤ n := by
  constructor
  · intro hx
    exact iInf_le_of_le n <| iInf_le_of_le hx le_rfl
  · intro h
    by_contra hx
    have hlt : (n : ℕ∞) < pOrder p x := by
      rw [pOrder]
      refine (lt_iInf_iff).2 ?_
      refine ⟨(n + 1 : ℕ∞), by
        simpa using (ENat.lt_natCast_add_one_iff (m := (n : ℕ∞)) (n := n)).2 le_rfl, ?_⟩
      intro m
      refine le_iInf ?_
      intro hm
      refine WithTop.coe_le_coe.mpr <| Nat.succ_le_of_lt <| Nat.lt_of_not_ge ?_
      intro hmn
      apply hx
      rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
      rw [pow_add, mul_smul]
      calc
        p ^ m • p ^ k • x = p ^ k • (p ^ m • x) := by
          rw [smul_smul, smul_smul, Nat.mul_comm]
        _ = 0 := by simp [hm]
    exact not_lt_of_ge h hlt

/-- Killing `p • x` at level `n` kills `x` at level `n + 1`. -/
lemma pOrder_le_succ_of_smul_p_le {x : G} {n : ℕ} (h : pOrder p (p • x) ≤ n) :
    pOrder p x ≤ n + 1 :=
  (smul_eq_zero_iff_le_pOrder (p := p) (x := x) (n + 1)).1 <| by
    simpa [pow_succ, mul_smul] using
      (smul_eq_zero_iff_le_pOrder (p := p) (x := p • x) n).2 h

/-- The converse: killing `x` at level `n + 1` kills `p • x` at level `n`. -/
lemma smul_p_pOrder_le_of_le_succ {x : G} {n : ℕ} (h : pOrder p x ≤ n + 1) :
    pOrder p (p • x) ≤ n :=
  (smul_eq_zero_iff_le_pOrder (p := p) (x := p • x) n).1 <| by
    simpa [pow_succ, mul_smul] using
      (smul_eq_zero_iff_le_pOrder (p := p) (x := x) (n + 1)).2 h

lemma pOrder_smul_p (x : G) (hx : 0 < pOrder p x) :
    pOrder p (p • x) = pOrder p x - 1 := by
  cases hox : pOrder p x using ENat.recTopCoe with
  | top =>
      simpa [hox] using show pOrder p (p • x) = ⊤ from by
        by_contra hy
        rcases WithTop.ne_top_iff_exists.mp hy with ⟨n, hn⟩
        have hxle : pOrder p x ≤ n + 1 :=
          pOrder_le_succ_of_smul_p_le p (by rw [← hn]; exact le_rfl)
        rw [hox] at hxle
        exact (WithTop.not_top_le_coe (n + 1) hxle).elim
  | coe n =>
      cases n with
      | zero =>
          simp [hox] at hx
      | succ n =>
          have hupper : pOrder p (p • x) ≤ n :=
            smul_p_pOrder_le_of_le_succ p (by simp [hox])
          cases n with
          | zero =>
              exact le_antisymm hupper bot_le
          | succ m =>
              apply le_antisymm hupper
              by_contra hlow
              have hlt : pOrder p (p • x) < m + 1 := lt_of_not_ge hlow
              have hle : pOrder p (p • x) ≤ m := by
                simpa [Nat.succ_eq_add_one] using
                  (ENat.lt_natCast_add_one_iff (m := pOrder p (p • x)) (n := m)).1 hlt
              have hxle : pOrder p x ≤ m + 1 := pOrder_le_succ_of_smul_p_le p hle
              rw [hox] at hxle
              exact (not_le_of_gt <| by
                simpa using
                  (ENat.lt_natCast_add_one_iff (m := (m : ℕ∞)) (n := m)).2 le_rfl) hxle |>.elim

lemma pOrder_pos_of_ne_zero (x : G) (hx : x ≠ 0) :
    0 < pOrder p x := by
  by_contra h
  have hle : pOrder p x ≤ 0 := le_of_not_gt h
  have hx0 : p ^ 0 • x = 0 :=
    (smul_eq_zero_iff_le_pOrder (p := p) (x := x) 0).2 hle
  exact hx (by simpa using hx0)

/-- A subgroup is `p`-pure if divisibility by powers of `p` seen in the ambient
group is already witnessed internally. -/
def IsPure (A : AddSubgroup G) : Prop :=
  ∀ (n : ℕ) (x : A), (x : G) ∈ pPow p n (G := G) → x ∈ pPow p n (G := A)

/-- An isotype subgroup is one whose induced Ulm filtration agrees with the
ambient filtration on every element. This is stronger than purity, and it is
the right hypothesis for ambient/intrinsic height equality. -/
def IsIsotype (A : AddSubgroup G) : Prop :=
  ∀ (x : A) (α : Ordinal.{0}),
    (x : G) ∈ ulmSubgroup p α (G := G) ↔ x ∈ ulmSubgroup p α (G := A)

lemma IsPure_bot : IsPure p (⊥ : AddSubgroup G) :=
  fun _ _ _ ↦ ⟨0, Subsingleton.elim _ _⟩

lemma IsPure_top : IsPure p (⊤ : AddSubgroup G) := fun _ _ hx ↦ by
  obtain ⟨y, hy⟩ := hx
  exact ⟨⟨y, by simp⟩, Subtype.ext hy⟩

lemma IsIsotype.isPure {A : AddSubgroup G} (hA : IsIsotype p A) :
    IsPure p A := by
  intro n x hx
  rw [← ulmSubgroup_nat (p := p) (G := G) n] at hx
  rw [← ulmSubgroup_nat (p := p) (G := A) n]
  exact (hA x n).mp hx

lemma ulmHeight_subgroup_le_ambient {A : AddSubgroup G} (x : A) :
    ulmHeight p x (G := A) ≤ ulmHeight p (x : G) :=
  iSup₂_le fun α hx ↦ le_iSup_of_le α <| le_iSup_of_le
    (map_ulmSubgroup_le (p := p) (φ := A.subtype) α ⟨x, hx, rfl⟩) le_rfl

lemma IsIsotype.ulmHeight_eq {A : AddSubgroup G} (hA : IsIsotype p A) (x : A) :
    ulmHeight p (x : G) = ulmHeight p x (G := A) :=
  le_antisymm
    (iSup₂_le fun α hx ↦ le_iSup_of_le α <| le_iSup_of_le ((hA x α).mp hx) le_rfl)
    (iSup₂_le fun α hx ↦ le_iSup_of_le α <| le_iSup_of_le ((hA x α).mpr hx) le_rfl)

lemma IsHeightPreserving.injective (hred : IsReducedPGroup p G)
    {φ : G →+ H} (hφ : IsHeightPreserving p φ) :
    Function.Injective φ := by
  intro x y hxy
  rcases hred.reduced with ⟨α, hα⟩
  have hmem : x - y ∈ ulmSubgroup p α (G := G) :=
    (hφ (x - y) α).mpr (by simp [hxy])
  rw [hα] at hmem
  exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp hmem)

lemma IsHeightPresOn.injective (hred : IsReducedPGroup p G)
    {A : AddSubgroup G} {B : AddSubgroup H} {φ : A →+ B} (hφ : IsHeightPresOn p φ) :
    Function.Injective φ := by
  intro x y hxy
  apply Subtype.ext
  rcases hred.reduced with ⟨α, hα⟩
  have hmem : (((x - y : A) : A) : G) ∈ ulmSubgroup p α (G := G) :=
    (hφ (x - y) α).mpr (by simp [hxy])
  rw [hα] at hmem
  exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp hmem)

/-- If `a` is in a subgroup but `b` is not, their sum is not in the subgroup.
Useful for the ultrametric argument in the extension theorem. -/
lemma not_mem_of_mem_of_not_mem_add {S : AddSubgroup G} {a b : G}
    (ha : a ∈ S) (hb : b ∉ S) : a + b ∉ S :=
  fun hab ↦ hb (by simpa using S.sub_mem hab ha)

/-- **Multiplication by an integer prime to `p` preserves the filtration.**

In a primary group every element has `p`-power order, so an `n` prime to `p` is
invertible on it: Bezout gives `a·n + b·p^k = 1` with `p^k • u = 0`, whence
`u = a • (n • u)`.  Membership of `n • u` and of `u` therefore agree at every
level.

This generalizes `mem_ulmSubgroup_zsmul_iff_of_pSocle` off the socle, which is
what the one-line extension step needs: the challenge element is a socle element,
but the elements `b + r·x` it must be checked against are not. -/
lemma mem_ulmSubgroup_zsmul_iff [Fact p.Prime] (hprim : IsPrimaryPGroup p G)
    {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (u : G) (β : Ordinal.{0}) :
    n • u ∈ ulmSubgroup p β (G := G) ↔ u ∈ ulmSubgroup p β (G := G) := by
  constructor
  · intro hmem
    obtain ⟨k, hk⟩ := hprim u
    -- `n` is prime to `p^k`, so Bezout inverts it on `u`
    have hcop : IsCoprime (n : ℤ) ((p : ℤ) ^ k) := by
      exact (Int.isCoprime_iff_gcd_eq_one.mpr (by
        have : Int.gcd n (p : ℤ) = 1 := by
          change n.natAbs.gcd p = 1
          rw [Nat.gcd_comm]
          exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2
            (fun h ↦ hn (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 h)))
        exact this)).pow_right
    obtain ⟨a, b, hab⟩ := hcop
    have hu : u = a • (n • u) := by
      calc u = (1 : ℤ) • u := (one_zsmul u).symm
        _ = (a * n + b * (p : ℤ) ^ k) • u := by rw [hab]
        _ = a • (n • u) + b • (((p : ℤ) ^ k) • u) := by
            rw [add_zsmul, mul_zsmul, mul_zsmul]
        _ = a • (n • u) + b • (0 : G) := by
            congr 2
            have : (((p : ℤ) ^ k) • u) = (p ^ k : ℕ) • u := by
              rw [← Int.natCast_pow, natCast_zsmul]
            rw [this, hk]
        _ = a • (n • u) := by simp
    rw [hu]
    exact (ulmSubgroup p β).zsmul_mem hmem a
  · intro hmem
    exact (ulmSubgroup p β).zsmul_mem hmem n

/-- Multiplication by an integer prime to `p` preserves Ulm height. -/
lemma ulmHeight_zsmul [Fact p.Prime] (hprim : IsPrimaryPGroup p G)
    {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (u : G) :
    ulmHeight p (n • u) = ulmHeight p u := by
  apply le_antisymm
  · exact ulmHeight_le_of_mem_imp p _ _
      (fun γ h ↦ (mem_ulmSubgroup_zsmul_iff p hprim hn u γ).mp h)
  · exact ulmHeight_le_of_mem_imp p _ _
      (fun γ h ↦ (mem_ulmSubgroup_zsmul_iff p hprim hn u γ).mpr h)

/-- For an element `g` of the `p`-socle (`p • g = 0`), membership of `n • g` in a
Ulm subgroup is equivalent to membership of `g`, provided `p ∤ n`.
Proof: Bezout gives `a * n + b * p = 1`, so `g = a • (n • g) + b • (p • g) = a • (n • g)`. -/
lemma mem_ulmSubgroup_zsmul_iff_of_pSocle [Fact p.Prime] {g : G}
    (hpg : p • g = 0) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (β : Ordinal) :
    n • g ∈ ulmSubgroup p β (G := G) ↔ g ∈ ulmSubgroup p β (G := G) := by
  constructor
  · intro hmem
    -- Get Bezout coefficients via Int.gcd_eq_gcd_ab
    have hgcd : Int.gcd n (p : ℤ) = 1 := by
      change n.natAbs.gcd p = 1
      rw [Nat.gcd_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2
        (fun h ↦ hn (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 h)))
    -- Bezout: n * gcdA + p * gcdB = 1
    have hbez := Int.gcd_eq_gcd_ab n (p : ℤ)
    rw [show (Int.gcd n (p : ℤ) : ℤ) = 1 from by exact_mod_cast hgcd] at hbez
    -- hbez : 1 = n * Int.gcdA n ↑p + ↑p * Int.gcdB n ↑p
    have hg_eq : g = Int.gcdA n ↑p • (n • g) := by
      calc g = (1 : ℤ) • g := (one_zsmul g).symm
        _ = (n * Int.gcdA n ↑p + ↑p * Int.gcdB n ↑p) • g := by rw [← hbez]
        _ = Int.gcdA n ↑p • (n • g) + Int.gcdB n ↑p • ((↑p : ℤ) • g) := by
            rw [add_zsmul, mul_comm n, mul_zsmul, mul_comm (↑p : ℤ), mul_zsmul]
        _ = Int.gcdA n ↑p • (n • g) + Int.gcdB n ↑p • (0 : G) := by
            -- (↑p : ℤ) • g = p • g = 0; congr 2 peels off gcdB • (–)
            congr 2; exact_mod_cast hpg
        _ = Int.gcdA n ↑p • (n • g) := by simp
    rw [hg_eq]
    exact (ulmSubgroup p β (G := G)).zsmul_mem hmem (Int.gcdA n ↑p)
  · exact fun hmem ↦ (ulmSubgroup p β (G := G)).zsmul_mem hmem n

lemma IsPure.map_of_heightPres {A : AddSubgroup G} (hA : IsPure p A)
    (φ : G →+ H) (hφ : IsHeightPreserving p φ) :
    IsPure p (A.map φ) := by
  intro n x hx
  rcases x.property with ⟨a, haA, hax⟩
  have hx' : φ a ∈ pPow p n (G := H) := by
    simpa [hax] using hx
  rw [← ulmSubgroup_nat (p := p) n] at hx'
  have ha_pow : a ∈ pPow p n (G := G) := by
    rw [← ulmSubgroup_nat (p := p) n]
    exact (hφ a n).mpr hx'
  rcases hA n ⟨a, haA⟩ ha_pow with ⟨b, hb⟩
  refine ⟨⟨φ b, ⟨b, b.property, rfl⟩⟩, ?_⟩
  ext
  have hb' : p ^ n • (b : G) = a := congrArg (fun z : A ↦ (z : G)) hb
  exact (by
    simpa [map_nsmul] using (congrArg φ hb').trans hax)

lemma IsPure.range_of_heightPresOn {A : AddSubgroup G} {B : AddSubgroup H}
    (hA : IsPure p A) (φ : A →+ B) (hφ : IsHeightPresOn p φ) :
    IsPure p ((⊤ : AddSubgroup A).map (B.subtype.comp φ)) := by
  intro n x hx
  rcases x.property with ⟨a, _haA, hax⟩
  have hx' : ((B.subtype.comp φ) a : H) ∈ pPow p n (G := H) := by
    simpa [hax] using hx
  rw [← ulmSubgroup_nat (p := p) (G := H) n] at hx'
  have ha_pow : (a : G) ∈ pPow p n (G := G) := by
    rw [← ulmSubgroup_nat (p := p) (G := G) n]
    exact (hφ a n).mpr hx'
  rcases hA n a ha_pow with ⟨b, hb⟩
  refine ⟨⟨(B.subtype.comp φ) b, ⟨b, by simp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  calc
    p ^ n • ((B.subtype.comp φ) b : H) = (B.subtype.comp φ) a := by
      simpa [AddMonoidHom.comp_apply, map_nsmul] using congrArg (B.subtype.comp φ) hb
    _ = (x : H) := by simpa using hax

end UlmsTheorem
