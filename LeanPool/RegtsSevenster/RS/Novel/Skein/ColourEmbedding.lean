/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition
public import LeanPool.RegtsSevenster.RS.Common.ListSign

/-!
# Embeddings of mixed colours

An embedding preserves the order of odd colours and their
symplectic partners and signs. Extending a functional by zero along
such an embedding preserves its alternating evaluations on the
embedded colours and annihilates inputs using any other colour.
-/

@[expose] public section

namespace RS

/-- Compatible embeddings of the even and odd colour sets. -/
structure MixedColourEmbedding (k ℓ K L : ℕ) where
  /-- The embedding of even colours. -/
  even : Fin k ↪ Fin K
  /-- The increasing embedding of odd colours. -/
  odd : Fin (2 * ℓ) ↪o Fin (2 * L)
  /-- Symplectic partners are preserved. -/
  partner_eq : ∀ c, odd (oddPartner ℓ c) = oddPartner L (odd c)
  /-- The signs of symplectic partners are preserved. -/
  sign_eq : ∀ c, oddPartnerSign L (odd c) = oddPartnerSign ℓ c

namespace MixedColourEmbedding

/-- The embedding of the multiset and set data read by a mixed
functional. -/
def dataEmbedding {k ℓ K L : ℕ} (e : MixedColourEmbedding k ℓ K L) :
    (Multiset (Fin k) × Finset (Fin (2 * ℓ))) ↪
      (Multiset (Fin K) × Finset (Fin (2 * L))) where
  toFun p := (p.1.map e.even, p.2.map e.odd.toEmbedding)
  inj' := by
    intro a b h
    exact Prod.ext
      (Multiset.map_injective e.even.injective (congrArg Prod.fst h))
      (Finset.map_injective e.odd.toEmbedding (congrArg Prod.snd h))

/-- Preserve first-half odd colours and shift their partners to the enlarged second half. -/
def oddInclusion {ℓ L : ℕ} (h : ℓ ≤ L)
    (c : Fin (2 * ℓ)) : Fin (2 * L) :=
  if hc : c.val < ℓ then ⟨c.val, by omega⟩
  else ⟨c.val - ℓ + L, by omega⟩

private theorem oddInclusion_strictMono {ℓ L : ℕ} (h : ℓ ≤ L) :
    StrictMono (oddInclusion h) := by
  intro a b hab
  change (oddInclusion h a).val < (oddInclusion h b).val
  simp only [oddInclusion]
  split_ifs <;> dsimp only at * <;>
    have := a.isLt <;> have := b.isLt <;>
    have : a.val < b.val := hab <;> omega

/-- Embed smaller colour spaces by retaining each first-half odd
colour and moving its partner into the enlarged second half. -/
def ofLE {k ℓ K L : ℕ} (hk : k ≤ K) (hℓ : ℓ ≤ L) :
    MixedColourEmbedding k ℓ K L where
  even := Fin.castLEEmb hk
  odd := OrderEmbedding.ofStrictMono (oddInclusion hℓ)
    (by exact oddInclusion_strictMono hℓ)
  partner_eq := by
    intro c
    change oddInclusion hℓ (oddPartner ℓ c) =
      oddPartner L (oddInclusion hℓ c)
    apply Fin.ext
    have := c.isLt
    by_cases hc : c.val < ℓ
    · have hcL : c.val < L := by omega
      have hnot : ¬ c.val + ℓ < ℓ := by omega
      simp [oddInclusion, oddPartner, hc, hcL, hnot]
    · have hsub : c.val - ℓ < ℓ := by omega
      have hnot : ¬ c.val - ℓ + L < L := by omega
      simp [oddInclusion, oddPartner, hc, hsub, hnot]
  sign_eq := by
    intro c
    change oddPartnerSign L (oddInclusion hℓ c) = oddPartnerSign ℓ c
    have := c.isLt
    by_cases hc : c.val < ℓ
    · have hcL : c.val < L := by omega
      simp [oddInclusion, oddPartnerSign, hc, hcL]
    · have hnot : ¬ c.val - ℓ + L < L := by omega
      simp [oddInclusion, oddPartnerSign, hc, hnot]

end MixedColourEmbedding

namespace MixedFunctional

/-- Extension by zero to the embedded colour data. -/
noncomputable def extendColours {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (e : MixedColourEmbedding k ℓ K L) :
    MixedFunctional K L := fun μ F =>
  Function.extend e.dataEmbedding (fun p => h p.1 p.2) (fun _ => 0) (μ, F)

/-- The extended functional agrees with the original on embedded
multisets and sets. -/
theorem extendColours_map {k ℓ K L : ℕ} (h : MixedFunctional k ℓ)
    (e : MixedColourEmbedding k ℓ K L)
    (μ : Multiset (Fin k)) (F : Finset (Fin (2 * ℓ))) :
    h.extendColours e (μ.map e.even) (F.map e.odd.toEmbedding) = h μ F :=
  e.dataEmbedding.injective.extend_apply _ _ (μ, F)

/-- An even colour outside the embedding makes the extended
functional vanish. -/
theorem extendColours_eq_zero_of_even {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (e : MixedColourEmbedding k ℓ K L)
    (μ : Multiset (Fin K)) (F : Finset (Fin (2 * L)))
    (c : Fin K) (hc : c ∈ μ) (hout : c ∉ Set.range e.even) :
    h.extendColours e μ F = 0 := by
  classical
  apply Function.extend_apply'
  rintro ⟨p, hp⟩
  have hμ : p.1.map e.even = μ := congrArg Prod.fst hp
  rw [← hμ] at hc
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hc
  exact hout ⟨a, ha⟩

/-- An odd colour outside the embedding makes the extended
functional vanish. -/
theorem extendColours_eq_zero_of_odd {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (e : MixedColourEmbedding k ℓ K L)
    (μ : Multiset (Fin K)) (F : Finset (Fin (2 * L)))
    (c : Fin (2 * L)) (hc : c ∈ F) (hout : c ∉ Set.range e.odd) :
    h.extendColours e μ F = 0 := by
  classical
  apply Function.extend_apply'
  rintro ⟨p, hp⟩
  have hF : p.2.map e.odd.toEmbedding = F := congrArg Prod.snd hp
  rw [← hF] at hc
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hc
  exact hout ⟨a, ha⟩

/-- Alternating evaluation commutes with the colour embedding. -/
theorem evalOdd_extendColours_map {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (e : MixedColourEmbedding k ℓ K L)
    (μ : Multiset (Fin k)) (w : List (Fin (2 * ℓ))) :
    (h.extendColours e).evalOdd (μ.map e.even) (w.map e.odd) =
      h.evalOdd μ w := by
  classical
  have hset : (w.map e.odd).toFinset = w.toFinset.map e.odd.toEmbedding := by
    ext c
    simp
  simp only [evalOdd, List.nodup_map_iff e.odd.injective,
    sortSign_map_orderEmbedding, hset, extendColours_map]

/-- Alternating evaluation vanishes if an even input colour is
outside the embedding. -/
theorem evalOdd_extendColours_eq_zero_of_even {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (e : MixedColourEmbedding k ℓ K L)
    (μ : Multiset (Fin K)) (w : List (Fin (2 * L)))
    (c : Fin K) (hc : c ∈ μ) (hout : c ∉ Set.range e.even) :
    (h.extendColours e).evalOdd μ w = 0 := by
  classical
  simp only [evalOdd, extendColours_eq_zero_of_even h e μ _ c hc hout,
    mul_zero, ite_self]

/-- Alternating evaluation vanishes if an odd input colour is
outside the embedding. -/
theorem evalOdd_extendColours_eq_zero_of_odd {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (e : MixedColourEmbedding k ℓ K L)
    (μ : Multiset (Fin K)) (w : List (Fin (2 * L)))
    (c : Fin (2 * L)) (hc : c ∈ w) (hout : c ∉ Set.range e.odd) :
    (h.extendColours e).evalOdd μ w = 0 := by
  classical
  simp only [evalOdd, extendColours_eq_zero_of_odd h e μ _ c
    (List.mem_toFinset.mpr hc) hout, mul_zero, ite_self]

end MixedFunctional

end RS
