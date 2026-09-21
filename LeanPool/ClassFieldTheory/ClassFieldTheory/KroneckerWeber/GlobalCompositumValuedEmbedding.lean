/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.RamificationTheory.HilbertRamification.PadicLocalizationCanonicalValuation
/-!
# A valued global embedding of the auxiliary compositum

The left factor is embedded through its chosen localization.
Consequently the pullback of the canonical absolute value on the common
local cyclotomic target is exactly the chosen `p`-adic place.  The corrected
normal-compositum embedding preserves this exact left restriction.
-/

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory
open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The value-preserving property for a global left-factor embedding.  The
finite-dimensional structure of the concrete cyclotomic target remains
internal to this named proposition. -/
noncomputable def kroneckerWeberGlobalLeftEmbeddingPreservesPadicPlace
    (p : Nat.Primes) [Fact p.1.Prime]
    (i : L →ₐ[ℚ]
      CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p)
        ℚ_[p.1]) : Prop := by
  let N := kroneckerWeberLocalCompositumOrder (L := L) p
  have hN : 0 < N := kroneckerWeberLocalCompositumOrder_pos (L := L) p
  letI : NeZero N := ⟨hN.ne'⟩
  let T := CyclotomicField N ℚ_[p.1]
  letI : FiniteDimensional ℚ_[p.1] T :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ_[p.1] T
  let w := kroneckerWeberPadicExtension (L := L) p.1
  exact ∀ x : L,
    padicFiniteExtensionAbsoluteValue p.1 T (i x) = w.1 x

/-- A global left-factor embedding which preserves the particular `p`-adic
place used to choose the local exponent. -/
noncomputable def kroneckerWeberGlobalValuedLeftEmbeddingProperty
    (p : Nat.Primes) : Prop := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let T :=
    CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p) ℚ_[p.1]
  exact ∃ i : L →ₐ[ℚ] T,
    kroneckerWeberGlobalLeftEmbeddingPreservesPadicPlace (L := L) p i

/-- The global field embeds into the common local cyclotomic target while
preserving the chosen `p`-adic place. -/
theorem kroneckerWeberGlobalValuedLeftEmbedding
    (p : Nat.Primes) :
    kroneckerWeberGlobalValuedLeftEmbeddingProperty (L := L) p := by
  let : Fact p.1.Prime := ⟨p.2⟩
  let N := kroneckerWeberLocalCompositumOrder (L := L) p
  have hN : 0 < N := kroneckerWeberLocalCompositumOrder_pos (L := L) p
  let : NeZero N := ⟨hN.ne'⟩
  let T := CyclotomicField N ℚ_[p.1]
  let : FiniteDimensional ℚ_[p.1] T :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ_[p.1] T
  let w := kroneckerWeberPadicExtension (L := L) p.1
  have hi := kroneckerWeberGlobalLeftRingEmbedding (L := L) p
  change ∃ r : L →+* T, ∀ x : L,
    padicFiniteExtensionAbsoluteValue p.1 T (r x) = w.1 x at hi
  obtain ⟨r, hr⟩ := hi
  let i : L →ₐ[ℚ] T :=
    { __ := r
      commutes' := fun q ↦ map_ratCast r q }
  refine ⟨i, ?_⟩
  change ∀ x : L,
    padicFiniteExtensionAbsoluteValue p.1 T (i x) = w.1 x
  exact hr

/-- A common-target compositum embedding whose restriction to `L` induces
the chosen `p`-adic absolute value. -/
structure KroneckerWeberGlobalValuedCompositumEmbeddingData
    (p : Nat.Primes) [Fact p.1.Prime] where
  /-- The value-preserving embedding of the original global field. -/
  leftEmbedding :
    L →ₐ[ℚ]
      CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p)
        ℚ_[p.1]
  /-- The embedding of the global compositum into the common local target. -/
  embedding :
    kroneckerWeberCompositumField L →ₐ[ℚ]
      CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p)
        ℚ_[p.1]
  /-- The compositum embedding restricts to the chosen left-factor embedding. -/
  embedding_left : ∀ x : L,
    embedding (kroneckerWeberCompositumEmbeddingLeft (L := L) x) =
      leftEmbedding x
  /-- The left-factor embedding pulls back the canonical target absolute value
  to the chosen `p`-adic place. -/
  leftEmbedding_absoluteValue :
    kroneckerWeberGlobalLeftEmbeddingPreservesPadicPlace
      (L := L) p leftEmbedding

/-- The synchronized valued embeddings of the original field and its global
cyclotomic compositum into the common local target. -/
noncomputable def kroneckerWeberGlobalValuedCompositumEmbeddingData
    (p : Nat.Primes)
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    KroneckerWeberGlobalValuedCompositumEmbeddingData (L := L) p := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let hi := kroneckerWeberGlobalValuedLeftEmbedding (L := L) p
  let i := Classical.choose hi
  let hiAbs := Classical.choose_spec hi
  let j :
      CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ →ₐ[ℚ]
        CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p)
          ℚ_[p.1] :=
    Classical.choice (kroneckerWeberGlobalRightEmbedding (L := L) p hp)
  let hex :=
    exists_finiteGaloisCompositumEmbeddingOfEmbeddings_left_eq
      ℚ L (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ)
      (CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p)
        ℚ_[p.1]) i j
  let g := Classical.choose hex
  let hg := Classical.choose_spec hex
  exact ⟨i, g, hg, hiAbs⟩

/-- The synchronized `p`-adic place on the global compositum, pulled back
from the canonical absolute value on the common local cyclotomic target. -/
noncomputable def kroneckerWeberGlobalCompositumCyclotomicPadicExtension
    (p : Nat.Primes) [Fact p.1.Prime]
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    AbsoluteValueExtension (Rat.AbsoluteValue.padic p.1)
      (kroneckerWeberCompositumField L) := by
  let N := kroneckerWeberLocalCompositumOrder (L := L) p
  have hN : 0 < N := kroneckerWeberLocalCompositumOrder_pos (L := L) p
  letI : NeZero N := ⟨hN.ne'⟩
  let T := CyclotomicField N ℚ_[p.1]
  letI : FiniteDimensional ℚ_[p.1] T :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ_[p.1] T
  let W :=
    kroneckerWeberGlobalValuedCompositumEmbeddingData (L := L) p hp
  let aT := padicFiniteExtensionAbsoluteValue p.1 T
  let aM : AbsoluteValue (kroneckerWeberCompositumField L) ℝ :=
    aT.comp W.embedding.injective
  refine ⟨aM, ?_⟩
  intro q
  change aT (W.embedding (algebraMap ℚ (kroneckerWeberCompositumField L) q)) =
    Rat.AbsoluteValue.padic p.1 q
  rw [W.embedding.commutes]
  change aT (q : T) = Rat.AbsoluteValue.padic p.1 q
  calc
    aT (q : T) = aT (algebraMap ℚ_[p.1] T (q : ℚ_[p.1])) := by
      congr 1
    _ = NormedField.toAbsoluteValue ℚ_[p.1] (q : ℚ_[p.1]) :=
      padicFiniteExtensionAbsoluteValue_extends p.1 T _
    _ = Rat.AbsoluteValue.padic p.1 q := by
      change ‖(q : ℚ_[p.1])‖ = Rat.AbsoluteValue.padic p.1 q
      simpa only [Rat.AbsoluteValue.padic_eq_padicNorm] using
        Padic.eq_padicNorm (p := p.1) q

end KroneckerWeber

end
