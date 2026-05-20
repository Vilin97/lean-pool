/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/

import LeanPool.BruhatTits.Cartan
import LeanPool.BruhatTits.Graph
import LeanPool.BruhatTits.Harmonic
import LeanPool.BruhatTits.Lattice
import LeanPool.BruhatTits.Utils

/-!
# Formalisation of the Bruhat-Tits Tree

Source: url:https://doi.org/10.1007/978-3-642-61856-7
Authors: Judith Ludwig, Christian Merten
Status: verified
Main declarations: `BruhatTits.BTtree`, `BruhatTits.BTlaplace_surjective`
Tags: algebraic-geometry, graph-theory, discrete-valuation-rings
MSC: 20E42, 05C25, 13H05
-/

open Module

/-!
## Mathematical overview

This project defines the Bruhat-Tits graph of `GL₂(K)` over the fraction field
of a discrete valuation ring `R`. Vertices are homothety classes of `R`-lattices
in `K²`, edges connect standard neighbouring lattices, and `GL₂(K)` acts on the
resulting graph.

The main graph-theoretic results prove that this graph is connected and acyclic,
hence a tree, and that when the residue field is finite every vertex has degree
`#(ResidueField R) + 1`. The import also contains the underlying Cartan
decomposition for matrices over a discretely valued field and an application to
surjectivity of a Laplacian on harmonic cochains.

## Provenance

Imported from <https://github.com/chrisflav/bruhat-tits>. Upstream is complete
and Apache-2.0 licensed. Ported from Lean v4.19.0 to Lean Pool's v4.30.0-rc2.
-/
