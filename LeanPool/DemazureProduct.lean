/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.DemazureProduct.Utils
public import LeanPool.DemazureProduct.Valley
public import LeanPool.DemazureProduct.SlipFace
public import LeanPool.DemazureProduct.AspPerm
public import LeanPool.DemazureProduct.Submodular
public import LeanPool.DemazureProduct.ReducedProducts
public import LeanPool.DemazureProduct.Reduction
public import LeanPool.DemazureProduct.Transpositions
public import LeanPool.DemazureProduct.InvSet
public import LeanPool.DemazureProduct.Avoiding321
public import LeanPool.DemazureProduct.Tableaux

/-!
# Extended Demazure Product on ASP Permutations

Source: arxiv:2206.14227
Authors: Nathan Pflueger
Status: verified
Main declarations: `LeanPool.DemazureProduct.AspPerm.star`
Tags: algebraic-combinatorics, demazure-product, bruhat-order, permutations
MSC: 05E05, 20F55
-/

@[expose] public section

/-!
This project formalizes the extended Demazure product on almost-sign-preserving
integer permutations via min-plus matrix multiplication. The imported upstream
declarations are placed under `LeanPool.DemazureProduct` to avoid collisions
with the separate Demazure-operators project already in Lean Pool.
-/
