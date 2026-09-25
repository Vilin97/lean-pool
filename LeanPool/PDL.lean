/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Beth

/-!
# Craig interpolation and Beth definability for propositional dynamic logic

Source: arxiv:2503.13276, url:https://github.com/m4lvin/lean4-pdl
Authors: PDL formalization contributors
Status: verified
Main declarations: `PDL.interpolation`, `PDL.beth`
Tags: modal-logic, propositional-dynamic-logic, craig-interpolation, beth-definability, tableaux
MSC: 03B45, 03B70, 03F03
-/

/-!
This development is ported from `m4lvin/lean4-pdl` at commit
`ec3b050e59cd829a350e92c512951a381a80cddd`, under Apache-2.0.
The human formalization contributors are Malvin Gattinger, Madeleine Gignoux,
Noam Cohen, Haitian Wang, Wietse Bosman, Xiaoshuang Yang, Amos Nicodemus, Andrés Goens,
DdosSantosGomes, Eshel Yaron and Dionysis Yusofy. They and the Aristotle proof assistant
jointly developed these proofs. The project registry records the paper authors separately from the
formalization contributors and records mixed human/AI provenance.

The entry points prove semantic existence of PDL interpolants and local Beth
definitions; they do not claim an executable extraction algorithm or a complexity bound.
-/
