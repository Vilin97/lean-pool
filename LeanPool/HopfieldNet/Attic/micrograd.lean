/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

/-!
This file implements a "Value" object for automatic differentiation in Lean 4,
mirroring the semantics of Andrej Karpathy's `micrograd` library.

Instead of a mutable class, we use a functional approach:
- A `Value` is a `Nat` (an index) into a `Graph`.
- The `Graph` is an `Array Node`, where each `Node` stores its
  data and the operation (`Op`) that created it.
- A state monad, `AutogradM := StateM Graph`, is used to build the graph.
- The `backward` function is a pure function that takes the final graph
  and a root `Value`, and returns an `Array Float` of all gradients.
-/
namespace MicrogradLean

/--
Represents the type of operation that created this node.
The `Nat` values are indices into the `Graph` array.
-/
inductive Op where
  | val : Op
  | add (l r : Nat) : Op
  | mul (l r : Nat) : Op
  | pow (b : Nat) (e : Float) : Op
  | relu (v : Nat) : Op
  deriving Inhabited

/--
A node in the computation graph.
-/
structure Node where
  data : Float  -- The result of the forward pass
  op : Op       -- The operation that created this node
  deriving Inhabited

/--
The entire computation graph, stored as an array of nodes.
-/
abbrev Graph := Array Node

/--
A "Value" is just an index into the graph.
-/
abbrev Value := Nat

/--
The monad for building the computation graph.
It holds the `Graph` as its state.
-/
abbrev AutogradM := StateM Graph

--Core functions for building the computation graph,
--mirroring the Python `Value` class methods.
namespace Value

/--
Creates a new leaf `Value` (a constant).
Equivalent to `Value(data)`.
-/
def mk (data : Float) : AutogradM Value := do
  let graph ← get
  let id := graph.size
  let node : Node := { data := data, op := .val }
  set (graph.push node)
  return id

/--
Implementation for `__add__`.
-/
def add (l r : Value) : AutogradM Value := do
  let graph ← get
  -- In a real library, we'd add bounds checks.
  -- Here we assume valid IDs, similar to Python's reference handling.
  let lNode := graph[l]!
  let rNode := graph[r]!
  let id := graph.size
  let node : Node := {
    data := lNode.data + rNode.data,
    op := .add l r
  }
  set (graph.push node)
  return id

/--
Implementation for `__mul__`.
-/
def mul (l r : Value) : AutogradM Value := do
  let graph ← get
  let lNode := graph[l]!
  let rNode := graph[r]!
  let id := graph.size
  let node : Node := {
    data := lNode.data * rNode.data,
    op := .mul l r
  }
  set (graph.push node)
  return id

/--
Implementation for `__pow__`.
-/
def pow (b : Value) (e : Float) : AutogradM Value := do
  let graph ← get
  let bNode := graph[b]!
  let id := graph.size
  let node : Node := {
    data := bNode.data ^ e,
    op := .pow b e
  }
  set (graph.push node)
  return id

/--
Implementation for `relu`.
-/
def relu (v : Value) : AutogradM Value := do
  let graph ← get
  let vNode := graph[v]!
  let id := graph.size
  let data := if vNode.data < 0.0 then 0.0 else vNode.data
  let node : Node := {
    data := data,
    op := .relu v
  }
  set (graph.push node)
  return id

-- === Magic Method Implementations ===
-- These aren't "magic" in Lean, just regular functions
-- that build on the core operations.

/--
Implementation for `__neg__`.
-/
def neg (v : Value) : AutogradM Value := do
  -- Note: We create a new node for -1.0 each time.
  -- A real library might cache this.
  let minusOne ← Value.mk (-1.0)
  Value.mul v minusOne

/--
Implementation for `__sub__`.
-/
def sub (l r : Value) : AutogradM Value := do
  let rNeg ← Value.neg r
  Value.add l rNeg

/--
Implementation for `__truediv__`.
-/
def div (l r : Value) : AutogradM Value := do
  let rInv ← Value.pow r (-1.0)
  Value.mul l rInv

-- === Helper Typeclasses for Ergonomics ===
-- These mimic Python's dynamic dispatch for `value + 2.0`

class OpAdd (α : Type) (β : Type) (γ : outParam Type) where
  add : α -> β -> γ

class OpMul (α : Type) (β : Type) (γ : outParam Type) where
  mul : α -> β -> γ

-- Instances for `Value` operations within the `AutogradM` monad
instance : OpAdd Value Value (AutogradM Value) where add := Value.add
instance : OpMul Value Value (AutogradM Value) where mul := Value.mul

instance : OpAdd Value Float (AutogradM Value) where
  add l r := do
    let rVal ← Value.mk r
    Value.add l rVal

instance : OpAdd Float Value (AutogradM Value) where
  add l r := do
    let lVal ← Value.mk l
    Value.add lVal r

instance : OpMul Value Float (AutogradM Value) where
  mul l r := do
    let rVal ← Value.mk r
    Value.mul l rVal

instance : OpMul Float Value (AutogradM Value) where
  mul l r := do
    let lVal ← Value.mk l
    Value.mul lVal r

-- === Backward Pass ===

/--
Computes a reverse topological sort of the graph
starting from the `root`. The result is a list of `Value` IDs
from the `root` down to the leaves.
-/
private def topoSort (graph : Graph) (root : Value) : List Value :=
  let rec build (v : Value) (visited : Array Bool) (topo : List Value) : (Array Bool × List Value) :=
    -- If already visited, just return
    if visited.get! v then (visited, topo) else

    -- Mark as visited
    let visited := visited.set! v true
    let node := graph[v]!

    -- Recursively visit children
    let (visited', topo') :=
      match node.op with
      | .val => (visited, topo) -- No children
      | .add l r | .mul l r =>
        let (v1, t1) := build l visited topo
        build r v1 t1 -- Visit right child, pass state from left
      | .pow b _ => build b visited topo
      | .relu v' => build v' visited topo

    -- Add self to list *after* children (post-order)
    -- This results in a list [root, ..., leaves],
    -- which is a reverse topological sort.
    (visited', v :: topo')

  -- Start the build from the root, with an empty visited array and topo list
  let (_, topo) := build root (mkArray graph.size false) []
  topo

/--
The main `backward` pass function.

It performs a reverse topological sort and computes the gradient
for every node by applying the chain rule (VJP).

Returns an array of gradients, indexed by `Value` ID.
-/
def backward (graph : Graph) (root : Value) : Array Float :=
  -- Get the nodes in reverse topological order (root to leaves)
  let topo := topoSort graph root

  -- Initialize all gradients to 0.0
  let mut grads := mkArray graph.size 0.0

  -- `self.grad = 1`
  grads := grads.set! root 1.0

  -- Loop over nodes from root to leaves
  for v in topo do
    let node := graph[v]!
    let out_grad := grads[v]! -- The gradient of this node (d_L / d_v)

    -- Apply the chain rule (VJP) for this node's op
    -- This propagates the gradient `out_grad` to the node's children.
    match node.op with
    | .val => pure () -- Leaf node, gradient accumulation stops here

    | .add l r =>
      -- self.grad += out.grad
      grads := grads.modify l (· + out_grad)
      -- other.grad += out.grad
      grads := grads.modify r (· + out_grad)

    | .mul l r =>
      let lNode := graph[l]!
      let rNode := graph[r]!
      -- self.grad += other.data * out.grad
      grads := grads.modify l (· + rNode.data * out_grad)
      -- other.grad += self.data * out.grad
      grads := grads.modify r (· + lNode.data * out_grad)

    | .pow b e =>
      let bNode := graph[b]!
      -- self.grad += (other * self.data**(other-1)) * out.grad
      let grad_update := (e * (bNode.data ** (e - 1.0))) * out_grad
      grads := grads.modify b (· + grad_update)

    | .relu v' =>
      let vNode := graph[v']!
      -- self.grad += (out.data > 0) * out.grad
      let grad_update := if vNode.data > 0.0 then out_grad else 0.0
      grads := grads.modify v' (· + grad_update)

  return grads

/--
Implementation for `__repr__`.
Needs the graph and grads array to get the data.
-/
def repr (v : Value) (graph : Graph) (grads : Array Float) : String :=
  -- Use `getD` for safety, though IDs should be valid
  let node := graph.getD v (Inhabited.default)
  let grad := grads.getD v 0.0
  s!"Value(data={node.data}, grad={grad})"

end Value

-- === Example Usage ===

/--
This computation mirrors the example in `micrograd` to check gradients.
-/
def exampleComputation : AutogradM (Value × Value × Value) := do
  let a ← Value.mk 2.0
  let b ← Value.mk 3.0
  let c ← Value.mk 10.0

  -- Use the typeclass instances for `2.0 * a` etc.
  let e ← OpMul.mul a b
  let d ← OpAdd.add e c

  let f ← Value.mk 2.0
  let L ← OpMul.mul d f
  let L_relu ← Value.relu L

  return (L_relu, a, b) -- return root and inputs

/--
Runs the example computation and backward pass, returning a
string representation of the results.
-/
def runExample : String :=
  -- Run the computation, starting with an empty graph `#[]`
  let (graph, (l, a, b)) := exampleComputation #[]

  -- Run the backward pass
  let grads := Value.backward graph l

  -- Print the results
  -- a = 2.0, b = 3.0, c = 10.0, f = 2.0
  -- e = a * b = 6.0
  -- d = e + c = 16.0
  -- L = d * f = 32.0
  -- L_relu = relu(L) = 32.0
  --
  -- Gradients:
  -- L_relu.grad = 1.0
  -- L.grad = 1.0
  -- d.grad = f.data * L.grad = 2.0 * 1.0 = 2.0
  -- f.grad = d.data * L.grad = 16.0 * 1.0 = 16.0
  -- e.grad = d.grad = 2.0
  -- c.grad = d.grad = 2.0
  -- a.grad = b.data * e.grad = 3.0 * 2.0 = 6.0
  -- b.grad = a.data * e.grad = 2.0 * 2.0 = 4.0
  let lStr := Value.repr l graph grads
  let aStr := Value.repr a graph grads
  let bStr := Value.repr b graph grads
  s!"L: {lStr}\na: {aStr}\nb: {bStr}"

-- Use #eval to run the example and see the output
#eval runExample

end MicrogradLean
