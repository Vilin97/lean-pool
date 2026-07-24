"""Tests for the pure-Python layered graph layout."""

from __future__ import annotations

import random

from lean_pool.exposition.layout import compute_layout


def test_empty_graph() -> None:
    """An empty graph yields empty layers, orders, and sizes."""
    layout = compute_layout([])
    assert layout.node_layers == []
    assert layout.node_orders == []
    assert layout.layer_sizes == []


def test_chain() -> None:
    """A linear chain puts each node on its own layer."""
    layout = compute_layout([[], [0], [1], [2]])
    assert layout.node_layers == [0, 1, 2, 3]
    assert layout.node_orders == [0, 0, 0, 0]
    assert layout.layer_sizes == [1, 1, 1, 1]


def test_diamond() -> None:
    """A diamond shares the middle layer and peaks one layer above it."""
    layout = compute_layout([[], [0], [0], [1, 2]])
    assert layout.node_layers == [0, 1, 1, 2]
    assert layout.layer_sizes == [1, 2, 1]
    assert sorted(layout.node_orders[1:3]) == [0, 1]
    assert layout.node_orders[0] == 0
    assert layout.node_orders[3] == 0


def test_two_cycle_shares_layer() -> None:
    """Members of a 2-cycle SCC share a layer; dependents sit above it."""
    layout = compute_layout([[1], [0], [0]])
    assert layout.node_layers[0] == layout.node_layers[1] == 0
    assert layout.node_layers[2] == 1
    assert layout.layer_sizes == [2, 1]


def test_barycenter_removes_crossing() -> None:
    """Crossed edges between two layers are uncrossed by the sweeps."""
    # Layer 0: nodes 0, 1. Layer 1: node 2 above node 1, node 3 above node 0.
    layout = compute_layout([[], [], [1], [0]])
    assert layout.node_layers == [0, 0, 1, 1]
    assert layout.node_orders[0] == 0
    assert layout.node_orders[1] == 1
    # Node 3 (over node 0) must come before node 2 (over node 1).
    assert layout.node_orders[3] == 0
    assert layout.node_orders[2] == 1


def _random_graph(seed: int, node_count: int) -> list[list[int]]:
    """Build a mostly-acyclic random graph with one planted 2-cycle."""
    generator = random.Random(seed)
    dependencies: list[list[int]] = [[] for _ in range(node_count)]
    for node in range(1, node_count):
        for _ in range(generator.randint(0, 3)):
            dependencies[node].append(generator.randrange(node))
    dependencies[10].append(20)
    dependencies[20].append(10)
    return [sorted(set(deps)) for deps in dependencies]


def test_deterministic_across_runs() -> None:
    """Two runs over equal inputs give identical layouts."""
    first = compute_layout(_random_graph(42, 60))
    second = compute_layout(_random_graph(42, 60))
    assert first == second


def test_random_graph_invariants() -> None:
    """Layers respect dependencies and orders are per-layer permutations."""
    dependencies = _random_graph(7, 50)
    layout = compute_layout(dependencies)
    assert sum(layout.layer_sizes) == 50
    assert layout.node_layers[10] == layout.node_layers[20]
    for node, deps in enumerate(dependencies):
        if not deps:
            assert layout.node_layers[node] == 0
        for dependency in deps:
            assert layout.node_layers[node] >= layout.node_layers[dependency]
    per_layer: dict[int, list[int]] = {}
    for node, layer in enumerate(layout.node_layers):
        per_layer.setdefault(layer, []).append(layout.node_orders[node])
    for layer, orders in per_layer.items():
        assert sorted(orders) == list(range(layout.layer_sizes[layer]))
