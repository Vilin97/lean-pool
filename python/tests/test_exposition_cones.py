"""Tests for per-declaration dependency cone metrics."""

from __future__ import annotations

from lean_pool.exposition.cones import compute_cone_metrics


def test_chain_and_diamond() -> None:
    """Cones are transitive and exclude the node itself; counts are direct."""
    # 0 <- 1 <- 3, 0 <- 2 <- 3 (3 depends on 1 and 2, both depend on 0),
    # 4 depends on 3, 5 is isolated.
    dependencies = [[], [0], [0], [1, 2], [3], []]
    metrics = compute_cone_metrics(dependencies)
    assert metrics.dependent_counts == [2, 1, 1, 1, 0, 0]
    assert metrics.dependency_cone_sizes == [0, 1, 1, 3, 4, 0]
    assert metrics.dependent_cone_sizes == [4, 2, 2, 1, 0, 0]


def test_cycle_members_count_each_other() -> None:
    """Members of a cycle appear in each other's cones exactly once."""
    # 0 <-> 1 (mutual recursion), 2 depends on 1.
    dependencies = [[1], [0], [1]]
    metrics = compute_cone_metrics(dependencies)
    assert metrics.dependent_counts == [1, 2, 0]
    assert metrics.dependency_cone_sizes == [1, 1, 2]
    assert metrics.dependent_cone_sizes == [2, 2, 0]


def test_empty_graph() -> None:
    """No nodes yields empty metric lists."""
    metrics = compute_cone_metrics([])
    assert metrics.dependent_counts == []
    assert metrics.dependency_cone_sizes == []
    assert metrics.dependent_cone_sizes == []
