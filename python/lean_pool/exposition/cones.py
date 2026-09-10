"""Per-declaration dependency metrics for the all-declarations viewer.

Given the intra-project dependency lists of one shard, computes for every
node its direct dependent count and the sizes of its two transitive cones:
the *dependency cone* (everything it transitively uses) and the *dependent
cone* (everything that transitively uses it). Both exclude the node itself.

Cones are accumulated over the SCC condensation as Python integer bitsets:
components come out of Tarjan dependencies-first, so one forward pass unions
each component's members with the cones of the components it depends on,
and one backward pass does the same for dependents. Cycles (mutual
recursion) therefore count every other member of the cycle in both cones.
"""

from __future__ import annotations

from dataclasses import dataclass

from lean_pool.exposition.layout import strongly_connected_components


@dataclass
class ConeMetrics:
    """Per-node metrics, indexed by shard-local node id."""

    dependent_counts: list[int]
    dependency_cone_sizes: list[int]
    dependent_cone_sizes: list[int]


def _component_cones(
    components: list[list[int]],
    component_of: list[int],
    neighbors: list[list[int]],
    order: range,
) -> list[int]:
    """Union member bits with neighbor-component cones, visiting ``order``.

    ``order`` must list every component after all components reachable from
    it through ``neighbors``.
    """
    cones = [0] * len(components)
    for component_index in order:
        bits = 0
        for node in components[component_index]:
            bits |= 1 << node
        for node in components[component_index]:
            for neighbor in neighbors[node]:
                neighbor_component = component_of[neighbor]
                if neighbor_component != component_index:
                    bits |= cones[neighbor_component]
        cones[component_index] = bits
    return cones


def compute_cone_metrics(dependencies: list[list[int]]) -> ConeMetrics:
    """Return dependent counts and transitive cone sizes for every node.

    ``dependencies[n]`` lists the node ids that node ``n`` depends on
    (self references already removed).
    """
    node_count = len(dependencies)
    dependents: list[list[int]] = [[] for _ in range(node_count)]
    for node, node_dependencies in enumerate(dependencies):
        for dependency in node_dependencies:
            dependents[dependency].append(node)
    components = strongly_connected_components(dependencies)
    component_of = [0] * node_count
    for component_index, members in enumerate(components):
        for node in members:
            component_of[node] = component_index
    forward = range(len(components))
    backward = range(len(components) - 1, -1, -1)
    dependency_cones = _component_cones(components, component_of, dependencies, forward)
    dependent_cones = _component_cones(components, component_of, dependents, backward)
    return ConeMetrics(
        dependent_counts=[len(nodes) for nodes in dependents],
        dependency_cone_sizes=[
            (dependency_cones[component_of[node]] & ~(1 << node)).bit_count()
            for node in range(node_count)
        ],
        dependent_cone_sizes=[
            (dependent_cones[component_of[node]] & ~(1 << node)).bit_count()
            for node in range(node_count)
        ],
    )
