import unittest
from unittest import TestCase

t = {
    10: [5, 15],
    5: [3, 4],
    15: [16]
}

def sum_tree_nodes_recursive(tree, node):
    total = node

    if node not in tree:
        return total

    if len(tree[node]) > 0:
        total += sum_tree_nodes_recursive(tree, t[node][0])

    if len(tree[node]) > 1:
        total += sum_tree_nodes_recursive(tree, t[node][1])

    return total

def sum_tree_nodes_loop(tree, node):
    total = node
    nodes = [node]

    while len(nodes) > 0:
        curr_node = nodes.pop(0)

        if curr_node not in tree:
            continue

        sub_nodes = tree[curr_node]

        if len(sub_nodes) > 0:
            total += sub_nodes[0]
            nodes.append(sub_nodes[0])

        if len(sub_nodes) > 1:
            total += sub_nodes[1]
            nodes.append(sub_nodes[1])

    return total

class Tests(TestCase):

    def test_adds_node_values(self):
        self.assertEqual(sum_tree_nodes_recursive(t, 10), 53)
        self.assertEqual(sum_tree_nodes_loop(t, 10), 53)

unittest.main()
