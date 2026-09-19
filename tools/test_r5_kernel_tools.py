"""Current proof-data regressions; historical migration tests are archived."""
import re
import unittest
from itertools import combinations

from analyze_r5_symmetry import canonicalize, independent_masks
from analyze_small_uniform import uniform_rows
from build_r5_kernel_serial import ready_modules
from prepare_r5_kernel_web import PROJECT, dependency_order, without_comments
from prepare_s7 import generate as generate_s7, witness_rows as s7_witness_rows


class KernelPreparationTests(unittest.TestCase):
    def test_final_dispatcher_imports_verified_branches(self):
        source = (PROJECT / "R5Kernel/Parts/M079.lean").read_text()
        for module in ("Parts.M033", "S7LegacyAPI", "S8LegacyAPI", "S9DirectAdapter", "Parts.M078"):
            self.assertIn("import R5Kernel." + module, source)
        source78 = (PROJECT / "R5Kernel/Parts/M078.lean").read_text()
        self.assertNotIn("import R5Kernel.Parts.M077", source78)
        self.assertIn("import R5Kernel.S11Dispatcher", source78)
        self.assertIn("import R5Kernel.S10LegacyAPI", source78)

    def test_s7_generator_reproduces_checked_sources(self):
        for ell in (5, 7):
            for name, source in generate_s7(ell):
                with self.subTest(module=name):
                    self.assertEqual((PROJECT / "R5Kernel" / (name + ".lean")).read_text(), source)

    def test_s7_certificates_and_orbits(self):
        for ell, count, bound in ((5, 23, 65), (7, 17, 54)):
            rows = s7_witness_rows(ell)
            types = independent_masks(7, ell)
            reps = {canonicalize(m, 7, ell)[0] for m in range(1, 128)}
            self.assertEqual(set(rows), reps)
            self.assertEqual(len(rows), count)
            values = []
            for mask, (beta, weights) in rows.items():
                self.assertEqual(len(weights), 7)
                self.assertGreaterEqual(beta, max(bin(i).count("1") for i in types if i & mask == i))
                value = beta * sum(w for x, w in enumerate(weights) if mask >> x & 1)
                value += sum(max(0, 2 * bin(i).count("1") -
                                 sum(w for x, w in enumerate(weights) if (i & mask) >> x & 1))
                             for i in types if i & mask)
                values.append(value)
            self.assertEqual(max(values), bound)
        self.assertLessEqual(10 + 65 // 2, 42)
        self.assertLessEqual(12 + 54 // 2, 42)

    def test_s6_attached_explicit_color_witnesses(self):
        source = (PROJECT / "R5Kernel/Parts/M026.lean").read_text()
        rows = {int(k): tuple(map(int, re.findall(r"\d+", values)))
                for k, values in re.findall(r"^  \| (\d+) => !\[(.*?)\]$", source, re.M)}
        admissible = {k for k in range(1, 32)
                      if all(not (k >> i & 1 and k >> ((i + 1) % 5) & 1)
                             for i in range(5))}
        self.assertEqual(set(rows), admissible)
        self.assertEqual(len(rows), 10)
        for k, colors in rows.items():
            with self.subTest(mask=k):
                self.assertEqual(len(colors), 6)
                self.assertTrue(all(0 <= c < 3 for c in colors))
                edges = [(i, (i + 1) % 5) for i in range(5)]
                edges += [(5, i) for i in range(5) if k >> i & 1]
                self.assertTrue(all(colors[a] != colors[b] for a, b in edges))
                for mask in range(64):
                    if all(not (mask >> a & 1 and mask >> b & 1) for a, b in edges):
                        self.assertLessEqual(len({colors[i] for i in range(6)
                                                  if mask >> i & 1}), 2)

    def test_s6_rotation_cover_by_blocked_rotations(self):
        blocked_a = [i if i < 5 else (i + 4) % 5 for i in range(10)]
        blocked_b = [(i + 4) % 5 if i < 5 else i - 5 for i in range(10)]
        for i in range(10):
            self.assertEqual([j for j in range(5) if i in (j, 5 + (j + 1) % 5)],
                             [blocked_a[i]])
            self.assertEqual([j for j in range(5) if i in ((j + 1) % 5, 5 + j)],
                             [blocked_b[i]])
        # A tagged index represents one member of X or Y, so this covers
        # all pairs with total cardinality at most four without 2^20 scanning.
        for count in range(5):
            for selected in combinations(range(20), count):
                bad = {blocked_a[i] if i < 10 else blocked_b[i - 10] for i in selected}
                self.assertLessEqual(len(bad), count)
                self.assertTrue(set(range(5)) - bad)

    def test_s10_rows_and_chunks_cover_every_symmetry_representative(self):
        for ell, count, bound in ((5, 47, 226), (7, 71, 214), (9, 91, 184)):
            with self.subTest(ell=ell):
                expected_reps = sorted({canonicalize(m, 10, ell)[0]
                                        for m in range(1, 1024)})
                self.assertEqual(len(expected_reps), count)
                source = (PROJECT / f"R5Kernel/S10C{ell}Data.lean").read_text()
                match = re.search(r"kernelS10RepresentativeMasks : List ℕ := \[(.*?)\]",
                                  source)
                actual_reps = list(map(int, re.findall(r"\d+", match.group(1))))
                self.assertEqual(actual_reps, expected_reps)
                actual_rows = [tuple(map(int, fields)) for fields in re.findall(
                    r"^  \| (\d+) => \((\d+), (\d+)\)$", source, re.M)]
                expected_rows = uniform_rows(10, ell)
                self.assertEqual(actual_rows, [expected_rows[m][:3] for m in expected_reps])
                checked = []
                for k in range((count + 7) // 8):
                    chunk = (PROJECT / f"R5Kernel/S10C{ell}Checks{k}.lean").read_text()
                    block = re.search(r"def block\d+ : List ℕ := \[(.*?)\]", chunk)
                    checked.extend(map(int, re.findall(r"\d+", block.group(1))))
                    self.assertIn(f"coverValue m ≤ {bound}", chunk)
                    self.assertIn("decide +kernel", chunk)
                self.assertEqual(checked, expected_reps)

    def test_s10_product_covers_exactly_the_independent_sets(self):
        for ell, count, alpha in ((5, 351, 7), (7, 231, 6), (9, 151, 5)):
            with self.subTest(ell=ell):
                cycle_parts = [0] + independent_masks(ell, ell)
                product = [cycle | (isolates << ell)
                           for cycle in cycle_parts for isolates in range(1 << (10 - ell))]
                independent = independent_masks(10, ell)
                self.assertEqual(len(independent), count)
                self.assertEqual(len(set(product)), count + 1)
                self.assertEqual(set(product), {0} | set(independent))
                self.assertEqual(max(bin(m).count("1") for m in independent), alpha)

    def test_s8_uniform_rows_match_exact_integer_exploration(self):
        source = (PROJECT / "R5Kernel/S8UniformData.lean").read_text()
        for ell in (5, 7):
            section = source.split(f"def kernelS8C{ell}UniformRow", 1)[1]
            section = section.split("  | _ => (0, 0)", 1)[0]
            actual = [(int(m), int(b), int(w)) for m, b, w in re.findall(
                r"^  \| (\d+) => \((\d+), (\d+)\)$", section, re.M)]
            expected = [row[:3] for row in uniform_rows(8, ell)[1:]]
            self.assertEqual(actual, expected)

    def test_s8_explicit_types_match_graph_independence(self):
        source = (PROJECT / "R5Kernel/S8UniformData.lean").read_text()
        for ell in (5, 7):
            section = source.split(f"def kernelS8C{ell}UniformTypes", 1)[1]
            section = section.split(" : List (Finset (Fin 8))", 1)[0]
            actual = [sum(1 << int(x) for x in re.findall(r"\d+", group))
                      for group in re.findall(r"\{([0-7, ]+)\}", section)]
            self.assertEqual(actual, independent_masks(8, ell))

    def test_s8_uniform_chunks_cover_all_masks(self):
        for ell in (5, 7):
            masks = []
            for k in range(16):
                path = PROJECT / f"R5Kernel/S8C{ell}UniformChunk{k}.lean"
                source = path.read_text()
                match = re.search(r"∀ i : Fin (\d+),\s*"
                                  r"KernelS8C\d+UniformCertificate \(i.val \+ (\d+)\)", source)
                self.assertIsNotNone(match)
                count, offset = map(int, match.groups())
                masks.extend(range(offset, offset + count))
                self.assertIn("decide +kernel", source)
            self.assertEqual(masks, list(range(256)))

    def test_experimental_uniform_bounds_fit_final_budget(self):
        expected = {(8, 5): 114, (8, 7): 93, (9, 5): 164, (9, 7): 146,
                    (9, 9): 120, (10, 5): 226, (10, 7): 214, (10, 9): 184}
        budget = {8: 77, 9: 114, 10: 149}
        for (s, ell), bound in expected.items():
            with self.subTest(s=s, ell=ell):
                self.assertEqual(max(row[3] for row in uniform_rows(s, ell)), bound)
                self.assertLessEqual(s * s // 4 + bound // 2, budget[s])

    def test_uniform_exploration_rejects_out_of_scope_inputs(self):
        for s, ell in ((8, 4), (11, 5), (8, 9)):
            with self.assertRaises(ValueError):
                uniform_rows(s, ell)

    def test_serial_build_selects_only_ready_local_modules(self):
        output = (
            "✖ [1/4] Building R5Kernel.Probes.Leaf\n"
            "error: target is out-of-date and needs to be rebuilt\n"
            "✖ [2/4] Building Mathlib.SomeDependency\n"
            "error: target is out-of-date and needs to be rebuilt\n"
            "✖ [3/4] Building R5Kernel.Probes.Failed (1s)\n"
            "error: proof failed\n"
            "✔ [4/4] Built R5Kernel.Probes.Cached\n"
        )
        self.assertEqual(ready_modules(output), ["R5Kernel.Probes.Leaf"])

    def test_lower_replacement_has_no_native_calls(self):
        source = (PROJECT / "R5Kernel/Parts/M003.lean").read_text()
        self.assertNotIn("native_decide", source)
        self.assertEqual(source.count("decide +kernel"), 11)

    def test_isolated_vertex_normalization(self):
        self.assertEqual(canonicalize(1 << 10, 11, 5)[0], 1 << 5)
        self.assertEqual(canonicalize(1 << 4, 11, 5)[0], 1)
        self.assertEqual(canonicalize(2047, 11, 5)[0], 2047)

    def test_cycle_independence_count(self):
        independent = independent_masks(11, 5)
        self.assertEqual(len(independent), 703)
        self.assertEqual(max(bin(mask).count("1") for mask in independent), 8)

    def test_small_product_covers_exactly_the_independent_sets(self):
        cycle_parts = [0] + independent_masks(5, 5)
        product = [cycle | (isolates << 5)
                   for cycle in cycle_parts for isolates in range(64)]
        self.assertEqual(len(product), 704)
        self.assertEqual(len(set(product)), 704)
        self.assertEqual(set(product), {0} | set(independent_masks(11, 5)))

    def test_cycle_orbits_cover_all_32_subsets(self):
        representatives = {canonicalize(mask, 5, 5)[0] for mask in range(32)}
        self.assertEqual(representatives, {0, 1, 3, 5, 7, 11, 15, 31})

    def test_c9_cycle_orbits_and_independent_types(self):
        representatives = {canonicalize(mask, 9, 9)[0] for mask in range(1 << 9)}
        self.assertEqual(len(representatives), 46)
        self.assertEqual(len(independent_masks(9, 9)), 75)

    def test_c9_representative_table_has_expected_packing(self):
        source = (PROJECT / "R5Kernel/Probes/S11C9CanonicalDefinitions.lean").read_text()
        match = re.search(
            r"def kernelS11C9RepresentativeMasks : List Nat := \[(.*?)\]\n\n",
            source, re.S)
        self.assertIsNotNone(match)
        reps = {int(value) for value in re.findall(r"\d+", match.group(1))}
        self.assertEqual(len(reps), 137)
        cycle_source = (PROJECT / "R5Kernel/Probes/S11C9OrbitDefinitions.lean").read_text()
        match = re.search(r"def kernelC9CanonicalMasks : List ℕ :=\n\s*\[(.*?)\]\n\n",
                          cycle_source, re.S)
        self.assertIsNotNone(match)
        cycles = {int(value) for value in re.findall(r"\d+", match.group(1))}
        packed = {c + 512 * ((1 << k) - 1) for c in cycles for k in range(3)}
        self.assertEqual(len(cycles), 46)
        self.assertEqual(packed, reps | {0})

    def test_packed_shapes_are_the_existing_55_representatives_plus_zero(self):
        source = (PROJECT / "R5Kernel/Probes/S11C5CanonicalDefinitions.lean").read_text()
        original = set(map(int, re.findall(r"^  \| (\d+) => mkR5RepDual11", source, re.M)))
        packed = {cycle + 32 * ((1 << count) - 1)
                  for cycle in (0, 1, 3, 5, 7, 11, 15, 31) for count in range(7)}
        self.assertEqual(len(packed), 56)
        self.assertEqual(packed, original | {0})

    def test_final_dependency_closure_has_no_trust_escape(self):
        order, _ = dependency_order()
        self.assertEqual(len(order), 359)
        expected = {PROJECT / (name.replace(".", "/") + ".lean")
                    for name, *_ in order}
        self.assertEqual(set((PROJECT / "R5Kernel").rglob("*.lean")), expected)
        for name, source, _, _ in order:
            with self.subTest(module=name):
                self.assertNotRegex(without_comments(source),
                                    r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b")


if __name__ == "__main__":
    unittest.main()
