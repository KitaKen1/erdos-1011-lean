"""Packaging/evidence regression tests; these do not replace Lean checking."""
import json
import unittest
import re

from check_r5_kernel_web_local import assess, verify_record, AXIOM_LINE, AUDIT, EXPECTED_TYPE, FINISHED
from prepare_r5_kernel_web import (ROOT, OUTPUT, MANIFEST, chunks, dependency_order,
                                   raw_string, render, sha256, split_imports, without_comments)
from prepare_c11_low_witness import DEST, generate as low_generate, witnesses
from prepare_c11_complement_witness import generate as complement_generate, witnesses as complement_witnesses
from prepare_c9_witness import canonical_masks as c9_masks, generate as c9_generate, witnesses as c9_witnesses
from prepare_s11_cover_chunks import generate as cover_generate, representative_masks
from prepare_s9_finite_decisions import INSERT, paths as s9_paths, transform as s9_transform


class StandalonePackagingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source, cls.manifest = render()

    def test_reproducible_bundle_and_manifest(self):
        self.assertEqual(OUTPUT.read_text(), self.source)
        self.assertEqual(json.loads(MANIFEST.read_text()), self.manifest)
        self.assertEqual(self.manifest["status"], "GENERATED_NOT_VERIFIED")

    def test_all_modules_present_in_dependency_order(self):
        order, external = dependency_order()
        self.assertEqual(len(order), len(self.manifest["modules"]))
        seen = set()
        for name, _, _, imports in order:
            for imp in imports:
                if imp.startswith("R5Kernel"):
                    self.assertIn(imp, seen)
            self.assertNotIn(name, seen)
            seen.add(name)
        self.assertEqual(order[-1][0], "R5Kernel.Final")
        self.assertNotIn("R5Kernel.Parts.M031", seen)
        self.assertNotIn("R5Kernel.Parts.M032", seen)
        self.assertTrue(all(x.startswith(("Lean.", "Mathlib.")) for x in external))

    def test_only_import_lines_are_removed(self):
        order, _ = dependency_order()
        for name, source, body, _ in order:
            with self.subTest(module=name):
                self.assertEqual(body, "".join(l for l in source.splitlines(True)
                                               if not l.startswith("import ")))
                self.assertIn("r5_kernel_web_source " + raw_string(name) + "\n" + raw_string(body),
                              self.source)

    def test_patch_chunks_preserve_source_exactly(self):
        parts = chunks(self.source)
        self.assertEqual("".join(parts), self.source)
        self.assertTrue(all(p.endswith("\n") for p in parts))
        self.assertLess(max(len(p.encode()) for p in parts), 25000)

    def test_nested_comments_do_not_create_imports(self):
        source = '/- outer /- import Fake.Inner -/\nimport Fake.Outer -/\nimport Mathlib.Tactic\n#check Nat\n'
        imports, body = split_imports(source)
        self.assertEqual(imports, ["Mathlib.Tactic"])
        self.assertIn("#check Nat", body)
        self.assertNotIn("Fake", without_comments(body))

    def test_raw_string_delimiter_is_unambiguous(self):
        self.assertEqual(raw_string('a"#b"##c'), 'r###"a"#b"##c"###')

    def test_low_card_witness_sources_reproduce(self):
        for name, source in low_generate():
            self.assertEqual((DEST / (name + ".lean")).read_text(), source)
            code = without_comments(source)
            self.assertNotRegex(code, r"\b(?:sorry|admit|axiom|native_decide)\b")

    def test_low_card_witness_maps_and_coverage(self):
        source = (DEST / "S11C11CanonicalDefinitions.lean").read_text()
        masks = list(map(int, re.findall(r"\d+", source.split(": List ℕ :=", 1)[1].split("]", 1)[0])))
        rows = witnesses()
        self.assertEqual(len(rows), 1024)
        for mask, (c, d) in rows.items():
            self.assertLess(c, 125)
            self.assertLess(d, 22)
            moved = sum(1 << ((x + d if d < 11 else d - x) % 11)
                        for x in range(11) if masks[c] >> x & 1)
            self.assertEqual(moved, mask)

    def test_complement_witness_source_reproduces(self):
        self.assertEqual((DEST / "S11C11ComplementWitness.lean").read_text(), complement_generate())

    def test_complement_witnesses_cover_all_representatives(self):
        source = (DEST / "S11C11CanonicalDefinitions.lean").read_text()
        masks = list(map(int, re.findall(r"\d+", source.split(": List ℕ :=", 1)[1].split("]", 1)[0])))
        rows = complement_witnesses()
        self.assertEqual(len(rows), 126)
        for mask, (c, d) in zip(masks, rows):
            self.assertLess(c, 126)
            self.assertLess(d, 22)
            moved = sum(1 << ((x + d if d < 11 else d - x) % 11)
                        for x in range(11) if masks[c] >> x & 1)
            self.assertEqual(moved, 2047 ^ mask)

    def test_c9_witness_sources_reproduce(self):
        for name, source in c9_generate():
            self.assertEqual((DEST / (name + ".lean")).read_text(), source)

    def test_c9_witnesses_cover_all_masks(self):
        masks = c9_masks()
        rows = c9_witnesses()
        self.assertEqual(set(rows), set(range(512)))
        for mask, (c, d) in rows.items():
            self.assertIn(c, masks)
            self.assertLess(d, 18)
            moved = sum(1 << ((x + d if d < 9 else d - x) % 9)
                        for x in range(9) if c >> x & 1)
            self.assertEqual(moved, mask)

    def test_cover_bound_sources_reproduce(self):
        for ell in (5, 7):
            for name, source in cover_generate(ell):
                self.assertEqual((DEST / (name + ".lean")).read_text(), source)

    def test_cover_partition_preserves_every_representative_once(self):
        for ell, count, bound in ((5, 55, 284), (7, 89, 516)):
            rows = []
            for name, source in cover_generate(ell):
                if "CoverBoundChunk" not in name:
                    continue
                block = list(map(int, re.findall(r"\d+", source.split(": List ℕ :=", 1)[1].split("]", 1)[0])))
                self.assertLessEqual(len(block), 8)
                self.assertIn(f"≤ {bound}", source)
                rows.extend(block)
            self.assertEqual(rows, representative_masks(ell))
            self.assertEqual(len(rows), count)
            self.assertEqual(len(set(rows)), count)

    def test_s9_decision_edit_is_local_and_preserves_all_other_text(self):
        self.assertEqual(len(s9_paths()), 96)
        for path in s9_paths():
            source = path.read_text()
            self.assertEqual(source.count(INSERT), 1)
            self.assertEqual(s9_transform(source), source)
            self.assertEqual(s9_transform(source.replace(INSERT, "")), source)
            self.assertIn("end Erdos1011", source)

    def test_s9_decision_edit_rejects_unexpected_source(self):
        for source in ("", "namespace Erdos1011\nnamespace Erdos1011\n",
                       "namespace Erdos1011\nattribute [local instance 2000] Other"):
            with self.assertRaises(ValueError):
                s9_transform(source)


class StandaloneEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.modules = [dict(module="R5Kernel.Common"), dict(module="R5Kernel.Final")]
        self.text = "\n".join(
            [line for m in self.modules for line in
             ("R5_WEB_BEGIN " + m["module"], "R5_WEB_END " + m["module"])] +
            [EXPECTED_TYPE, AXIOM_LINE, AUDIT, FINISHED]) + "\n"

    def accepted(self, text=None, code=0):
        checks, _ = assess(self.text if text is None else text, code, self.modules)
        return all(checks.values())

    def test_complete_run(self):
        self.assertTrue(self.accepted())

    def test_missing_or_reordered_modules(self):
        self.assertFalse(self.accepted(self.text.replace("R5_WEB_END R5Kernel.Common\n", "")))
        self.assertFalse(self.accepted(self.text.replace("R5_WEB_END R5Kernel.Common", "R5_WEB_END R5Kernel.Final")))

    def test_reject_overlapping_module_events(self):
        interleaved = self.text.replace(
            "R5_WEB_END R5Kernel.Common\nR5_WEB_BEGIN R5Kernel.Final",
            "R5_WEB_BEGIN R5Kernel.Final\nR5_WEB_END R5Kernel.Common")
        self.assertFalse(self.accepted(interleaved))

    def test_reject_nonzero_exit_even_with_success_messages(self):
        self.assertFalse(self.accepted(code=1))

    def test_reject_changed_target_range(self):
        self.assertFalse(self.accepted(self.text.replace("80 ≤ n", "118 ≤ n")))

    def test_reject_missing_or_weakened_audit(self):
        self.assertFalse(self.accepted(self.text.replace(AXIOM_LINE, "")))
        self.assertFalse(self.accepted(self.text.replace(AUDIT, "")))
        self.assertFalse(self.accepted(self.text.replace(FINISHED, "")))
        self.assertFalse(self.accepted(self.text.replace("Quot.sound]", "Quot.sound, sorryAx]")))

    def test_reject_error_diagnostic(self):
        self.assertFalse(self.accepted(self.text + "SomeFile.lean:1:0: error: test failure\n"))

    def test_reject_memory_failure_even_with_complete_markers(self):
        for message in ("lean::memory_exception", "excessive memory consumption detected at 'interpreter'"):
            with self.subTest(message=message):
                self.assertFalse(self.accepted(self.text + message + "\n"))

    def make_record(self):
        manifest = dict(modules=self.modules, source_sha256="source-hash", bytes=100,
                        lean_toolchain="test-version", lake_manifest_sha256="pin-hash",
                        source=str(OUTPUT.relative_to(ROOT)))
        record = dict(status="PASS", exit_code=0, completed_modules=2, module_count=2,
                      source_sha256="source-hash", bundle_manifest_sha256="manifest-hash",
                      log_sha256=sha256(self.text.encode()), checks=dict(inputs_unchanged=True),
                      command=["lake", "env", "lean", "-j1", "-M6144", str(OUTPUT)],
                      **{k: manifest[k] for k in ("bytes", "lean_toolchain", "lake_manifest_sha256", "source")})
        return record, manifest

    def test_record_hashes_and_metadata(self):
        record, manifest = self.make_record()
        self.assertEqual(verify_record(record, self.text, manifest, "manifest-hash")["offline_evidence_check"], "PASS")
        for field in ("source_sha256", "bundle_manifest_sha256", "log_sha256", "lean_toolchain"):
            changed = dict(record, **{field: "changed"})
            with self.subTest(field=field), self.assertRaises(ValueError):
                verify_record(changed, self.text, manifest, "manifest-hash")

    def test_record_accepts_a_different_checkout_prefix(self):
        record, manifest = self.make_record()
        record["command"][-1] = "/another/checkout/" + manifest["source"]
        self.assertEqual(verify_record(record, self.text, manifest, "manifest-hash")[
            "offline_evidence_check"], "PASS")

    def test_record_rejects_wrong_source_or_flags(self):
        for target in ("/tmp/Other.lean", "Erdos1011R5KernelLean4Web.lean",
                       "/tmp/../lean4web/Erdos1011R5KernelLean4Web.lean"):
            record, manifest = self.make_record()
            record["command"][-1] = target
            with self.subTest(target=target), self.assertRaisesRegex(ValueError, "command"):
                verify_record(record, self.text, manifest, "manifest-hash")
        record, manifest = self.make_record()
        record["command"][3] = "-j8"
        with self.assertRaisesRegex(ValueError, "command"):
            verify_record(record, self.text, manifest, "manifest-hash")

    def test_record_rejects_different_command(self):
        record, manifest = self.make_record()
        record["command"] = ["lake", "build", "R5Kernel.Final"]
        with self.assertRaisesRegex(ValueError, "command"):
            verify_record(record, self.text, manifest, "manifest-hash")


if __name__ == "__main__":
    unittest.main()
