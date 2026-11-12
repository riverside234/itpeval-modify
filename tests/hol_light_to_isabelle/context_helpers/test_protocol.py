"""Reject stale, malformed, or proof-bearing fact inspection results."""

from pathlib import Path
import tempfile
import unittest
import xml.etree.ElementTree as ET

from eval.pipeline.hol_light_to_isabelle.babel_formal_pipeline.v2_dsp.native_search import (
    FACTS_VERSION, RESULT_VERSION, NativeFailure, read_result,
)


class FactProtocolTests(unittest.TestCase):
    def test_inspection_is_versioned_request_bound_and_non_proving(self):
        request = {"action": "inspect_facts", "request_id": "one", "input_sha256": "digest",
                   "fact_names": ["A.rule"]}
        result = ET.Element("dsp_result", schema=RESULT_VERSION, action="inspect_facts",
                            request_id="one", input_sha256="digest", success="true", target_closed="false")
        for field in ("proof", "error", "category", "attempts", "settings"):
            ET.SubElement(result, field)
        facts = ET.SubElement(result, "facts", schema=FACTS_VERSION, boundary="before_oracle")
        item = ET.SubElement(facts, "fact", requested="A.rule", name="A.rule", status="resolved", scope="global")
        ET.SubElement(item, "proposition").text = "P ==> P"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "result.xml"
            ET.ElementTree(result).write(path, encoding="utf-8")
            parsed = read_result(path, request, returncode=0)
            self.assertEqual(parsed["fact_inspection"]["facts"][0]["propositions"], ["P ==> P"])
            for node, name, value in ((item, "requested", "unrequested"),
                                      (facts, "schema", "unknown_version"),
                                      (result, "target_closed", "true")):
                previous = node.get(name)
                node.set(name, value)
                ET.ElementTree(result).write(path, encoding="utf-8")
                with self.assertRaises(NativeFailure) as error:
                    read_result(path, request, returncode=0)
                self.assertEqual(error.exception.category, "protocol_error")
                node.set(name, previous)
