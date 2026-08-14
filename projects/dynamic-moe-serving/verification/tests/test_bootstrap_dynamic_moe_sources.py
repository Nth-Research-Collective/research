import tempfile
import unittest
from pathlib import Path

from scripts.bootstrap_dynamic_moe_sources import (
    BootstrapError,
    SOURCE_PINS,
    sha256,
    validate_existing_file,
)


class TestDynamicMoeSourceBootstrap(unittest.TestCase):
    def test_source_pins_are_complete(self):
        self.assertEqual(
            {pin.relative_path for pin in SOURCE_PINS},
            {"2607.17880v1.tar", "2304.01889v2.tar"},
        )
        for pin in SOURCE_PINS:
            self.assertEqual(len(pin.sha256), 64)
            self.assertEqual(len(pin.member_sha256), 64)
            int(pin.sha256, 16)
            int(pin.member_sha256, 16)

    def test_existing_file_validation_accepts_exact_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source"
            path.write_bytes(b"dynamic-moe-source")
            self.assertEqual(validate_existing_file(path, sha256(path)), sha256(path))

    def test_existing_file_validation_refuses_mismatch(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source"
            path.write_bytes(b"unexpected")
            with self.assertRaisesRegex(BootstrapError, "refusing to overwrite"):
                validate_existing_file(path, "0" * 64)


if __name__ == "__main__":
    unittest.main()
