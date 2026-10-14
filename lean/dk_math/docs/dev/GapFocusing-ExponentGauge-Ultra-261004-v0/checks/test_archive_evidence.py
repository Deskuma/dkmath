"""Integrity and extraction safety regressions for archive_evidence.py."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

import archive_evidence as archive


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.evidence = self.root / 'evidence'
        self.evidence.mkdir()
        self.destination = self.root / 'restored'

    def fixture(self, entries, records=None):
        path = self.evidence / 'logs-test.tar.gz'
        with tarfile.open(path, 'w:gz') as tar:
            for name, kind, content in entries:
                info = tarfile.TarInfo(name)
                info.type = kind
                info.linkname = 'outside' if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE) else ''
                info.size = len(content) if kind == tarfile.REGTYPE else 0
                tar.addfile(info, io.BytesIO(content) if kind == tarfile.REGTYPE else None)
        if records is None:
            records = [{'path': name, 'bytes': len(content),
                        'sha256': hashlib.sha256(content).hexdigest(),
                        'archive': path.name}
                       for name, kind, content in entries if kind == tarfile.REGTYPE]
        item = {'name': path.name, 'bytes': path.stat().st_size,
                'sha256': archive.digest(path), 'files': len(records)}
        data = {'format_version': 1, 'files': records, 'archives': [item],
                'totals': {'files': len(records),
                           'uncompressed_bytes': sum(x['bytes'] for x in records),
                           'compressed_bytes': item['bytes']}}
        (self.evidence / 'manifest.json').write_text(json.dumps(data))
        (self.evidence / 'SHA256SUMS').write_text(f'{item["sha256"]}  {path.name}\n')
        return data

    def test_byte_roundtrip_and_existing_file_policy(self):
        raw = b'bytes\x00\xff\r\nunchanged\n'
        self.fixture([('logs/subdir/unusual.bin', tarfile.REGTYPE, raw)])
        archive.restore(self.evidence, self.destination, False)
        path = self.destination / 'logs/subdir/unusual.bin'
        self.assertEqual(path.read_bytes(), raw)
        archive.restore(self.evidence, self.destination, False)
        path.write_bytes(b'different')
        with self.assertRaises(ValueError):
            archive.restore(self.evidence, self.destination, False)
        self.assertEqual(path.read_bytes(), b'different')
        archive.restore(self.evidence, self.destination, True)
        self.assertEqual(path.read_bytes(), raw)

    def test_unsafe_paths(self):
        for name in ['/logs/a', 'logs/../outside', 'logs//a', 'other/a', 'logs/a/./b', 'logs\\a']:
            with self.subTest(name=name):
                self.fixture([(name, tarfile.REGTYPE, b'x')])
                with self.assertRaises(ValueError):
                    archive.restore(self.evidence, self.destination, False)
                self.assertFalse(self.destination.exists())

    def test_links_and_devices(self):
        for kind in [tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.FIFOTYPE, tarfile.DIRTYPE]:
            with self.subTest(kind=kind):
                self.fixture([('logs/a', kind, b'')], [
                    {'path': 'logs/a', 'bytes': 0, 'sha256': hashlib.sha256(b'').hexdigest(),
                     'archive': 'logs-test.tar.gz'}])
                with self.assertRaises(ValueError):
                    archive.restore(self.evidence, self.destination, False)

    def test_extra_duplicate_missing_members(self):
        original = [('logs/a', tarfile.REGTYPE, b'a')]
        record = self.fixture(original)['files']
        for entries in [original * 2, original + [('logs/b', tarfile.REGTYPE, b'b')], []]:
            with self.subTest(entries=entries):
                self.fixture(entries, record)
                with self.assertRaises(ValueError):
                    archive.restore(self.evidence, self.destination, False)

    def test_content_corruption_and_archive_corruption(self):
        data = self.fixture([('logs/a', tarfile.REGTYPE, b'a')])
        records = data['files']
        self.fixture([('logs/a', tarfile.REGTYPE, b'b')], records)
        with self.assertRaises(ValueError):
            archive.verify(self.evidence)
        self.fixture([('logs/a', tarfile.REGTYPE, b'a')])
        with (self.evidence / 'logs-test.tar.gz').open('ab') as stream:
            stream.write(b'corrupt')
        with self.assertRaises(ValueError):
            archive.verify(self.evidence)

    def test_file_directory_collision_and_extra_archive(self):
        self.fixture([('logs/a', tarfile.REGTYPE, b'a'), ('logs/a/b', tarfile.REGTYPE, b'b')])
        with self.assertRaises(ValueError):
            archive.restore(self.evidence, self.destination, False)
        self.fixture([('logs/a', tarfile.REGTYPE, b'a')])
        (self.evidence / 'logs-extra.tar.gz').write_bytes(b'extra')
        with self.assertRaises(ValueError):
            archive.verify(self.evidence)

    def test_symlink_destination_and_all_conflicts_preflight(self):
        self.fixture([('logs/a', tarfile.REGTYPE, b'a'), ('logs/b', tarfile.REGTYPE, b'b')])
        (self.destination / 'logs').mkdir(parents=True)
        (self.destination / 'logs/b').write_bytes(b'different')
        with self.assertRaises(ValueError):
            archive.restore(self.evidence, self.destination, False)
        self.assertFalse((self.destination / 'logs/a').exists())
        (self.destination / 'logs/b').unlink()
        (self.destination / 'logs/b').symlink_to(self.root / 'outside')
        with self.assertRaises(ValueError):
            archive.restore(self.evidence, self.destination, True)


if __name__ == '__main__':
    unittest.main()
