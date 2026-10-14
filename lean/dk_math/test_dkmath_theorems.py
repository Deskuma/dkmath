import importlib.util
from pathlib import Path
import sqlite3
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('dkmath_theorems.py')
spec = importlib.util.spec_from_file_location('dkmath_theorems', SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

class TestSourceFinder(unittest.TestCase):
    def test_nested_comments_do_not_become_theorems(self):
        code = 'namespace X\n/- theorem phantom : True := by trivial /- lemma ghost : True -/ -/\n' \
               'theorem real : True := by trivial\nend X\n'
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            f = root/'DkMath'/'T.lean'
            f.parent.mkdir()
            f.write_text(code)
            decs, imports, count, h = mod.scan(f, root)
            self.assertEqual([d[0] for d in decs], ['X.real'])

    def test_multi_namespace_and_end(self):
        code = 'namespace A\nsection B\nnamespace C\nlemma h : True := by trivial\nend C\nend B\n' \
               'theorem k : True := by trivial\nend A\n'
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); f = root/'DkMath'/'T.lean'
            f.parent.mkdir(); f.write_text(code)
            self.assertEqual([d[0] for d in mod.scan(f, root)[0]], ['A.C.h', 'A.k'])

if __name__ == '__main__': unittest.main()
