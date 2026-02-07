import os
import sys
import math
import cmath

import pytest

# ensure package folder is importable
HERE = os.path.dirname(__file__)
ROOT = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, ROOT)

from CosmicComplex import CosmicComplex


def approx_complex(a: complex, b: complex, rel=1e-9, abs_tol=1e-12):
    return abs(a - b) <= max(rel * max(abs(a), abs(b)), abs_tol)


def test_G_equals_sum_terms():
    cc = CosmicComplex(d=8, x=4.0, mode="even")
    for theta in (0.0, 0.5, 3.0, -1.2):
        obs = cc.observe(theta)
        S = sum(obs.terms)
        assert approx_complex(obs.G, S)


def test_partial_sums_end_equals_G():
    cc = CosmicComplex(d=8, x=4.0, mode="even")
    obs = cc.observe(1.3)
    assert obs.partial_sums
    assert approx_complex(obs.partial_sums[-1], obs.G)


def test_dominant_k_and_entropy():
    cc = CosmicComplex(d=8, x=4.0, mode="even")
    obs = cc.observe(2.0)
    assert 0 <= obs.dominant_k <= cc.params.d
    assert obs.entropy >= 0.0


def test_dyadic_validation():
    # mode='dyadic' should reject non-power-of-two d
    with pytest.raises(ValueError):
        CosmicComplex(d=6, x=1.0, mode="dyadic")


def test_edge_cases_zero():
    # x=0 and theta=0 => G == 0
    cc = CosmicComplex(d=4, x=0.0, mode="any")
    obs = cc.observe(0.0)
    assert approx_complex(obs.G, 0 + 0j)
    assert approx_complex(sum(obs.terms), 0 + 0j)
