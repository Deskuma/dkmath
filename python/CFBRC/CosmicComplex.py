#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.

cid: 6986ab45-8ed4-83a4-b4b7-bafb7db2e5dc

CosmicComplex (CC) — initial template (雛形)

目的:
- G(θ) を「値」ではなく「項・寄与率・部分和・位相」の観測ログとして扱う
- 演算(操作)をモノイドとして合成し、演算前後の Motion(差分) を観測する

最初は d=8 など偶数、運用は dyadic (d=2^n) 推奨。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, List, Optional, Sequence, Tuple
import math
import cmath

# -------------------------
# Utilities
# -------------------------


def comb(n: int, k: int) -> int:
    return math.comb(n, k)


def unwrap(phases: Sequence[float]) -> List[float]:
    """Simple phase unwrap (radians)."""
    if not phases:
        return []
    out = [phases[0]]
    twopi = 2.0 * math.pi
    for p in phases[1:]:
        prev = out[-1]
        dp = p - prev
        # wrap to (-pi, pi]
        dp = (dp + math.pi) % twopi - math.pi
        out.append(prev + dp)
    return out


def safe_log(x: float, eps: float = 1e-300) -> float:
    return math.log(max(x, eps))


# -------------------------
# Data models
# -------------------------


@dataclass(frozen=True)
class CCParams:
    d: int
    x: float = 1.0
    # 拡張: u, window, normalization mode, cutoffs, etc.
    # u: float = 0.0


@dataclass
class Observation:
    theta: float
    params: CCParams

    G: complex = 0j
    terms: List[complex] = field(default_factory=list)  # T_k(θ) list
    abs_terms: List[float] = field(default_factory=list)  # |T_k|
    contrib: List[float] = field(default_factory=list)  # |T_k| / Σ|T_j|
    dominant_k: int = 0  # argmax |T_k|

    partial_sums: List[complex] = field(default_factory=list)  # S_m = Σ_{k≤m} T_k
    arg: float = 0.0  # arg(G)
    entropy: float = 0.0  # -Σ p log p


@dataclass
class Delta:
    dG: complex = 0j
    darg: float = 0.0
    dominant_move: Tuple[int, int] = (0, 0)
    d_entropy: float = 0.0
    d_contrib: List[float] = field(default_factory=list)


@dataclass
class Motion:
    before: Observation
    after: Observation
    delta: Delta


# -------------------------
# Monoid operations (Ops)
# -------------------------


class Op:
    """
    演算モノイド要素:
    - apply_params: params を変える
    - map_theta: theta を変える（パラメータと独立）
    - postprocess_obs: 観測結果を加工（レンズ）
    """

    name: str = "Op"

    def apply_params(self, p: CCParams) -> CCParams:
        return p

    def map_theta(self, theta: float) -> float:
        return theta

    def postprocess_obs(self, obs: Observation) -> Observation:
        return obs

    def then(self, other: "Op") -> "OpChain":
        return OpChain([self, other])


class IdOp(Op):
    name = "Id"


class OpChain(Op):
    name = "OpChain"

    def __init__(self, ops: Sequence[Op]):
        self.ops = list(ops)

    def apply_params(self, p: CCParams) -> CCParams:
        for op in self.ops:
            p = op.apply_params(p)
        return p

    def map_theta(self, theta: float) -> float:
        for op in self.ops:
            theta = op.map_theta(theta)
        return theta

    def postprocess_obs(self, obs: Observation) -> Observation:
        for op in self.ops:
            obs = op.postprocess_obs(obs)
        return obs

    def then(self, other: Op) -> "OpChain":
        return OpChain(
            self.ops + ([other] if not isinstance(other, OpChain) else other.ops)
        )


# --- Example Ops ---


class ScaleX(Op):
    name = "ScaleX"

    def __init__(self, a: float):
        self.a = float(a)

    def apply_params(self, p: CCParams) -> CCParams:
        return CCParams(d=p.d, x=p.x * self.a)


class ChangeD(Op):
    name = "ChangeD"

    def __init__(self, d: int):
        self.d = int(d)

    def apply_params(self, p: CCParams) -> CCParams:
        return CCParams(d=self.d, x=p.x)


class ShiftTheta(Op):
    name = "ShiftTheta"

    def __init__(self, t0: float):
        self.t0 = float(t0)

    def map_theta(self, theta: float) -> float:
        return theta + self.t0


class FlipTheta(Op):
    name = "FlipTheta"

    def map_theta(self, theta: float) -> float:
        return -theta


# 例: terms を寄与率順に並べ替えたい等は postprocess_obs でやる
# class ReorderTerms(Op): ...

# -------------------------
# Core: CosmicComplex
# -------------------------


class CosmicComplex:
    """
    CC = CosmicComplex (double-C): 複素化の因数(項)構造を観測するツール

    mode:
      - "any": 制限なし
      - "even": d 偶数のみ
      - "dyadic": d = 2^n のみ（運用推奨）
    """

    def __init__(self, d: int, x: float = 1.0, mode: str = "dyadic"):
        self.mode = mode
        self.params = CCParams(d=int(d), x=float(x))
        self._validate_d(self.params.d)

    # ---- validation ----
    def _validate_d(self, d: int) -> None:
        if d <= 0:
            raise ValueError("d must be positive.")
        if self.mode == "even":
            if d % 2 != 0:
                raise ValueError("mode='even' requires even d.")
        elif self.mode == "dyadic":
            if d & (d - 1) != 0:  # power of two check
                raise ValueError("mode='dyadic' requires d = 2^n.")
        elif self.mode == "any":
            pass
        else:
            raise ValueError(f"unknown mode: {self.mode}")

    # ---- term definition ----
    def term(self, k: int, theta: float, p: Optional[CCParams] = None) -> complex:
        """
        T_k(θ) = C(d,k) * x^(d-k) * (iθ)^k
        """
        if p is None:
            p = self.params
        d, x = p.d, p.x
        return comb(d, k) * (x ** (d - k)) * ((1j * theta) ** k)

    def terms(self, theta: float, p: Optional[CCParams] = None) -> List[complex]:
        if p is None:
            p = self.params
        return [self.term(k, theta, p) for k in range(p.d + 1)]

    def G(self, theta: float, p: Optional[CCParams] = None) -> complex:
        """
        Default: G(θ) = (x + iθ)^d
        NOTE: ここを差し替えるだけで、(x+iθ)^d - (iθ)^d などにもできる。
        """
        if p is None:
            p = self.params
        # (x + iθ)^d をそのまま使う（高速）
        return (p.x + 1j * theta) ** p.d

    # ---- observation ----
    def observe(self, theta: float, op: Optional[Op] = None) -> Observation:
        """
        1点観測。op があれば (params, theta, obs) に作用させた結果を返す。
        """
        op = op or IdOp()

        # apply op to params and theta
        p2 = op.apply_params(self.params)
        self._validate_d(p2.d)
        th2 = op.map_theta(float(theta))

        # compute terms and G
        ts = self.terms(th2, p2)
        Gv = self.G(th2, p2)

        abs_ts = [abs(z) for z in ts]
        # use fsum for better numeric stability; guard against zero total
        sabs = math.fsum(abs_ts) or 1e-300
        contrib = [a / sabs for a in abs_ts]
        dominant_k = max(range(len(abs_ts)), key=lambda k: abs_ts[k], default=0)

        # partial sums polygon
        ps: List[complex] = []
        acc = 0j
        for z in ts:
            acc += z
            ps.append(acc)

        # phase + entropy
        arg = cmath.phase(Gv)
        # use fsum for more accurate summation in entropy
        H = -math.fsum(pk * safe_log(pk) for pk in contrib)

        obs = Observation(
            theta=th2,
            params=p2,
            G=Gv,
            terms=ts,
            abs_terms=abs_ts,
            contrib=contrib,
            dominant_k=dominant_k,
            partial_sums=ps,
            arg=arg,
            entropy=H,
        )

        # postprocess lens
        obs = op.postprocess_obs(obs)
        return obs

    # ---- motion (before/after) ----
    def motion(self, theta: float, op: Op) -> Motion:
        """
        演算前後の動き = Motion を返す。
        before: Id
        after : op
        """
        before = self.observe(theta, IdOp())
        after = self.observe(theta, op)

        dG = after.G - before.G

        # unwrap-aware darg (single point: choose minimal wrapped difference)
        darg = after.arg - before.arg
        darg = (darg + math.pi) % (2.0 * math.pi) - math.pi

        d_contrib = []
        n = min(len(before.contrib), len(after.contrib))
        for i in range(n):
            d_contrib.append(after.contrib[i] - before.contrib[i])

        delta = Delta(
            dG=dG,
            darg=darg,
            dominant_move=(before.dominant_k, after.dominant_k),
            d_entropy=(after.entropy - before.entropy),
            d_contrib=d_contrib,
        )
        return Motion(before=before, after=after, delta=delta)

    # ---- batch helpers ----
    def observe_grid(
        self, thetas: Iterable[float], op: Optional[Op] = None
    ) -> List[Observation]:
        return [self.observe(th, op=op) for th in thetas]

    def dominant_trace(
        self, thetas: Iterable[float], op: Optional[Op] = None
    ) -> List[int]:
        return [self.observe(th, op=op).dominant_k for th in thetas]

    def entropy_trace(
        self, thetas: Iterable[float], op: Optional[Op] = None
    ) -> List[float]:
        return [self.observe(th, op=op).entropy for th in thetas]


# -------------------------
# Example usage (minimal)
# -------------------------

if __name__ == "__main__":
    cc = CosmicComplex(d=8, x=4.0, mode="even")  # or mode="dyadic"

    # single observation
    obs0 = cc.observe(theta=3.0)
    print("G:", obs0.G)
    print("dominant_k:", obs0.dominant_k)
    print("entropy:", obs0.entropy)

    # motion: flip theta + scale x
    op = FlipTheta().then(ScaleX(1.25))
    mot = cc.motion(theta=3.0, op=op)
    print("ΔG:", mot.delta.dG)
    print("Δarg:", mot.delta.darg)
    print("dominant move:", mot.delta.dominant_move)
    print("Δentropy:", mot.delta.d_entropy)
