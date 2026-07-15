"""Shared verified values for the Cosmic Formula Manim prototype."""

from dataclasses import dataclass


@dataclass(frozen=True)
class CosmicDemoData:
    primes: tuple[int, ...] = (2, 3, 5, 7)
    offset: int = 11
    fresh_factors: tuple[int, int] = (13, 17)

    @property
    def product(self) -> int:
        result = 1
        for prime in self.primes:
            result *= prime
        return result

    @property
    def boundary(self) -> int:
        return self.product + self.offset

    @property
    def body(self) -> int:
        return self.product * (self.product + 2 * self.offset)

    @property
    def gap(self) -> int:
        return self.offset**2

    @property
    def big(self) -> int:
        return self.boundary**2


DEMO = CosmicDemoData()

# Keep accidental visual drift from reaching a render.
assert DEMO.product == 210
assert DEMO.boundary == 221
assert DEMO.fresh_factors[0] * DEMO.fresh_factors[1] == DEMO.boundary
assert DEMO.body == 48720
assert DEMO.gap == 121
assert DEMO.big == 48841
