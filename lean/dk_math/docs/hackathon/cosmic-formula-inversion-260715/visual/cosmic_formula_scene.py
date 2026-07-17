"""First coherent Manim prototype for the verified Cosmic Formula demo."""

from manim import (
    BLUE_B,
    BLUE_D,
    DOWN,
    FadeIn,
    FadeOut,
    GOLD,
    GREEN,
    GrowFromCenter,
    LEFT,
    ORIGIN,
    Rectangle,
    ReplacementTransform,
    RIGHT,
    Scene,
    Square,
    Text,
    UP,
    VGroup,
    WHITE,
    Write,
)

from demo_data import DEMO


BACKGROUND = "#0B1020"
KNOWN = BLUE_B
PRODUCT = "#67E8F9"
OFFSET = GOLD
BODY = BLUE_D
GAP = "#FB7185"
BOUNDARY = "#F8FAFC"
FRESH = "#A78BFA"
MUTED = "#94A3B8"


class CosmicFormulaPrototype(Scene):
    """One continuous schematic journey from finite primes to fresh factors."""

    def construct(self) -> None:
        self.camera.background_color = BACKGROUND

        title = Text("DkMath · Cosmic Formula Inversion", font_size=34, color=WHITE)
        title.to_edge(UP)
        subtitle = Text(
            "verified arithmetic · schematic geometry",
            font_size=20,
            color=MUTED,
        ).next_to(title, DOWN, buff=0.14)
        self.play(Write(title), FadeIn(subtitle), run_time=0.8)

        prime_tokens = VGroup(
            *[self.token(str(prime), KNOWN) for prime in DEMO.primes]
        ).arrange(RIGHT, buff=0.35)
        set_label = Text(
            f"S = {{{', '.join(map(str, DEMO.primes))}}}",
            font_size=34,
            color=KNOWN,
        ).next_to(prime_tokens, DOWN, buff=0.45)
        self.play(
            *[GrowFromCenter(token) for token in prime_tokens],
            Write(set_label),
            run_time=1.2,
        )
        self.wait(0.4)

        product_text = Text(
            f"P = {' × '.join(map(str, DEMO.primes))} = {DEMO.product}",
            font_size=38,
            color=PRODUCT,
        )
        self.play(
            ReplacementTransform(VGroup(prime_tokens, set_label), product_text),
            run_time=1.1,
        )
        offset_text = Text(
            f"u = {DEMO.offset}    gcd({DEMO.product}, {DEMO.offset}) = 1",
            font_size=30,
            color=OFFSET,
        ).next_to(product_text, DOWN, buff=0.4)
        self.play(Write(offset_text), run_time=0.8)
        self.wait(0.5)
        self.play(FadeOut(product_text), FadeOut(offset_text), run_time=0.5)

        geometry, body_group, gap_square, outer = self.completion_geometry()
        formula = Text(
            "Body + Gap = Big",
            font_size=34,
            color=WHITE,
        ).to_edge(LEFT).shift(UP * 1.5 + RIGHT * 0.45)
        body_formula = Text(
            f"Body = P(P + 2u) = {DEMO.body}",
            font_size=25,
            color=KNOWN,
        ).next_to(formula, DOWN, aligned_edge=LEFT, buff=0.35)
        gap_formula = Text(
            f"Gap = u² = {DEMO.gap}",
            font_size=25,
            color=GAP,
        ).next_to(body_formula, DOWN, aligned_edge=LEFT, buff=0.25)
        identity = Text(
            "P(P + 2u) + u² = (P + u)²",
            font_size=27,
            color=BOUNDARY,
        ).next_to(gap_formula, DOWN, aligned_edge=LEFT, buff=0.5)

        self.play(FadeIn(body_group), Write(formula), Write(body_formula), run_time=1.2)
        self.play(GrowFromCenter(gap_square), Write(gap_formula), run_time=0.9)
        self.play(FadeIn(outer), Write(identity), run_time=0.9)
        self.add(geometry)

        boundary_label = Text(
            f"completed boundary  P + u = {DEMO.boundary}",
            font_size=27,
            color=BOUNDARY,
        ).next_to(outer, DOWN, buff=0.28)
        numeric = Text(
            f"{DEMO.body} + {DEMO.gap} = {DEMO.big}",
            font_size=24,
            color=MUTED,
        ).next_to(boundary_label, DOWN, buff=0.18)
        self.play(Write(boundary_label), FadeIn(numeric), run_time=0.9)
        self.wait(0.7)

        factorization = Text(
            f"{DEMO.boundary} = {DEMO.fresh_factors[0]} × {DEMO.fresh_factors[1]}",
            font_size=46,
            color=FRESH,
        )
        self.play(
            FadeOut(VGroup(geometry, formula, body_formula, gap_formula, identity,
                           boundary_label, numeric)),
            FadeIn(factorization),
            run_time=0.8,
        )

        original = Text(
            f"S = {{{', '.join(map(str, DEMO.primes))}}}",
            font_size=32,
            color=KNOWN,
        ).next_to(factorization, UP, buff=0.65)
        fresh_tokens = VGroup(
            *[self.token(str(prime), FRESH) for prime in DEMO.fresh_factors]
        ).arrange(RIGHT, buff=0.75).next_to(factorization, DOWN, buff=0.6)
        freshness = Text(
            f"{DEMO.fresh_factors[0]}, {DEMO.fresh_factors[1]} ∉ S   ·   fresh prime factors",
            font_size=29,
            color=FRESH,
        ).next_to(fresh_tokens, DOWN, buff=0.38)
        theorem = Text(
            "prime q | (P + u)  and  gcd(P, u) = 1   ⇒   q ∉ S",
            font_size=22,
            color=MUTED,
        ).next_to(freshness, DOWN, buff=0.42)
        self.play(Write(original), GrowFromCenter(fresh_tokens), run_time=0.9)
        self.play(Write(freshness), FadeIn(theorem), run_time=0.9)
        self.wait(1.0)

        verified = Text(
            "Verified Lean anchors:\n"
            "demo_thirteen_fresh · demo_seventeen_fresh\n"
            "demo_cosmic_completion",
            font_size=25,
            line_spacing=1.25,
            color=GREEN,
        )
        self.play(
            FadeOut(VGroup(factorization, original, fresh_tokens, freshness, theorem)),
            FadeIn(verified),
            run_time=0.8,
        )
        self.wait(1.0)
        self.play(FadeOut(VGroup(title, subtitle, verified)), run_time=0.6)

    @staticmethod
    def token(label: str, color: str) -> VGroup:
        circle = Square(side_length=0.78, color=color, stroke_width=3)
        circle.set_fill(color, opacity=0.16)
        text = Text(label, font_size=30, color=WHITE).move_to(circle)
        return VGroup(circle, text)

    @staticmethod
    def completion_geometry() -> tuple[VGroup, VGroup, Square, Square]:
        center = RIGHT * 3.35 + DOWN * 0.2
        side = 4.15
        gap_side = 1.15

        left_body = Rectangle(
            width=side - gap_side,
            height=side,
            color=BODY,
            stroke_width=0,
            fill_opacity=0.82,
        ).move_to(center + LEFT * gap_side / 2)
        lower_body = Rectangle(
            width=gap_side,
            height=side - gap_side,
            color=BODY,
            stroke_width=0,
            fill_opacity=0.82,
        ).move_to(center + RIGHT * (side - gap_side) / 2 + DOWN * gap_side / 2)
        body_group = VGroup(left_body, lower_body)

        gap_square = Square(
            side_length=gap_side,
            color=GAP,
            stroke_width=3,
            fill_opacity=0.9,
        ).move_to(center + RIGHT * (side - gap_side) / 2 + UP * (side - gap_side) / 2)
        gap_square.set_fill(GAP, opacity=0.9)

        outer = Square(
            side_length=side,
            color=BOUNDARY,
            stroke_width=5,
        ).move_to(center)
        geometry = VGroup(body_group, gap_square, outer).move_to(center)
        return geometry, body_group, gap_square, outer
