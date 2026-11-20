#!/usr/bin/env python3
"""Generate the line drawings of the website's landing page.

Writes `web/static_files/hero-wedge.svg`, the background of the hero; the eleven illustrations of
the feature cards, as standalone files in `web/static_files/cards/` and as Lean strings in
`web/Site/CardArt.lean`, which the page inlines. The output is deterministic: the same script writes
the same files.

Strokes and fills are `currentColor`. The hero background is a CSS mask over a block filled with a
theme colour (`Site.siteCss`), so only its opacities matter. The inline card drawings take the
accent colour from the card, and their groups of class `a1` (warm) and `a2` (cool) take the
colours `--card-accent-1` and `--card-accent-2`, defined for the light and dark themes in
`Site.siteCss`. In the drawings, `t` (time) points up and `x` (space) to the right.

Usage, from the repository root: `python3 scripts/gen_hero_background.py`.
"""

from __future__ import annotations

import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATIC = ROOT / "web" / "static_files"
CARDS = STATIC / "cards"


def num(v: float) -> str:
    """A coordinate with at most two decimals and no trailing zeros."""
    s = f"{v:.2f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def poly(points: list[tuple[float, float]], closed: bool = False) -> str:
    """Path data through `points`."""
    d = "M" + " L".join(f"{num(x)} {num(y)}" for x, y in points)
    return d + (" Z" if closed else "")


def path(d: str, *, w: float = 1.4, op: float = 1.0, fill: float = 0.0, dash: str = "",
         cap: str = "round") -> str:
    """A `<path>` element: stroke width `w`, stroke opacity `op`, fill opacity `fill`."""
    attrs = [f'd="{d}"', f'stroke-width="{num(w)}"', f'stroke-linecap="{cap}"',
             'stroke-linejoin="round"']
    attrs.append('stroke="currentColor"' if op > 0 else 'stroke="none"')
    if 0 < op < 1:
        attrs.append(f'stroke-opacity="{num(op)}"')
    if fill > 0:
        attrs.append(f'fill="currentColor" fill-opacity="{num(fill)}"')
    else:
        attrs.append('fill="none"')
    if dash:
        attrs.append(f'stroke-dasharray="{dash}"')
    return "<path " + " ".join(attrs) + "/>"


def circle(cx: float, cy: float, r: float, *, w: float = 1.4, op: float = 1.0,
           fill: float = 0.0, dash: str = "") -> str:
    d = (f"M{num(cx - r)} {num(cy)} a{num(r)} {num(r)} 0 1 0 {num(2 * r)} 0 "
         f"a{num(r)} {num(r)} 0 1 0 {num(-2 * r)} 0 Z")
    return path(d, w=w, op=op, fill=fill, dash=dash)


def dot(cx: float, cy: float, r: float = 2.2, op: float = 1.0) -> str:
    return path(f"M{num(cx - r)} {num(cy)} a{num(r)} {num(r)} 0 1 0 {num(2 * r)} 0 "
                f"a{num(r)} {num(r)} 0 1 0 {num(-2 * r)} 0 Z", op=0, fill=op)


def arrow(x1: float, y1: float, x2: float, y2: float, *, w: float = 1.4, op: float = 1.0,
          head: float = 6.0) -> str:
    """A straight arrow from `(x1, y1)` to `(x2, y2)`."""
    a = math.atan2(y2 - y1, x2 - x1)
    l = (x2 - head * math.cos(a - 0.45), y2 - head * math.sin(a - 0.45))
    r = (x2 - head * math.cos(a + 0.45), y2 - head * math.sin(a + 0.45))
    return path(poly([(x1, y1), (x2, y2)]) + " " + poly([l, (x2, y2), r]), w=w, op=op)


def g(cls: str, elems: list[str]) -> str:
    """A group of elements drawn in an accent colour: `a1` (warm) or `a2` (cool)."""
    return f'<g class="{cls}">' + "".join(elems) + "</g>"


def svg(width: int, height: int, body: list[str], title: str) -> str:
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
            f'width="{width}" height="{height}" role="img" aria-label="{title}">\n'
            f"<title>{title}</title>\n" + "\n".join(body) + "\n</svg>\n")


def hyperbola_space(cx: float, cy: float, c: float, side: int, tmax: float,
                    n: int = 64) -> list[tuple[float, float]]:
    """The branch `x = side * sqrt(c + t²)`, `|t| ≤ tmax`, of `x² − t² = c`, around `(cx, cy)`."""
    pts = []
    for i in range(n + 1):
        t = -tmax + 2 * tmax * i / n
        pts.append((cx + side * math.sqrt(c + t * t), cy - t))
    return pts


def hyperbola_time(cx: float, cy: float, c: float, side: int, xmax: float,
                   n: int = 64) -> list[tuple[float, float]]:
    """The branch `t = side * sqrt(c + x²)`, `|x| ≤ xmax`, of `t² − x² = c`, around `(cx, cy)`."""
    pts = []
    for i in range(n + 1):
        x = -xmax + 2 * xmax * i / n
        pts.append((cx + x, cy - side * math.sqrt(c + x * x)))
    return pts


# The hero background ---------------------------------------------------------------------------

def hero() -> str:
    """Boost orbits `x² − t² = c` in all four quadrants, with the light cone through the origin."""
    width, height = 1600, 900
    cx, cy = width / 2, height / 2
    reach = 1100.0
    body = [path(poly([(cx - reach, cy + reach), (cx + reach, cy - reach)]), w=1.1, op=0.8),
            path(poly([(cx - reach, cy - reach), (cx + reach, cy + reach)]), w=1.1, op=0.8)]
    for k in range(1, 15):
        a = 46.0 * k  # the orbit through x = a on the x-axis
        c = a * a
        op = 0.75 if k % 3 == 0 else 0.45
        for side in (1, -1):
            body.append(path(poly(hyperbola_space(cx, cy, c, side, reach, 96)), w=1.0, op=op))
            body.append(path(poly(hyperbola_time(cx, cy, c, side, reach, 96)), w=1.0, op=op))
    return svg(width, height, body, "Boost orbits and the light cone")


# The card illustrations (viewBox 240 × 140) ----------------------------------------------------

W, H = 240, 140


def card_gns() -> list[str]:
    """A vector Ω (warm) and its orbit π(a)Ω (cool) spanning a dense subspace."""
    ox, oy = 70, 100
    plane = [(30, 112), (190, 112), (225, 40), (65, 40)]
    body = [path(poly(plane, closed=True), w=1.0, op=0.5, fill=0.08)]
    vecs = [(150, 62), (182, 84), (118, 52), (100, 78), (160, 98), (200, 58), (132, 88)]
    body.append(g("a2", [arrow(ox, oy, x, y, w=0.9, op=0.6, head=4.5) for x, y in vecs]))
    body.append(path("M108 32 C 150 14, 215 22, 222 52", w=1.0, op=0.6, dash="3 4"))
    body.append(g("a1", [arrow(ox, oy, 140, 74, w=2.2, head=8), dot(ox, oy, 3.2)]))
    return body


def card_bounded() -> list[str]:
    """A bounded spectrum (warm) on a segment, with nested spectral projections (cool) above it."""
    y = 104
    body = [path(poly([(20, y), (220, y)]), w=1.0, op=0.5)]
    boxes = []
    for i, (a, b) in enumerate([(40, 202), (60, 150), (80, 128)]):
        top = 30 + 18 * i
        boxes.append(path(poly([(a, y - 14), (a, top), (b, top), (b, y - 14)]), w=1.1,
                          op=0.9 - 0.15 * i, fill=0.06))
    body.append(g("a2", boxes))
    spec = [path(poly([(a, y), (b, y)]), w=4.0) for a, b in [(46, 92), (118, 136), (160, 196)]]
    spec += [dot(108, y, 2.6), dot(148, y, 2.6)]
    body.append(g("a1", spec))
    body += [path(poly([(x, y - 6), (x, y + 6)]), w=1.4) for x in (46, 196)]
    return body


def card_unbounded() -> list[str]:
    """A spectrum (warm) spreading over the whole real line, off to ±∞ (cool)."""
    y = 82
    body = [arrow(120, y, 228, y, w=1.2, head=7), arrow(120, y, 12, y, w=1.2, head=7)]
    dots = []
    for k in range(-6, 7):
        x = 120 + math.copysign(1, k) * 15 * abs(k) ** 1.15 if k else 120
        dots.append(dot(x, y, 2.6, 1.0 if abs(k) < 5 else 0.6))
    body.append(g("a2", [
        path("M120 82 C 120 40, 196 36, 214 52", w=1.3, op=0.85, dash="4 4"),
        arrow(206, 47, 218, 56, w=1.3, op=0.85, head=6),
        path("M120 82 C 120 40, 44 36, 26 52", w=1.3, op=0.85, dash="4 4"),
        arrow(34, 47, 22, 56, w=1.3, op=0.85, head=6)]))
    body.append(g("a1", dots))
    return body


def card_stone() -> list[str]:
    """The unit circle, the point e^{itA} (cool) and its flow (warm)."""
    cx, cy, r = 120, 72, 48
    body = [path(poly([(cx - 70, cy), (cx + 70, cy)]), w=0.9, op=0.4),
            path(poly([(cx, cy + 62), (cx, cy - 62)]), w=0.9, op=0.4),
            circle(cx, cy, r, w=1.4, fill=0.05)]
    a0, a1 = math.radians(10), math.radians(115)
    pts = [(cx + (r + 10) * math.cos(a0 + (a1 - a0) * i / 40),
            cy - (r + 10) * math.sin(a0 + (a1 - a0) * i / 40)) for i in range(41)]
    body.append(g("a1", [path(poly(pts), w=1.8), arrow(*pts[-3], *pts[-1], w=1.8, head=7)]))
    a = math.radians(55)
    px, py = cx + r * math.cos(a), cy - r * math.sin(a)
    body.append(g("a2", [path(poly([(cx, cy), (px, py)]), w=1.6), dot(px, py, 3.4)]))
    body.append(dot(cx + r, cy, 2.6, 0.6))
    return body


def card_spacetime() -> list[str]:
    """A light cone (warm sheets) with a worldline (cool) through its vertex."""
    cx, cy = 120, 72
    cone = [path(poly([(cx - 58, cy - 58), (cx + 58, cy + 58)]), w=1.5),
            path(poly([(cx + 58, cy - 58), (cx - 58, cy + 58)]), w=1.5),
            path(f"M{cx - 58} {cy - 58} A58 11 0 0 0 {cx + 58} {cy - 58} "
                 f"A58 11 0 0 0 {cx - 58} {cy - 58} Z", w=1.2, fill=0.14),
            path(f"M{cx - 58} {cy + 58} A58 11 0 0 0 {cx + 58} {cy + 58}", w=1.2),
            path(f"M{cx - 58} {cy + 58} A58 11 0 0 1 {cx + 58} {cy + 58}", w=1.0, op=0.45,
                 dash="3 3")]
    return [arrow(cx, cy + 66, cx, cy - 68, w=0.9, op=0.45, head=5),
            g("a1", cone),
            g("a2", [path("M120 72 C 128 52, 112 34, 124 10", w=1.6)]),
            dot(cx, cy, 3)]


def diamond(cx: float, cy: float, r: float) -> list[tuple[float, float]]:
    return [(cx, cy - r), (cx + r, cy), (cx, cy + r), (cx - r, cy)]


def card_minkowski() -> list[str]:
    """Nested causal diamonds; the two small ones (warm, cool) are spacelike separated."""
    return [path(poly(diamond(120, 70, 60), closed=True), w=1.4, fill=0.06),
            g("a1", [path(poly(diamond(94, 74, 20), closed=True), w=1.5, fill=0.22)]),
            g("a2", [path(poly(diamond(148, 70, 18), closed=True), w=1.5, fill=0.22),
                     path(poly(diamond(150, 70, 9), closed=True), w=1.0, op=0.8, fill=0.3)]),
            path(poly([(94, 54), (114, 34)]), w=0.9, op=0.45, dash="3 3"),
            path(poly([(94, 54), (74, 34)]), w=0.9, op=0.45, dash="3 3"),
            path(poly([(148, 52), (166, 34)]), w=0.9, op=0.45, dash="3 3"),
            path(poly([(148, 52), (130, 34)]), w=0.9, op=0.45, dash="3 3")]


def card_curved() -> list[str]:
    """A curved coordinate grid with a tilted light cone (warm) at a point (cool)."""
    body = []

    def warp(u: float, v: float) -> tuple[float, float]:
        bump = 18 * math.exp(-((u - 120) ** 2 + (v - 70) ** 2) / 2600)
        return (u + 0.25 * bump * (u - 120) / 30, v + bump)

    for i in range(9):
        u = 24 + 24 * i
        body.append(path(poly([warp(u, 10 + 4 * k) for k in range(31)]), w=0.9, op=0.4))
    for j in range(6):
        v = 14 + 24 * j
        body.append(path(poly([warp(16 + 7 * k, v) for k in range(31)]), w=0.9, op=0.4))
    cx, cy = warp(120, 64)
    s, tilt = 30, 0.35
    ex, ey = math.cos(tilt), math.sin(tilt)
    tx, ty = -ey, -ex  # the tilted time direction (up)
    cone = []
    for sgn in (1, -1):
        cone.append(path(poly([(cx + s * (sgn * ex + tx), cy + s * (sgn * ey + ty)),
                               (cx - s * (sgn * ex + tx), cy - s * (sgn * ey + ty))]), w=1.7))
    for sgn in (1, -1):
        cone.append(path(poly([(cx + sgn * s * (ex + tx), cy + sgn * s * (ey + ty)),
                               (cx + sgn * s * (-ex + tx), cy + sgn * s * (-ey + ty)), (cx, cy)],
                              closed=True), w=0, op=0, fill=0.2))
    body.append(g("a1", cone))
    body.append(g("a2", [dot(cx, cy, 3.4)]))
    return body


def card_tomita() -> list[str]:
    """S = JΔ^{1/2}: a scaling Δ^{1/2} (cool) followed by a reflection J of a shape (warm)."""
    body = [path(poly([(120, 12), (120, 128)]), w=1.2, op=0.55, dash="5 4")]
    cx, cy = 66, 72
    scale = []
    for k in range(8):
        a = 2 * math.pi * k / 8 + math.pi / 8
        scale.append(arrow(cx + 9 * math.cos(a), cy + 9 * math.sin(a),
                           cx + 30 * math.cos(a), cy + 30 * math.sin(a), w=1.3, head=5))
    scale.append(dot(cx, cy, 2.8))
    body.append(g("a2", scale))
    body.append(circle(cx, cy, 34, w=1.0, op=0.4, dash="3 3"))
    tri = [(150, 52), (196, 64), (160, 98)]
    body.append(g("a1", [path(poly(tri, closed=True), w=1.5, fill=0.2)]))
    body.append(path(poly([(240 - x, y) for x, y in tri], closed=True), w=1.0, op=0.35,
                     dash="3 3"))
    body.append(path("M96 30 C 108 18, 132 18, 144 30", w=1.3))
    body.append(arrow(140, 26.5, 145, 31, w=1.3, head=6))
    return body


def card_borchers() -> list[str]:
    """The strip 0 ≤ Im z ≤ 1/2 (cool) and the dilations of the half-line (warm)."""
    y0, y1 = 100, 46
    body = [g("a2", [path(poly([(14, y0), (226, y0), (226, y1), (14, y1)], closed=True), w=0,
                          op=0, fill=0.14),
                     path(poly([(14, y1), (226, y1)]), w=1.4, dash="6 4")]),
            path(poly([(14, y0), (226, y0)]), w=1.4),
            path(poly([(120, 124), (120, 22)]), w=0.9, op=0.45)]
    dil = [path(poly([(x, y0 - 4), (x, y0 + 4)]), w=1.4, op=1.0 - 0.15 * k)
           for k, x in enumerate([132, 150, 178, 220])]
    dil += [path("M130 116 C 160 128, 196 126, 212 114", w=1.6),
            arrow(204, 119, 213, 113, w=1.6, head=6)]
    body.append(g("a1", dil))
    body.append(dot(120, y0, 3))
    return body


def card_reeh() -> list[str]:
    """A small diamond (warm) whose reach (cool arrows) fills the plane."""
    body = []
    for k, r in enumerate([82, 64, 48, 34]):
        body.append(path(poly(diamond(120, 70, r), closed=True), w=1.0, op=0.18 + 0.12 * k,
                         dash="4 4"))
    reach = []
    for a in (0, 90, 180, 270):
        ra = math.radians(a + 45)
        reach.append(arrow(120 + 22 * math.cos(ra), 70 + 22 * math.sin(ra),
                           120 + 46 * math.cos(ra), 70 + 46 * math.sin(ra), w=1.3, head=5))
    body.append(g("a2", reach))
    body.append(g("a1", [path(poly(diamond(120, 70, 16), closed=True), w=1.7, fill=0.3)]))
    return body


def card_bw() -> list[str]:
    """The right wedge x > |t| with its boost orbits (warm) and a boost (cool)."""
    cx, cy = 70, 70
    reach = 66
    body = [path(poly([(cx, cy), (cx + reach, cy - reach), (cx + 170, cy - reach),
                       (cx + 170, cy + reach), (cx + reach, cy + reach)], closed=True),
                 w=0, op=0, fill=0.08),
            path(poly([(cx - 50, cy + 50), (cx + reach, cy - reach)]), w=1.3),
            path(poly([(cx - 50, cy - 50), (cx + reach, cy + reach)]), w=1.3)]
    orbits = []
    for k in range(1, 6):
        a = 24.0 * k
        orbits.append(path(poly(hyperbola_space(cx, cy, a * a, 1, reach, 48)), w=1.3,
                           op=1.0 - 0.12 * k))
    body.append(g("a1", orbits))
    body.append(g("a2", [arrow(cx + 48, cy + 18, cx + 50, cy - 16, w=1.7, head=6)]))
    body.append(dot(cx, cy, 3))
    return body


CARD_DRAWINGS = {
    "gns": (card_gns, "A vector and its cyclic orbit"),
    "spectral-bounded": (card_bounded, "A bounded spectrum with spectral projections"),
    "spectral-unbounded": (card_unbounded, "A spectrum spreading over the real line"),
    "stone": (card_stone, "A one-parameter unitary group on the circle"),
    "spacetime": (card_spacetime, "A light cone"),
    "haag-kastler": (card_minkowski, "Nested causal diamonds"),
    "curved": (card_curved, "A curved spacetime with a light cone"),
    "tomita-takesaki": (card_tomita, "A scaling followed by a reflection"),
    "borchers": (card_borchers, "The strip and a dilation"),
    "reeh-schlieder": (card_reeh, "A small diamond whose reach fills the plane"),
    "bisognano-wichmann": (card_bw, "A wedge with its boost orbits"),
}


def card_svg(draw) -> str:
    """The inline markup of a card drawing: no size (the card sets it), hidden from screen readers
    (the card's title says what it shows)."""
    return (f'<svg class="feature-card-svg" xmlns="http://www.w3.org/2000/svg" '
            f'viewBox="0 0 {W} {H}" aria-hidden="true" focusable="false">'
            + "".join(draw()) + "</svg>")


def lean_module() -> str:
    """`web/Site/CardArt.lean`: the card drawings as Lean strings, for inlining in the page."""
    lines = [
        "/-!",
        "# Card illustrations",
        "",
        "The line drawings of the landing page's feature cards, inlined into the page by",
        "`Site.featureCardHtml`. This file is written by `scripts/gen_hero_background.py`; edit the",
        "script, not this file. Strokes and fills are `currentColor`; the groups of class `a1` and",
        "`a2` are the accent colours, set in `Site.siteCss`.",
        "-/",
        "",
        "namespace Site",
        "",
        "/-- The drawing of each card, by name, as inline SVG markup. -/",
        "def cardArt : List (String × String) := [",
    ]
    items = [f'  ("{name}", r#"{card_svg(draw)}"#)' for name, (draw, _) in CARD_DRAWINGS.items()]
    lines.append(",\n".join(items))
    lines += ["]", "", "end Site", ""]
    return "\n".join(lines)


def main() -> None:
    CARDS.mkdir(parents=True, exist_ok=True)
    (STATIC / "hero-wedge.svg").write_text(hero(), encoding="utf-8")
    for name, (draw, title) in CARD_DRAWINGS.items():
        (CARDS / f"{name}.svg").write_text(svg(W, H, draw(), title), encoding="utf-8")
    (ROOT / "web" / "Site" / "CardArt.lean").write_text(lean_module(), encoding="utf-8")
    print(f"wrote {(STATIC / 'hero-wedge.svg').relative_to(ROOT)}, {len(CARD_DRAWINGS)} card "
          f"drawings in {CARDS.relative_to(ROOT)} and web/Site/CardArt.lean")


if __name__ == "__main__":
    main()
