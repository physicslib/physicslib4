#!/usr/bin/env python3
"""Generate the website's icons: an "h6" tile in the teal accent, the "6" in the rose accent.

Writes `web/static_files/favicon.svg` (the drawing) and, rendered from it with `rsvg-convert`
(librsvg), `web/static_files/favicon.png` (64 x 64) and `web/static_files/apple-touch-icon.png`
(180 x 180). The colours are those of `Site.siteCss`: the tile is the accent `#0f766e`, the "h" is
white, and the "6" is the rose of the wordmark in its lighter shade, `#fb7185` (that of the dark
theme and of the teal footer), which stays legible on the tile at 16 pixels.

Usage, from the repository root: `python3 scripts/gen_favicon.py [SIX_COLOUR]`.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATIC = ROOT / "web" / "static_files"

TEAL = "#0f766e"
WHITE = "#ffffff"
SIX = "#fb7185"


def svg(six: str) -> str:
    """The tile, on a 180-unit square, as an SVG document."""
    return f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 180 180" width="180" height="180">
  <rect width="180" height="180" fill="{TEAL}"/>
  <text x="90" y="124" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-weight="700" font-size="104" letter-spacing="-2"><tspan fill="{WHITE}">h</tspan><tspan fill="{six}">6</tspan></text>
</svg>
"""


def main() -> None:
    six = sys.argv[1] if len(sys.argv) > 1 else SIX
    source = STATIC / "favicon.svg"
    source.write_text(svg(six), encoding="utf-8")
    for name, size in (("favicon.png", 64), ("apple-touch-icon.png", 180)):
        subprocess.run(["rsvg-convert", "-w", str(size), "-h", str(size), "-o", str(STATIC / name),
                        str(source)], check=True)


if __name__ == "__main__":
    main()
