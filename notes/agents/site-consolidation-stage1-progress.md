# Site consolidation, stage 1: feature-card links (2026-10-29)

Decision applied: each card links to the top of its reference-manual chapter.

## Changes

- `web/Site/Links.lean`: removed `sectionUrl` (blueprint guide pages, its only use was the cards);
  added `manualChapterUrl slug = "../manual/" ++ slug ++ "/"`, the one place that encodes where the
  website sits relative to the manual (stage 4 changes only this).
- `web/Site/Components.lean`: the six cards use `manualChapterUrl`. A card is a single `<a>`, so
  per-tag links would be nested anchors; the spectral card links to "Bounded spectral theory" and
  the §10.x tags stay plain spans (none link anywhere).
- `web/README.md`: "Served from a sub-path" mentions the card links and drops the guide pages.

## Verification

`lake build`, `generate-site`, `generate-manual` (fresh `_out/site`, `_out/manual`); chapter
directories match the expected slugs. Served `/tmp/srv/physicslib4/{site,manual}` on port 8765:

| Card | href | Status | Landing page title |
|---|---|---|---|
| Haag–Kastler axioms in Minkowski spacetime | ../manual/Haag-Kastler-axioms-in-Minkowski-spacetime/ | 200 | The Haag–Kastler axioms in Minkowski spacetime |
| The axioms in curved spacetime | ../manual/The-axioms-in-curved-spacetime-and-general-covariance/ | 200 | The axioms in curved spacetime and general covariance |
| The GNS construction | ../manual/The-GNS-construction/ | 200 | The GNS construction |
| Spectral theorems | ../manual/Bounded-spectral-theory/ | 200 | Bounded spectral theory |
| Stone's theorem | ../manual/Stones-theorem/ | 200 | Stone's theorem |
| Spacetime geometry | ../manual/Spacetime-and-geometry/ | 200 | Spacetime and geometry |

`python3 scripts/check_temporal_wording.py`: OK. Not committed.
