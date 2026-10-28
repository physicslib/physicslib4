import VersoManual
import Manual.GNS
import Manual.Spectral
import Manual.Unbounded
import Manual.Stone
import Manual.Spacetime
import Manual.HaagKastler
import Manual.Curved
import Manual.Conventions
import Manual.NotProved
import Manual.FeatureTests

open Verso.Genre Manual

#doc (Manual) "physicslib4 reference manual" =>

This manual describes how physicslib4 encodes the mathematics of algebraic quantum field theory:
which definitions the library makes, why they take the form they do, which theorems it proves, and
where they live. It has one chapter per section of Chapter 10 of the blueprint. The
[tutorial](../tutorial/) introduces the subject; the
[API documentation](https://physicslib.github.io/physicslib4/docs/) lists every declaration.
The library's conventions and design decisions are stated once, in the chapter
{ref "conventions"}[Conventions and design decisions], and the standard facts it does not prove
are listed in the {ref "not-proved"}[appendix].

{include 1 Manual.GNS}

{include 1 Manual.Spectral}

{include 1 Manual.Unbounded}

{include 1 Manual.Stone}

{include 1 Manual.Spacetime}

{include 1 Manual.HaagKastler}

{include 1 Manual.Curved}

{include 1 Manual.Conventions}

{include 1 Manual.NotProved}

{include 1 Manual.FeatureTests}
