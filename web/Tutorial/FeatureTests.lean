import VersoManual
import Tutorial.Meta
import Tutorial.Papers

open Verso.Genre Manual
open Tutorial

#doc (Manual) "Feature tests" =>

%%%
tag := "feature-tests"
draft := true
%%%

A draft-only chapter, built with `generate-tutorial --draft`. It shows each feature that the
chapters use, as an example of the markup.

# Mathematics

Inline: the algebra $`\mathfrak{U}(\mathbf{B})` of the diamond $`\mathbf{B} = I^+(p)\cap I^-(q)`.
Display:

$$`\omega(a) = \langle \Omega, \pi(a)\Omega\rangle, \qquad a \in \mathfrak{U}.`

# Exercises

:::::exercise
Show that the intersection of two causal diamonds, if it is not empty, contains a causal diamond.

::::solution
Pick a point $`x` in the intersection. Both diamonds are open, so a small diamond around $`x` lies
in each of them.
::::
:::::

# Figures

:::figure "diamond"
Two spacelike-separated diamonds $`\mathbf{B}_1` and $`\mathbf{B}_2` inside a diamond $`\mathbf{B}`.
:::

# Citations

Textual: {citet haagKastler1964}[]. Parenthetical: the locally covariant setting{citep brunettiFredenhagenVerch2003}[]. Inline reference: {citehere grossi2024}[].
