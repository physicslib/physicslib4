import VersoManual
import Site.Diagram

/-!
# Directives for the tutorial

Block directives that the manual genre does not provide:

* `exercise`: an exercise, set off in a box with the label "Exercise".
* `solution`: a solution, collapsed by default (an HTML `<details>` element). It is usually written
  inside an `exercise`, after the statement.
* `figure "name"`: one of the project's diagrams (`diagrams` below), with the contents of the
  directive as its caption.
* `goals`: wraps a Lean block and shows the proof state after every tactic, without a click.

```
:::::exercise
Show that every causal diamond is open.

::::solution
It is the intersection of two open sets.
::::
:::::
```
-/

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Verso.Output Html
open Lean

namespace Tutorial

/-- The diagrams that `figure` can show, by name. -/
def diagrams : List (String × Html) := [
  ("diamond", Site.diamondDiagram),
  ("cones", Site.conesDiagram)
]

block_extension Block.exercise where
  traverse _ _ _ := pure none
  -- Long Lean messages (`#check` and `leanOutput` blocks) wrap instead of overflowing, as on the
  -- website (`Site/Theme.lean`). Every chapter has exercises, so the rule reaches every page.
  extraCss := [r##"
pre.hl.lean.lean-output { white-space: pre-wrap; overflow-wrap: anywhere; }
"##]
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml := some fun _ goB _ _ contents => do
    return {{
      <div class="exercise">
        <p class="exercise-label">"Exercise"</p>
        {{ ← contents.mapM goB }}
      </div>
    }}

block_extension Block.solution where
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml := some fun _ goB _ _ contents => do
    return {{
      <details class="solution">
        <summary>"Solution"</summary>
        <div class="solution-body">{{ ← contents.mapM goB }}</div>
      </details>
    }}

block_extension Block.figure (name : String) where
  data := .str name
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml := some fun _ goB _ data contents => do
    let .str name := data
      | Verso.reportError s!"Malformed figure data: {data}"; return .empty
    let some svg := diagrams.lookup name
      | Verso.reportError s!"Unknown diagram '{name}'"; return .empty
    return {{
      <figure class="tutorial-figure">
        {{ svg }}
        <figcaption>{{ ← contents.mapM goB }}</figcaption>
      </figure>
    }}

block_extension Block.goals where
  traverse _ _ _ := pure none
  -- A tactic nested in another, such as each rule of `rw [a, b]`, keeps its state hidden: the
  -- state after the enclosing tactic is shown instead. The state at `by` repeats the statement,
  -- so it is hidden too. These rules rely on Verso's markup for highlighted Lean: a tactic is a
  -- `span.tactic` holding a `label` (the tactic's text) and a `span.tactic-state`, and the `by`
  -- keyword carries `data-binding="kw-occ-Lean.Parser.Term.byTactic-…"`. If a Verso upgrade
  -- changes these, the redundant states reappear; check a `goals` block after upgrading.
  extraCss := [r##"
.goals .tactic .tactic,
.goals .tactic:has(> label > [data-binding^="kw-occ-Lean.Parser.Term.byTactic"]) {
  display: inline !important;
}
.goals .tactic .tactic > .tactic-state,
.goals .tactic:has(> label > [data-binding^="kw-occ-Lean.Parser.Term.byTactic"]) > .tactic-state {
  display: none !important;
}
.goals .tactic-state { margin: 0.25rem 0 0.5rem 0; max-width: 100%; overflow-x: auto; }
"##]
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml := some fun _ goB _ _ contents =>
    withReader (fun ρ => { ρ with codeOptions.visibleProofStates := .all }) do
      return {{ <div class="goals">{{ ← contents.mapM goB }}</div> }}

/-- An exercise. Its solution, if any, goes in a nested `solution` directive. -/
@[directive]
def exercise : DirectiveExpanderOf Unit
  | (), stxs => do
    let blocks ← stxs.mapM elabBlock
    ``(Block.other Block.exercise #[$blocks,*])

/-- A solution, collapsed until the reader opens it. -/
@[directive]
def solution : DirectiveExpanderOf Unit
  | (), stxs => do
    let blocks ← stxs.mapM elabBlock
    ``(Block.other Block.solution #[$blocks,*])

/--
Lean code whose proof states are all shown open: the goal after each tactic appears below it
without a click.
-/
@[directive]
def goals : DirectiveExpanderOf Unit
  | (), stxs => do
    let blocks ← stxs.mapM elabBlock
    ``(Block.other Block.goals #[$blocks,*])

/-- The name of the diagram shown by `figure`. -/
structure FigureArgs where
  name : String

instance : FromArgs FigureArgs DocElabM where
  fromArgs := FigureArgs.mk <$> .positional `name .string

/-- A figure showing one of the `diagrams`; the contents of the directive are its caption. -/
@[directive]
def figure : DirectiveExpanderOf FigureArgs
  | {name}, stxs => do
    unless diagrams.any (·.1 == name) do
      throwError "Unknown diagram '{name}'; known: {diagrams.map (·.1)}"
    let blocks ← stxs.mapM elabBlock
    ``(Block.other (Block.figure $(quote name)) #[$blocks,*])

end Tutorial
