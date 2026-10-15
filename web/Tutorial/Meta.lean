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
