import VersoManual
import Book.Theme

/-!
# Tutorial theme

The tutorial shares its look with the reference manual (`Book.Theme`): the website's design tokens,
stylesheet and header. This module supplies what is the tutorial's own: the meta description and
the header with "Tutorial" active.
-/

open Verso.Genre.Manual
open Verso.Output Html

namespace Tutorial

/-- The header of every tutorial page: the website header, with "Tutorial" active. -/
def tutorialHeader : Html :=
  Site.headerWith Site.siteFromBook Site.tutorialNavLinks (· == "Tutorial")

/-- The HTML configuration of the tutorial (`Book.config`). -/
def config : RenderConfig :=
  Book.config "A tutorial on algebraic quantum field theory and its formalisation in Lean 4 in physicslib4."

/-- An extra build step: puts `tutorialHeader` in place of the manual header on every HTML page. -/
def replaceHeader : ExtraStep := Book.replaceHeader tutorialHeader

end Tutorial
