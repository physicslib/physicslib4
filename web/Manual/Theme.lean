import VersoManual
import Book.Theme

/-!
# Reference manual theme

The reference manual shares its look with the tutorial (`Book.Theme`): the website's design tokens,
stylesheet and header. This module supplies what is the manual's own: the meta description and the
header with "Reference manual" active.
-/

open Verso.Genre.Manual
open Verso.Output Html

namespace RefManual

/-- The header of every page of the manual: the website header, with "Reference manual" active. -/
def manualHeader : Html :=
  Site.headerWith Site.siteFromBook Site.manualNavLinks (· == "Reference manual")

/-- The HTML configuration of the reference manual (`Book.config`). -/
def config : RenderConfig :=
  Book.config "The reference manual of physicslib4, a Lean 4 formalisation of algebraic quantum field theory."

/-- An extra build step: puts `manualHeader` in place of the manual header on every HTML page. -/
def replaceHeader : ExtraStep := Book.replaceHeader manualHeader

end RefManual
