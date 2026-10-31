import VersoBlog
import Site

open Verso Genre Blog Site Syntax

/--
The physicslib4 website: the landing page and the About, Roadmap and Get Involved pages. The tutorial and the reference manual are separate books
(`TutorialMain.lean`, `ManualMain.lean`).
The wordmark icons in `static_files/` are copied to the site root.
-/
def physicslib4Site : Verso.Genre.Blog.Site := site Site.FrontPage /
  "about" Site.About
  "roadmap" Site.Roadmap
  "get-involved" Site.GetInvolved
  static "apple-touch-icon.png" ← "static_files/apple-touch-icon.png"
  static "favicon.png" ← "static_files/favicon.png"

def main (args : List String) : IO UInt32 :=
  blogMain Site.theme physicslib4Site (options := args)
