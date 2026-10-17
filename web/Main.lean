import VersoBlog
import Site

open Verso Genre Blog Site Syntax

/--
The physicslib4 website: the landing page. The tutorial and the reference manual are separate books
(`TutorialMain.lean`, `ManualMain.lean`).
The wordmark icons in `static_files/` are copied to the site root.
-/
def physicslib4Site : Verso.Genre.Blog.Site := site Site.FrontPage /
  static "apple-touch-icon.png" ← "static_files/apple-touch-icon.png"
  static "favicon.png" ← "static_files/favicon.png"

def main (args : List String) : IO UInt32 :=
  blogMain Site.theme physicslib4Site (options := args)
