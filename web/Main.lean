import VersoBlog
import Site

open Verso Genre Blog Site Syntax

/--
The physicslib4 site: the landing page, and stub pages for the tutorial and the reference manual.
The wordmark icons in `static_files/` are copied to the site root.
-/
def physicslib4Site : Verso.Genre.Blog.Site := site Site.FrontPage /
  static "apple-touch-icon.png" ← "static_files/apple-touch-icon.png"
  static "favicon.png" ← "static_files/favicon.png"
  "tutorial" Site.Tutorial
  "manual" Site.Manual

def main (args : List String) : IO UInt32 :=
  blogMain Site.theme physicslib4Site (options := args)
