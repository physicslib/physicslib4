/-!
# Site-wide strings and links

The website, the tutorial and the reference manual are published side by side, at
`/physicslib4/site/`, `/physicslib4/tutorial/` and `/physicslib4/manual/`. Every page of each carries
a `<base href>` pointing at its own root, so the relative paths below resolve to the same place from
every page: `../tutorial/` and `../manual/` from the website, `../site/` from the books, and so on.
-/

namespace Site

/-- The tagline, shown under the wordmark and in the page metadata. -/
def tagline : String := "A Lean 4 formalisation of the mathematical foundations of physics"

/-- The project's GitHub repository. -/
def githubUrl : String := "https://github.com/physicslib/physicslib4"

/-- The published site that hosts the blueprint, the API docs and the blueprint guide pages. -/
def publishedRoot : String := "https://physicslib.github.io/physicslib4/"

/-- The blueprint. -/
def blueprintUrl : String := publishedRoot ++ "blueprint/"

/-- The API documentation. -/
def docsUrl : String := publishedRoot ++ "docs/"

/-- A blueprint guide page for one section of Chapter 10, e.g. `sectionUrl "sec10-1-gns"`. -/
def sectionUrl (page : String) : String := publishedRoot ++ page ++ ".html"

/--
The API documentation of the declaration `decl`, defined in the module `module`. doc-gen4 writes
one page per module, at the module's path, and anchors each declaration by its full name: for
example `Physicslib4.AQFT.HaagKastler.LocalNet`, in `Physicslib4.AQFT.HaagKastler.LocalAlgebras`, is
at `docs/Physicslib4/AQFT/HaagKastler/LocalAlgebras.html#Physicslib4.AQFT.HaagKastler.LocalNet`.
-/
def apiDocsUrl (module decl : String) : String :=
  docsUrl ++ "/".intercalate (module.splitOn ".") ++ ".html#" ++ decl

/-- The tutorial, a separate book (`Tutorial/`), relative to the root of the website or a book. -/
def tutorialPath : String := "../tutorial/"

/-- The reference manual, a separate book (`Manual/`), relative to the root of the website or a book. -/
def manualPath : String := "../manual/"

/-- The website root, relative to the root of a book. -/
def siteFromBook : String := "../site/"

/--
The navigation links, in order, given the paths of the roots of the tutorial and the reference
manual relative to the current root. Used by the header and the footer of the website and the
books.
-/
def navLinksFrom (tutorialRoot manualRoot : String) : Array (String × String) := #[
  ("Tutorial", tutorialRoot),
  ("Reference manual", manualRoot),
  ("Blueprint", blueprintUrl),
  ("API docs", docsUrl)
]

/-- The navigation links of the website. -/
def navLinks : Array (String × String) := navLinksFrom tutorialPath manualPath

/-- The navigation links of the tutorial. -/
def tutorialNavLinks : Array (String × String) := navLinksFrom "./" manualPath

/-- The navigation links of the reference manual. -/
def manualNavLinks : Array (String × String) := navLinksFrom tutorialPath "./"

end Site
