/-!
# Site-wide strings and links

The website is published at the root of the project site, `/physicslib4/`, with the tutorial and
the reference manual beneath it, at `/physicslib4/tutorial/` and `/physicslib4/manual/`. Every page
of each carries a `<base href>` pointing at its own root, so the relative paths below resolve to the
same place from every page: `tutorial/`, `manual/` and `about/` from the website, `../` (the website),
`../about/` and `../tutorial/` or `../manual/` (the other book) from the books.
-/

namespace Site

/-- The tagline, shown under the wordmark and in the page metadata. -/
def tagline : String := "Solving Hilbert's 6th problem in Lean 4"

/-- The project's GitHub repository. -/
def githubUrl : String := "https://github.com/physicslib/physicslib4"

/-- The published site that hosts the blueprint and the API docs. -/
def publishedRoot : String := "https://physicslib.github.io/physicslib4/"

/-- The blueprint. -/
def blueprintUrl : String := publishedRoot ++ "blueprint/"

/-- The API documentation. -/
def docsUrl : String := publishedRoot ++ "docs/"


/--
The API documentation of the declaration `decl`, defined in the module `module`. doc-gen4 writes
one page per module, at the module's path, and anchors each declaration by its full name: for
example `Physicslib4.AQFT.HaagKastler.LocalNet`, in `Physicslib4.AQFT.HaagKastler.LocalAlgebras`, is
at `docs/Physicslib4/AQFT/HaagKastler/LocalAlgebras.html#Physicslib4.AQFT.HaagKastler.LocalNet`.
-/
def apiDocsUrl (module decl : String) : String :=
  docsUrl ++ "/".intercalate (module.splitOn ".") ++ ".html#" ++ decl

/-- The tutorial, a separate book (`Tutorial/`), relative to the root of the website. -/
def tutorialPath : String := "tutorial/"

/-- The reference manual, a separate book (`Manual/`), relative to the root of the website. -/
def manualPath : String := "manual/"

/-- The tutorial, relative to the root of a book. -/
def tutorialFromBook : String := "../tutorial/"

/-- The reference manual, relative to the root of a book. -/
def manualFromBook : String := "../manual/"

/--
The top of a reference-manual chapter, relative to the root of the website, given the chapter's
page name, e.g. `manualChapterUrl "The-GNS-construction"`. The website is served at
`/physicslib4/` and the manual at `/physicslib4/manual/`. The feature cards use this function; the
caption links of the code gallery in `Site/FrontPage.lean` are plain text in the page's markup and
write the same `manual/` prefix directly.
-/
def manualChapterUrl (slug : String) : String := manualPath ++ slug ++ "/"

/-- The website root, relative to the root of a book. -/
def siteFromBook : String := "../"

/-- The About page, relative to the root of the website. -/
def aboutPath : String := "about/"

/-- The Roadmap page, relative to the root of the website. -/
def roadmapPath : String := "roadmap/"

/-- The Get Involved page, relative to the root of the website. -/
def getInvolvedPath : String := "get-involved/"

/-- The documentation links of the footer, given the roots of the tutorial and the reference manual. -/
def docLinksFrom (tutorialRoot manualRoot : String) : Array (String × String) := #[
  ("Tutorial", tutorialRoot),
  ("Reference manual", manualRoot),
  ("Blueprint", blueprintUrl),
  ("API docs", docsUrl)
]

/--
The navigation links, in order, given the path of the website's root and the paths of the roots of
the tutorial and the reference manual, all relative to the current root. Used by the header of the
website and the books.
-/
def navLinksFrom (siteRoot tutorialRoot manualRoot : String) : Array (String × String) := #[
  ("About", siteRoot ++ aboutPath),
  ("Tutorial", tutorialRoot),
  ("Roadmap", siteRoot ++ roadmapPath),
  ("Get involved", siteRoot ++ getInvolvedPath),
  ("Reference manual", manualRoot),
  ("Blueprint", blueprintUrl),
  ("API docs", docsUrl)
]

/-- The navigation links of the website. -/
def navLinks : Array (String × String) := navLinksFrom "" tutorialPath manualPath

/-- The navigation links of the tutorial. -/
def tutorialNavLinks : Array (String × String) := navLinksFrom siteFromBook "./" manualFromBook

/-- The navigation links of the reference manual. -/
def manualNavLinks : Array (String × String) := navLinksFrom siteFromBook tutorialFromBook "./"

end Site
