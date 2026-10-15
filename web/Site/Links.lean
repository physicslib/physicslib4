/-!
# Site-wide strings and links

The website and the tutorial are published side by side, at `/physicslib4/site/` and
`/physicslib4/tutorial/`. Every page of either carries a `<base href>` pointing at its own root, so
the relative paths below resolve to the same place from every page: `../tutorial/` from the
website, `../site/` from the tutorial.
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

/-- The tutorial, a separate book (`Tutorial/`), relative to the website root. -/
def tutorialPath : String := "../tutorial/"

/-- The reference manual, a page of the website, relative to the website root. -/
def manualPath : String := "manual/"

/-- The website root, relative to the tutorial root. -/
def siteFromTutorial : String := "../site/"

/--
The navigation links, in order, given the paths of the website and the tutorial roots relative to
the current root. Used by the header and the footer of the website and the tutorial.
-/
def navLinksFrom (siteRoot tutorialRoot : String) : Array (String × String) := #[
  ("Tutorial", tutorialRoot),
  ("Reference manual", siteRoot ++ manualPath),
  ("Blueprint", blueprintUrl),
  ("API docs", docsUrl)
]

/-- The navigation links of the website. -/
def navLinks : Array (String × String) := navLinksFrom "" tutorialPath

/-- The navigation links of the tutorial. -/
def tutorialNavLinks : Array (String × String) := navLinksFrom siteFromTutorial "./"

end Site
