/-!
# Site-wide strings and links

Paths inside the site are relative to the site root: every page carries `<base href>` pointing at the
root, so `tutorial/` resolves to the same place from every page.
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

/-- The tutorial (user guide), a page of this site. -/
def tutorialPath : String := "tutorial/"

/-- The reference manual, a page of this site. -/
def manualPath : String := "manual/"

/-- The navigation links, in order. Used by the header and the footer. -/
def navLinks : Array (String × String) := #[
  ("Tutorial", tutorialPath),
  ("Reference manual", manualPath),
  ("Blueprint", blueprintUrl),
  ("API docs", docsUrl)
]

end Site
