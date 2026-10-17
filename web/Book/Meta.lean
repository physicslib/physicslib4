import VersoManual
import Site.Links

/-!
# Markup for the books

* `{apiDocs Name}[text]`: a link to the API documentation (doc-gen4) of the declaration `Name`,
  whose text is `text`, or `Name` in code type when `text` is empty. The name is resolved when the
  book is built, so a renamed or removed declaration is a build error.

```
{apiDocs Physicslib4.AQFT.HaagKastler.LocalNet}[]
```
-/

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Verso.Output Html
open Lean Elab

namespace Book

/-- The declaration named by `apiDocs`. -/
structure ApiDocsArgs where
  name : Name

instance : FromArgs ApiDocsArgs DocElabM where
  fromArgs := ApiDocsArgs.mk <$> .positional `name .resolvedName

/--
A link to the API documentation of a declaration of the library or of a dependency, at
`Site.apiDocsUrl` (the page of the module that declares it, anchored by its full name).
-/
@[role]
def apiDocs : RoleExpanderOf ApiDocsArgs
  | {name}, contents => do
    let env ← getEnv
    let some idx := env.getModuleIdxFor? name
      | throwError "'{name}' is not declared in an imported module, so it has no API docs page"
    let module := env.header.moduleNames[idx.toNat]!
    let url := Site.apiDocsUrl module.toString name.toString
    let text ←
      if contents.isEmpty then pure #[← ``(Inline.code $(quote name.toString))]
      else contents.mapM elabInline
    ``(Inline.link #[$text,*] $(quote url))

end Book
