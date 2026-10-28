import VersoManual
import Tutorial
import Tutorial.Theme

open Verso.Genre Manual

/-!
The `generate-tutorial` executable: builds the tutorial book into `<output>/html-multi/`
(`--output <output>`, default `_out`). `--draft` also includes the draft-only chapters.
-/

def main := manualMain (%doc Tutorial) (config := Tutorial.config) (extraSteps := [Tutorial.replaceHeader])
