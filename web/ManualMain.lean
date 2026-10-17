import VersoManual
import Manual
import Manual.Theme

open Verso.Genre Manual

/-!
The `generate-manual` executable: builds the reference manual into `<output>/html-multi/`
(`--output <output>`, default `_out`). `--draft` also includes the draft-only chapters.
-/

def main := manualMain (%doc Manual) (config := RefManual.config) (extraSteps := [RefManual.replaceHeader])
