import VersoManual

/-!
# References

Works cited in the tutorial, for the manual genre's citation roles: `{citet haagKastler1964}[]`
gives "Haag and Kastler (1964)", `{citep …}[]` the parenthetical form, both with the full
reference as a margin note, and `{citehere …}[]` the full reference inline. The genre has no entry
type for books, so Haag's *Local Quantum Physics* is cited by hand (see "Further reading").
-/

open Verso.Genre.Manual

namespace Tutorial

/-- R. Haag and D. Kastler, "An algebraic approach to quantum field theory" (1964). -/
def haagKastler1964 : Article where
  title := inlines!"An algebraic approach to quantum field theory"
  authors := #[inlines!"Rudolf Haag", inlines!"Daniel Kastler"]
  journal := inlines!"Journal of Mathematical Physics"
  year := 1964
  month := none
  volume := inlines!"5"
  number := inlines!"7"
  pages := some (848, 861)
  url := some "https://doi.org/10.1063/1.1704187"

/-- R. Brunetti, K. Fredenhagen and R. Verch, "The generally covariant locality principle" (2003). -/
def brunettiFredenhagenVerch2003 : Article where
  title := inlines!"The generally covariant locality principle: a new paradigm for local quantum field theory"
  authors := #[inlines!"Romeo Brunetti", inlines!"Klaus Fredenhagen", inlines!"Rainer Verch"]
  journal := inlines!"Communications in Mathematical Physics"
  year := 2003
  month := none
  volume := inlines!"237"
  number := inlines!"1–2"
  pages := some (31, 68)
  url := some "https://doi.org/10.1007/s00220-003-0815-7"

/-- R. Grossi, "Entanglement in algebraic quantum field theories" (2024), arXiv:2410.16599. -/
def grossi2024 : ArXiv where
  title := inlines!"Entanglement in Algebraic Quantum Field Theories"
  authors := #[inlines!"Rafael Grossi"]
  year := 2024
  id := "2410.16599"

end Tutorial
