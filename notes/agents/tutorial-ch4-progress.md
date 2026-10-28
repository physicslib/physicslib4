# Tutorial chapter 4 "Doing it yourself": progress log

Plan: `notes/agents/plan-verso-stage3-tutorial-ch4-2026-10-17.md`.

## Step 0: feasibility of the worked project

Option A is feasible, with API that exists, and is used. Prototype in `/tmp/ch4/A.lean`
(`import Physicslib4`), checked with `lake env lean`:

- every local element is a scalar: `Q.ι hB a = algebraMap ℂ Q.carrier a`, by
  `(AlgHomClass.commutes (Q.ι hB) a).symm` (the trivial net's local algebras are `ℂ` by definition);
- the range of `algebraMap ℂ Q.carrier` is closed: `Submodule.closed_of_finiteDimensional` applied to
  `LinearMap.range (Algebra.linearMap ℂ Q.carrier)`, then `LinearMap.coe_range`;
- every element of `Q.carrier` is a scalar: `IsClosed.closure_subset_iff` and `Q.dense_range`;
- `StarAlgHom.ofId ℂ Q.carrier` is bijective (injective via `FaithfulSMul.algebraMap_injective` /
  `(algebraMap ℂ _).injective` once `Nontrivial Q.carrier`, from `Q.ι_injective` and `1 ≠ 0` in `ℂ`);
- `(StarAlgEquiv.ofBijective _ h).symm.toStarAlgHom : Q.carrier →⋆ₐ[ℂ] ℂ`, then
  `identityState.comp` of it is a state on `trivialHaagKastlerNet.quasilocal.carrier`;
- uniqueness: every state `ω` agrees with it (`exists_scalar`, `Algebra.algebraMap_eq_smul_one`,
  `map_smul` on `ω.toContinuousLinearMap`, `State.apply_one`). `map_smul` directly on a
  `GNS.State` fails (no `MulActionHomClass` instance): a good type-class error for section 5.

No colimit lift was needed: density plus closedness of `ℂ·1` does it.

## Sections

- Section 1 "Setting up": 733 words (incl. 2 exercises), build OK. Chapter path: `Doing-it-yourself/`.
- Section 2 "How the project is organised": 538 words (1 exercise), build OK.
- Section 3 "From an idea to a statement": 685 words (2 exercises), build OK.
- Section 4 "Finding the API": 480 words (1 exercise), build OK. `exact?` output captured with leanOutput (matches).
- Section 5 "Proving it": 645 words (1 exercise), build OK. Error messages captured with leanOutput (type class: map_smul on GNS.State; universe: nonempty_haagKastlerNet at .{1}; coercion: rw [ω.apply_one] on toContinuousLinearMap).
- Section 6 "The worked project": 747 words (1 exercise), build OK. Option A carried out: trivial_ι_eq_algebraMap, isClosed_range_algebraMap, trivial_exists_scalar (goals), trivial_bijective (goals), trivialNetState, value check; uniqueness as exercise.
- Section 7 "Checking and contributing": 529 words (1 exercise), build OK. mk_all --check verified locally.
- Section 8 "Where to go next": ~340 words (1 exercise: invariance of trivialNetState), build OK.
- README.md and home_page/index.md Contributing shortened to point to https://physicslib.github.io/physicslib4/tutorial/Doing-it-yourself/ ; version statement kept in home page. check_temporal_wording.py OK.
- Final reread done; fixes: softened "library has no state" to "constructs none", search-tool caveat, `\leanok` wording, line wraps.
- Final: 4,884 words (wc of prose incl. exercises, excl. code), 10 exercises, tutorial builds (`lake build`, `generate-tutorial`), no root-relative URLs, check_temporal_wording OK.
- For a reviewer: build-time estimates for `lake build` are guesses; no `**Restriction:**` lines currently exist in the library (section 8 speaks of them generically); `web/README.md` layout list does not yet name `Tutorial/DoingItYourself.lean` (outside this task's allowed files); chapter uses `lake exe cache get` while README Getting Started uses `get!`.

## Review fixes (review-tutorial-ch4-2026-10-17.md)

- Applied all findings: 1.1 (commutes applied to ι, wording), 1.2 (failed to synthesize / stuck), 1.3 (checkdecls in section 7 solution), 1.4 (\leanfile is the project's macro), 2.1 (leanblueprint web, pdf, then checkdecls, with explanation), 2.2 (grep without "theorem"; first hit is the declaration), 2.3 (Graphviz), 2.4/3d (README `cache get`; no `get!` in home_page), 3a (build-time wording), 3b (Restriction template form in code, no Stone example; section 8 allows an empty search), 3c (web/README chapter 3 and 4 lines; dropped "(in preparation)" for chapter 1), 4.1 (two "As you will recall" varied), 4.2, 4.3, 4.4 (prose rewrapped to 100 columns), 5.1 (Lean lines within 60 columns).
- Not done: `.claude/CLAUDE.md:7` `get!` (the user edits that file).
- Build OK; check_temporal_wording OK.
