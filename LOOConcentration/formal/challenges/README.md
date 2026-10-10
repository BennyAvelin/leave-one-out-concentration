# Manuscript theorem challenges

These four exercises copy the exact author-approved Lean theorem headers, in manuscript order:

| Manuscript result | Lean name | Source label |
| --- | --- | --- |
| Theorem 1: Lipschitz case | `simplifiedConcentration` | `thm:simplified` |
| Theorem 2: general concentration | `mainConcentration` | `thm:main` |
| Corollary 1: centered Lp bound | `looMoments` | `cor:loo-moments` |
| Theorem 3: data-dependent concentration | `dataDependentConcentration` | `thm:data-dependent` |

Numbering is from the pinned author-approved manuscript SHA-256 `4d83a9d8a5eaaebd46dcf7af522cab5030aa88c20a68e2043260cfa319830804`. This package targets the manuscript interfaces in `LOOConcentration.Revision`. The OLS application has no exercise here.

`Challenge.lean` contains four intentional `by sorry` exercise bodies in namespace `LOOConcentration.Revision.Challenges`. These are the only authorized proof holes and are outside the production library. It imports the definitions and prerequisites needed to state the results; its 29-module project import closure excludes all frozen result modules and result providers. The formal statements use the same standing assumption, variational log-Sobolev constant, gradient conventions and endpoint conditions as the frozen exports.

`Solution.lean` has the byte-identical four headers and uses the existing proved provider assemblies. It is a reference solution, not an independent proof development. It imports those proof providers separately from the challenge. `ComparatorSupport.lean` compares elaborated types against the actual frozen exports and checks solution axioms; it is compiled only in temporary audit harnesses.

After installing the pinned toolchain and fetching dependency caches, run from `LOOConcentration/formal`:

```sh
python3 challenges/generate.py
python3 challenges/compare.py
python3 challenges/test_comparator.py
```

The whole-release `python3 scripts/ci.py` also runs these three commands. The generator checks exact frozen headers, templates, source/dependency pins and import isolation. The comparator checks exactly four challenge holes, exact elaborated types for all four exercises and reference solutions, and standard-only solution axioms (`propext`, `Classical.choice`, `Quot.sound`). Regression checks reject extra premises, changed conclusions, proof holes in solutions, custom axioms, unauthorized imports and stale bindings; separate Lean checks reject type drift and forbidden axioms even for fixtures that independently elaborate.

## Submit another solution

Copy either `Challenge.lean` or `Solution.lean` to `MySolution.lean` and fill or replace its four proof bodies. Keep the chosen imports, preamble, namespace, exact headers, declaration order and footer unchanged. Put auxiliary facts inside the proofs; extra top-level declarations/imports are outside this proof-only format.

```sh
python3 challenges/compare.py --solution MySolution.lean
```

The challenge preamble gives the prerequisite-only exercise surface. The reference preamble also imports existing result providers and is accepted for checking reference-style submissions. This is a project-specific local comparator, not a Mathlib-only registry challenge or a sandbox for untrusted code.

`manifest.json` binds the exact approved result sources, header hashes, prerequisite and solution import closures, dependency configuration, templates, support checker, and four explicit exercise-hole exceptions. Reports are written to `challenges/reports/latest/` and `challenges/reports/regressions/`, and are excluded from version control. No upstream dependencies are compiled by these checkers.
