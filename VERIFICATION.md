# Verification and manuscript correspondence

The formalization targets the author-approved manuscript with SHA-256
`4d83a9d8a5eaaebd46dcf7af522cab5030aa88c20a68e2043260cfa319830804`.
The manuscript is excluded from this distribution. The older published preprint
was never formalized. The [arXiv record](https://arxiv.org/abs/2211.02478)
identifies the paper; it may serve different source text. The declarations do
not automatically certify other versions.

## Scope and correspondence

The production library consists of exactly 560 modules in the project import closure of the four entry points documented in the [README](README.md). This includes the core interfaces, estimator proofs, supplementary uniform-deletion result, and four model-selection exports. There are no authorized production proof holes or custom axioms. The separate theorem challenge template has four intentional exercise holes.

The release retains 149 modules in `LOOConcentration/` solely as required proof dependencies. These include the OLS theorem and its data-dependent concentration dependency. Modules from earlier development are retained only where required by the manuscript interfaces and extensions. Required dependency declarations preserve their exact previously frozen statements.

Three contextual source rulings remain pending: the AMS literature comparison, sphere/equatorial-neighborhood and qualified perturbation wording, and the concentration-tool consumption sentence. Whole-manuscript correspondence is therefore not certified. Simulation material and the bounded-data/no-LSI remark remain excluded; source assumption boundaries remain assumptions. Kernel verification proves the Lean declarations and does not by itself establish manuscript fidelity.


## Reproducing the checks

From the repository root, after installing Elan:

```sh
cd LOOConcentration/formal
lake exe cache get
python3 scripts/ci.py
```

CI verifies the exact source allowlist and import closure, rejects production
holes and custom axioms, checks clean pinned dependencies, builds all 560
production modules, verifies 25 retained dependency file/command/ABI pins, and
audits 86 interface/correspondence exports. It also checks the four challenge
and solution types, standard-only solution axioms, and ten comparator
regressions, then rechecks source and dependency pins. Fetch the pinned caches
first: the checker stops if it observes upstream compilation.

The release was verified with initially empty project artifacts and a separate
copy of existing pinned dependency caches. This did not test a first-time
network cache download. All nine dependency checkouts and their cached
artifacts remained unchanged during validation.

The pinned GitHub Actions workflow runs the same complete checker. Generated
reports are excluded from version control and written under
`LOOConcentration/formal/verification/` and
`LOOConcentration/formal/challenges/reports/`. After a build, the retained
dependency ABI check can also be run with
`python3 scripts/check_dependency_anchors.py`.

## Provenance

`PUBLIC_SOURCES.json` records the exact code hashes, production module closure and entry points. `revision-anchors.json` records the manuscript interfaces and their manuscript source hash. `dependency-anchors.json` contains only the frozen dependency declarations required by this closure, retaining their file, declaration and elaborated ABI pins. Private campaign records and draft snapshots do not ship; public provenance is distilled from earlier audits without claiming a new audit of a later paper.

Protected dependency files retain original comment-only manuscript filenames and line locators because their full-file hashes are immutable audit pins. These are provenance markers, not available files or manuscript links. Other internal path comments were scrubbed to the public paper URL. Existing inherited source diagnostics and two scoped `linter.style.haveILetI` exceptions are preserved; neither exception disables proof checking. The new release axiom audit runs from a separate temporary probe.


See the [README](README.md) for the mathematical results, imports, challenges,
and license, and the [challenge guide](LOOConcentration/formal/challenges/README.md)
for the comparator format and its limitations.
