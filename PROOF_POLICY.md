# Proof policy

Every production Lean module must compile with the pinned toolchain. No placeholders, custom mathematical axioms, unsafe proof escapes, unchecked native decision procedures or opaque model-identification assumptions may be used to upgrade paper coverage.

The declaration audit inventories by actual defining module, rather than only a namespace prefix. It includes definitions, generated declarations and theorem types. Transitive axioms must be a subset of `propext`, `Classical.choice` and `Quot.sound`. Mathlib and Lean remain trusted dependencies; no complete manual review of those libraries is claimed.

The exact formal statement matters. A theorem proved under an unproved weighted-volume input is a conditional deduction; a finite geometric identity used in an analytic proof is supporting coverage. Neither certifies the complete paper theorem. Full status requires every conclusion and its original hypotheses to match checked declarations for the paper's objects, up to documented representation equivalences.

The [proof correspondence ledger](formalization/proof-correspondence.json) distinguishes statement coverage from reviewed mathematical proof strategy. The companion has short proof ideas and optional full expositions for selected results.

A full certificate retains the genuine hypotheses of the manuscript. A major cited result can appear as a named, explicitly disclosed premise. See [GAPS.md](formalization/GAPS.md).

Older reusable lemmas may expose geometry or concentration records as explicit parameters. Such a lemma alone does not certify a paper assertion. The final direct endpoints must discharge those records or supply their own proved estimates, and their complete types must contain no unproved mathematical theorem parameter.

Proof ideas carry the same status as the corresponding certificate. A cited-premise deduction names the premise in its heading and explanation. Appendix B gives optional full expositions of selected proofs. The original manuscript retains its full written arguments separately. Removing editorial color wrappers from the generated companion must retain all their content and may not change an assertion. Questions, conjectures, the explicitly labeled counting heuristic and quoted prior literature are excluded from proved-assertion counts. Substantive proved remarks and separately inventoried claims in the prose are included and have their own source endpoints.

Frozen structural types and manuscript statement identities are independent of editable presentation indexes. Full type expressions and complete evidence are retained losslessly in compressed JSON; the small JSON indexes are conveniences and do not replace the full-type comparison. A Lean source edit, import edit, added declaration, type change or audit-input change requires fresh complete compilation and audit, inspection of actual types, and renewed correspondence review.

A manuscript-only revision still invalidates the old manuscript/PDF snapshot. It requires renewed statement and proof-method review, updated source fingerprints, an actual PDF build with a matching receipt, and a deliberate new release snapshot. When every checked Lean source and audit input is unchanged and hash-matched, the existing complete kernel evidence may be reused. Such a revision must say that it reuses the audit, rather than claim a new kernel run. This revision changes Lean proofs and therefore requires a new whole-project audit; the exact counts and audit time are recorded in release/verification.json. The check command never refreshes evidence automatically.

Audit workers partition the actual module-defined declaration inventory by a deterministic name hash. Each selected declaration receives the same official transitive-axiom traversal and complete type serialization as an unsharded audit. Worker totals must agree, all shard indices must be present, and the merged unique rows must equal the full inventory count. Every project module must remain represented. No cached or approximate axiom result substitutes for this audit.

GitHub Actions configuration is reproducibility infrastructure, not evidence of a successful remote run. Saved local evidence identifies its actual build mode and checked sources.
