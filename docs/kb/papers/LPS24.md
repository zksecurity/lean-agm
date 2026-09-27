---
kind: paper
bibkey: LPS24
title: "On Knowledge-Soundness of Plonk in {ROM} from Falsifiable Assumptions"
year: 2024
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2024/994
source_metadata: ../sources/LPS24/metadata.yml
status: seeded
related_modules:
  - ArkLib/AGM/Interaction.lean
  - ArkLib/ProofSystem/Plonk/Basic.lean
---

# LPS24

## At A Glance

`LPS24` is background for AGM-style reasoning about Plonk knowledge-soundness.
It motivated the former handle-table interface; the replacement instead cites [FKL18](FKL18.md).

## What ArkLib Uses From This Paper

- Background for applications of the explained-value interface in `ArkLib/AGM/Interaction.lean`.
- Conceptual linkage between AGM-style reasoning and Plonk knowledge-soundness questions.

## Main ArkLib Touchpoints

- `ArkLib/AGM/Interaction.lean` provides an interface, not an implementation of this paper's proof.
- [`ArkLib/ProofSystem/Plonk/Basic.lean`](../../../ArkLib/ProofSystem/Plonk/Basic.lean) is the
  natural neighboring subtree when this reference matters in protocol work.

## Version Notes

- This is the ePrint version currently recorded in `references.bib`.
- In ArkLib, `LPS24` matters mainly as a modeling and motivation reference until the AGM and Plonk
  subtrees are more complete.

## Known Divergences From ArkLib

- ArkLib has not yet formalized a full `LPS24`-style knowledge-soundness development.
- The current AGM module proves explained-value execution soundness, not the paper's end results.

## Open Formalization Gaps

- If AGM or Plonk work becomes active, this page should likely grow into an audit page covering
  which parts of the knowledge-soundness argument are actually present in ArkLib.

## Source Access

- Source metadata: [`../sources/LPS24/metadata.yml`](../sources/LPS24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
