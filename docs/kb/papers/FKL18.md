---
kind: paper
bibkey: FKL18
title: "The Algebraic Group Model and its Applications"
year: 2018
bib_source: blueprint/src/references.bib
canonical_url: https://www.iacr.org/archive/crypto2018/10993298/10993298.pdf
source_metadata: ../sources/FKL18/metadata.yml
status: seeded
related_modules:
  - ArkLib/AGM/Interaction.lean
---

# FKL18

## At A Glance

The representation-based AGM definition in Section 2.1 is the starting point for
ArkLib's explained group-interaction interface.

## What ArkLib Uses From This Paper

Outgoing group elements carry representations over previously received group inputs.
Incoming group elements extend the available basis without explanations of their own.

## Main ArkLib Touchpoints

- `ArkLib/AGM/Interaction.lean`: indexed group lists, explanations, all-reply-path
  algebraicity, certified adversaries, and execution soundness.
- `ArkLibTest/AGM/`: adaptive execution and representation-boundary regression tests.
- [AGM guide](../../wiki/algebraic-group-model.md): interface and game-design responsibilities.

## Open Formalization Gaps

The interface does not formalize computational efficiency or semantic independence of
ordinary data and advice from unlisted group inputs. It uses additive same-sort
representations and does not implement pairing-product explanations. It does not prove
the paper's application theorems or equivalence with the former handle-table interface.

## Source Access

- [Paper](https://www.iacr.org/archive/crypto2018/10993298/10993298.pdf), Section 2.1.
- [Source metadata](../sources/FKL18/metadata.yml).
