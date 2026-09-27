# Lean AGM

A representation-based algebraic group model layer for Lean 4 and VCVio. Apache-2.0.

Read the [line-by-line review](docs/review.md) for definitions, types, and theorem statements
without proof walkthroughs. Tests and guards have a [separate review](docs/review-tests.md).

- [Interaction](AlgebraicGroupModel/Interaction.lean): explained outgoing group arguments
  and final outputs, separate input lists per group sort, and a certified adaptive runner.
- [Tests](AGMTest): one- and two-group execution, invalid representations, and axiom guards.

Incoming group replies need no explanations and extend the chronological basis.
Each outgoing element must reconstruct from inputs received **before** that output.
The certified runner passes actual query values to the game; its soundness theorem proves
final representation validity. It does not check explanations at runtime.
No hash/signing oracle, pairing, group-operation machine, or signature game is prescribed.
`Interaction.Adversary` is the only interface. It accepts an indexed family
`G : Tag → Type` over a shared coefficient type. For one group, use `Tag := Unit`
and `G := fun _ => G1`.

`message.groups s` lists values of sort `s`, and
`output.coefficients s` explains them only from previously received values of that sort.
All sorts share one adaptive query stream; replies may introduce values in any of them.

## Explanation Rule

Every group element in an adversary's outgoing `groups` lists, whether in an oracle query
or the final answer, must come with coefficients expressing it as a linear combination
of previously received inputs from the same group. There must be exactly one coefficient
per tracked input, and the combination must equal the outgoing element.

For example, if the tracked inputs are `[g, H, S]`, an output `sigma` with coefficients
`[a, b, c]` must satisfy:

```text
sigma = a * g + b * H + c * S
```

Here `*` denotes scalar multiplication. An oracle reply is the answer to an adversary's
query. Its group elements need no explanations: they become new tracked inputs. Starting
from `[g]`, receiving a hash reply `H` extends the list to `[g, H]`, so later outputs may
use both. The query itself cannot use that reply before it arrives.

The adversary supplies a Lean proof that this rule holds for every possible reply path,
not only those produced by a particular game. Outputs and coefficients may depend on the
replies; whatever replies arrive, the explanations must remain valid. The runner does not
check this at runtime, and the rule does not check ordinary `data`.

## Build

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build AlgebraicGroupModel AGMTest
```

Use `import AlgebraicGroupModel` or individual modules. Lean and VCVio are pinned.

To use the library from another project's `lakefile.lean`:

```lean
require «lean-agm» from git
  "https://github.com/zksecurity/lean-agm" @ "main"
```

Use a compatible Lean toolchain. Replace `main` with a reviewed commit hash to pin the
dependency reproducibly.

## Scope

The explanation rule must hold for every possible oracle reply, not just replies from one
particular game. Group elements, including starting generators, must go in the explicit
`groups` lists, both in initial inputs and in later messages. Lean does not inspect `data`
or advice for hidden group elements. Hiding one there does not bypass the checks on `groups`,
but can give the adversary untracked information. A game must also read group-valued requests
and candidate answers from `groups` (or check equality to an explained entry), not accept
unchecked group values decoded from `data`. Ordinary messages, labels, and sampled numbers
can stay in `data`; their types and interpretation must not hide additional group inputs.
This boundary is the game designer's responsibility. Each adversary supplies a Lean proof
for its outgoing `groups`; no manual review of its implementation replaces that proof.
Each group output must be explained using inputs from the same group.
Explaining outputs of a pairing needs additional machinery.
This library does not bound running time. Replacing ArkLib's current model with it would require
updating callers and reviewing the change in which adversaries the model allows.

The starting point is Fuchsbauer, Kiltz, and Loss,
[*The Algebraic Group Model and its Applications*, Section 2.1](https://www.iacr.org/archive/crypto2018/10993298/10993298.pdf).
Extracted from `zksecurity/bls-lean`; token/output adapters and signature security proofs
live there, not in this library.

## ArkLib Integration

A proposed home is `ArkLib/AGM/Interaction.lean`, with tests under `ArkLibTest/AGM/`, alongside
the [existing `AGM/Basic.lean`](https://github.com/Verified-zkEVM/ArkLib/blob/7653a901ed466c88a2e61a3075011b73d7bb2316/ArkLib/AGM/Basic.lean).
That module uses table handles and group-operation oracles; this one uses actual group values
and supplied explanations. They could coexist; replacing the existing interface would require
an explicit migration and a decision about this difference in the adversary model.
The port needs ArkLib's module/export conventions, compatible dependencies, and its test/lint
checks. Missing bridges include converting our list-based additive explanations to its
finite-indexed, multiplicative `GroupRepresentation`, and relating the two execution models.
We also do not enforce the absence of hidden group inputs, bound running time, or support
pairing-output explanations. These are separate gaps, not claims that upstreaming would prove.
