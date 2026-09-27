# Algebraic Group Model

`ArkLib/AGM/Interaction.lean` defines the representation-based interface in namespace `AGM`.
`ArkLib/AGM/Basic.lean` retains the independent finite-indexed, multiplicative
`GroupRepresentation` utility and its prime-order lemmas.

## Interface

- `Message Data G` separates ordinary data from explicit group lists, one per sort.
- `Explained F Data G` attaches one coefficient vector to each outgoing group element.
- `Explained.Valid` requires exact vector lengths and same-sort reconstruction.
- `IsAlgebraic` checks requests before their replies and final outputs on every reply path.
- `Adversary` bundles a program with that proof. `Adversary.run` executes it using the
  game's plain oracle handler, appending received group elements to the tracked lists.
- `Adversary.run_valid` proves final representation validity for every supported result
  when the handler executes in an ambient `OracleComp`. It is not a runtime check.

One group uses `Tag := Unit`. Multiple groups use `G : Tag -> Type` with a shared scalar
type. A group output is explained only from previously received values of its own sort;
its coefficients may depend on data or values observed in other sorts. Oracle replies
need no explanations. No hash, signing, pairing, or group-operation oracle is prescribed.

## Replacing the Handle Interface

The handle-table API (`GroupValTable`, the `Group*Oracle` specifications and their
implementations, and the old `Adversary` and unfinished `Adversary.run`) is removed.
The new `AGM.Adversary` and `AGM.Adversary.run` have different types and semantics:
adversaries receive actual values and explain outgoing group elements, rather than
constructing them only through table-operation oracles and returning handles.

Callers supply a group family, ordinary input/query/reply/result types, an algebraicity
proof, explicit initial group inputs, and a plain oracle handler. There is no automatic
translation from handle programs and no claim that the two adversary models are equivalent.
`GroupRepresentation` and its existing tests remain unchanged; the interaction layer uses
additive, list-based explanations and does not yet provide a conversion theorem between them.

## Game Review Boundary

Register relevant incoming group elements, including generators and public keys, in
`groups`, both initially and in oracle replies. Read group-valued requests and candidate
answers from the explained `groups` lists, or check equality to entries there. For example,
a hash reply introduces a new group input without coefficients; a candidate signature
must be read from an explained output list rather than decoded from unchecked `data`.

Payload types and advice must not hide unlisted group inputs. The type system does not
enforce this semantic condition. The interface also does not establish computational
efficiency or provide pairing-product representations in a target group. All-reply-path
algebraicity is stronger than checking only paths supported by a particular handler.

## Verification

`ArkLibTest/AGM/` covers the retained prime-order representation API, one- and two-group
adaptive execution, repeated inputs, malformed representations, same-sort isolation,
future-input rejection, and axiom/API guards. Run the repository's normal `lake test`
and `scripts/validate.sh --axioms` checks; no separate package or dependency is needed.
