# AGM Review: Definitions and Statements

A source-order walkthrough of the complete public interface. Tests and guards have their own
[test review](review-tests.md). **Definition bodies are included; theorem proof bodies are not.**
A theorem excerpt stops at its proposition, before `:=`.

Each quotation uses the actual source line numbers, written as `number | code`. These numbers
are reading annotations, not Lean syntax; excerpts are not standalone Lean files.
Each review item starts with its purpose in plain English, followed by the source and line notes.

Source quotations and line numbers refer to the source files alongside this guide.
Links below use paths within this repository and source line anchors.

## Reading Route

1. [Notation and type parameters](#notation-and-type-parameters)
2. [Source setup](#source-setup)
3. [Groups](#groups), [extend](#extend), [Message](#message), [Explained](#explained)
4. [evaluate](#evaluate), [Valid](#explainedvalid), [ofVectors](#explainedofvectors), [constructor guarantee](#explainedvalid_ofvectors)
5. [plainSpec](#plainspec), [explainedSpec](#explainedspec)
6. [IsAlgebraic](#isalgebraic), [return rule](#isalgebraic_pure), [query rule](#isalgebraic_query), [Adversary](#adversary)
7. [Certified execution](#adversaryrun), [soundness](#adversaryrun_valid)
8. [Build and repository files](#build-and-repository-files), [review checklist](#review-checklist)
9. Separate [test review](review-tests.md)

## Notation and Type Parameters

| Lean notation | Read it as |
| --- | --- |
| `x : T` | Value `x` has type `T`. |
| `F : Type` | `F` is a type. Here `Type` means `Type 0`. |
| `A → B` | A function taking an `A` and returning a `B`. Arrows associate to the right. |
| `(s : Tag) → List (G s)` | A function whose return type depends on its argument `s`. |
| `f a b` | `(f a) b`: application uses spaces and associates to the left. |
| `(x : T)` / `{x : T}` | Explicit / usually inferred parameter. |
| `[C]` | A typeclass instance argument, usually filled by instance search. |
| `(Reply := Reply)` | Supply a parameter explicitly by name. |
| `fun x => e` | A function mapping `x` to expression `e`. |
| `fun _ => e` | A function ignoring its argument. |
| `(· ++ ·)` | Anonymous two-argument list append; `·` marks argument positions. |
| `⟨a, b⟩` | Construct a record or pair, inferred from the expected type. |
| `z.1` / `z.2` | First / second component of a pair. |
| `Prop` / `Bool` | A logical proposition / an executable Boolean value. |
| `∀`, `∧`, `↔`, `¬`, `∈` | For all; and; if and only if; not; belongs to. |
| `def` / `abbrev` | A definition / an abbreviation intended to unfold readily. |
| `structure` / `theorem` | A record type / a named proved proposition. |
| `private` / `example` | A file-local declaration / an unnamed checked theorem. |
| `@[simp]` | Make this theorem available as a simplification rule. |
| `:=` / `where` | Begin a definition's body / a structure's fields or record construction. |

The common parameters are:

| Parameter | Meaning |
| --- | --- |
| `Tag` | Group-sort labels, such as two labels for G1 and G2. |
| `G : Tag → Type` | The carrier type for each group sort. |
| `F` | Shared coefficient type, typically a scalar field in applications. |
| `Data`, `Input`, `Query`, `Result` | Ordinary payload types for the relevant message. |
| `Reply : Query → Type` | Ordinary reply-data type, allowed to depend on the request data. |
| `N : Type → Type` | Target computation type when interpreting an adversary. |

### OracleComp Has Two Arguments

```text
OracleComp (explainedSpec F G Query Reply) (Explained F Result G)
           ^ oracle interface             ^ final result type
```

After receiving `spec`, `OracleComp spec` still expects a result type.
The result is a type of interactive programs, not a completed result value.
A program can return immediately or issue a request and continue based on its reply.

The pinned VCVio definition has the shape
`OracleComp (spec : OracleSpec.{u,v} ι) : Type w → Type (max u v w)`.
Its last argument is written in the return function type, rather than as a named parameter.
Our interface instantiates `u`, `v`, and `w` with zero.
Universe levels classify types; they are not runtime sizes or costs.
A specification returning reply types can itself live one level higher:
if `ι : Type u`, then `ι → Type v` has type `Type (max u (v + 1))`.

These explanations follow the locally pinned
[OracleComp source](https://github.com/Verified-zkEVM/VCVio/blob/f5119c64ebb055d69c143704e12eba6df7dc386c/VCVio/OracleComp/OracleComp.lean)
and [QueryImpl source](https://github.com/Verified-zkEVM/VCVio/blob/f5119c64ebb055d69c143704e12eba6df7dc386c/VCVio/OracleComp/SimSemantics/QueryImpl/Basic.lean).

## Source Setup

All public declarations below are in
[`AlgebraicGroupModel/Interaction.lean`](../AlgebraicGroupModel/Interaction.lean).

| Source | Meaning |
| --- | --- |
| [Lines 1-5](../AlgebraicGroupModel/Interaction.lean#L1) | Copyright, author, and Apache-2.0 notice; no mathematical declaration. |
| [Line 6](../AlgebraicGroupModel/Interaction.lean#L6) | Import list sums and their algebraic infrastructure. |
| [Line 7](../AlgebraicGroupModel/Interaction.lean#L7) | Import scalar-multiplication infrastructure. |
| [Line 8](../AlgebraicGroupModel/Interaction.lean#L8) | Import indexed list operations used by coefficient vectors. |
| [Line 9](../AlgebraicGroupModel/Interaction.lean#L9) | Import oracle-program interpretation via `simulateQ`. |
| [Line 10](../AlgebraicGroupModel/Interaction.lean#L10) | Import structural support: which outputs an oracle program can reach. |
| [Lines 12-33](../AlgebraicGroupModel/Interaction.lean#L12) | Scope documentation and literature reference; not extra hypotheses enforced by Lean. |
| [Line 35](../AlgebraicGroupModel/Interaction.lean#L35) | Open the namespace; e.g. the full name of `Message` is `AlgebraicGroupModel.Interaction.Message`. |
| [Line 37](../AlgebraicGroupModel/Interaction.lean#L37) | Allow shorter names from `OracleComp` and `OracleSpec`. |
| [Line 39](../AlgebraicGroupModel/Interaction.lean#L39) | Declare the implicit group-label type used by subsequent definitions. |
| [Line 97](../AlgebraicGroupModel/Interaction.lean#L97) | Declare common implicit types for following statements instead of repeating every binder. |
| [Lines 99, 101](../AlgebraicGroupModel/Interaction.lean#L99) | Start a section and make algebraic-operation instances available to its declarations. |
| [Line 158](../AlgebraicGroupModel/Interaction.lean#L158) | End the local section, including certified execution. Previously defined declarations retain their parameters. |
| [Line 160](../AlgebraicGroupModel/Interaction.lean#L160) | Close the namespace. |

Comments, blank lines, and proof bodies add no further public statements.
The source calls these carriers groups, but its minimal assumptions are weaker:
`AddMonoid` need not be commutative and `SMul` supplies an operation, not module laws.

## Groups

**In plain English:** Keep a separate ordered list of received group elements for each group sort. The list records positions, so repeated values remain separate inputs.

[Source line 42](../AlgebraicGroupModel/Interaction.lean#L42). Definition, including its body.

```lean
42 | abbrev Groups (G : Tag → Type) := (s : Tag) → List (G s)
```

| Line | Explanation |
| --- | --- |
| 42 | `abbrev` defines an easily unfolded abbreviation, not a new wrapper with a constructor. `G` maps each group label to its carrier type. The result `(s : Tag) → List (G s)` is a dependent function: choosing `s` also determines the type of elements in the returned list. |

For two labels, this can hold a list of G1 elements and a differently typed list of G2 elements.
It is not a combined list of untyped points. For one group, choose `Tag := Unit` and
`G := fun _ => G1`; then `inputs ()` is its list. These are received-input lists, often called
bases here, but **no linear independence is assumed**. Repeated values keep separate positions.
Each list is finite; the definition does not require the set of group labels to be finite.

## extend

**In plain English:** Append newly received values to the end of each sort's list. Earlier positions stay unchanged, so later explanations can still refer to them.

[Source line 45](../AlgebraicGroupModel/Interaction.lean#L45). Definition, including its body.

```lean
45 | def extend {G : Tag → Type} (inputs replies : Groups G) : Groups G :=
46 |   fun s => inputs s ++ replies s
```

| Line | Explanation |
| --- | --- |
| 45 | `{G : Tag → Type}` is inferred from the two explicit arguments. Both `inputs` and `replies` are collections of lists with the same group indexing. The result has that same type. |
| 46 | `fun s => ...` builds the new collection, one sort at a time. `++` appends lists: old inputs come first, then this reply's inputs. No sorting, deduplication, or cross-sort transfer occurs. |

Example: `[P, Q] ++ [R, P]` becomes `[P, Q, R, P]`.
The helper itself can append any lists. Its use by `IsAlgebraic` and `Adversary.run` is what ensures
that only received replies, not the adversary's outgoing elements, extend the basis.

## Message

**In plain English:** Package ordinary data together with the group elements being sent. This is the plain message format: it makes no claim about how those elements were constructed.

[Source line 49](../AlgebraicGroupModel/Interaction.lean#L49). Definition, including its body.

```lean
49 | structure Message (Data : Type) (G : Tag → Type) where
50 |   data : Data
51 |   groups : Groups G
```

| Line | Explanation |
| --- | --- |
| 49 | `structure` declares a record. `Data` is the ordinary payload type; `G` supplies the group carrier types. The record is parameterized by those types. |
| 50 | `data : Data` stores one ordinary payload value. |
| 51 | `groups : Groups G` stores a separate list of actual group values for each sort. This field has no coefficients and no validity proof. |

A message could contain `data = requestDescription`, `groups source1 = [P]`, and
`groups source2 = []`. The direction of communication is not built into `Message`:
the same shape can describe initial inputs, plain requests received by a game, or replies.

There is no `F` parameter because this envelope contains no scalar explanations.
The name `data` does not forbid a protocol from choosing a payload type that itself contains
group values. The game must designate its relevant group inputs correctly, both initially
and in every oracle reply. This includes group-valued public parameters and public keys.

The same boundary matters when the game receives a request or final answer: read its
group-valued components from `groups`, or check that they equal explained entries there.
For example, a signature game's message can be ordinary `data`, but its candidate signature
must come from `groups`. Decoding a different signature from `data` and accepting it would
bypass the representation guarantee. Lean checks the adversary's proof for `groups`, not
the game's interpretation of `data`.

Review these input and output boundaries in the game, not each adversary's implementation.
Every `Adversary` already carries a proof covering all its outgoing group lists on all reply
paths. This does not establish that arbitrary payload types or advice are free of hidden
group inputs; that remains a requirement on the modeled protocol.

## Explained

**In plain English:** Attach a claimed coefficient vector to each outgoing group element. This record stores the explanations, but does not itself prove they are correct.

[Source line 54](../AlgebraicGroupModel/Interaction.lean#L54). Definition, including its body.

```lean
54 | structure Explained (F Data : Type) (G : Tag → Type) where
55 |   value : Message Data G
56 |   coefficients : Tag → List (List F)
```

| Line | Explanation |
| --- | --- |
| 54 | This record adds a common coefficient type `F` to the ordinary payload type and group family. |
| 55 | `value` is the actual outgoing message, including its payload and group values. |
| 56 | Choose a sort with `coefficients s`. The outer list then supplies one coefficient vector per outgoing element; each inner `List F` supplies one coefficient per received input of that sort. |

If the received list is `[P, Q]` and the outgoing list is `[R, S]`, coefficients
`[[2, 3], [0, 1]]` claim `R = 2 • P + 3 • Q` and `S = 0 • P + 1 • Q`.
This notation uses the usual scalar laws in that example.

**This record stores a claim, not a proof.** It is possible to construct an `Explained`
value with the wrong vector lengths or incorrect group values. `Valid` checks it;
`Adversary.algebraic` certifies that all outputs and requests satisfy those checks.

## evaluate

**In plain English:** Reconstruct one group element by multiplying each received input by its coefficient and adding the results. This function computes a value; it does not check that the coefficient list has the right length.

[Source line 59](../AlgebraicGroupModel/Interaction.lean#L59). Definition, including its body.

```lean
59 | def evaluate {F G : Type} [Zero F] [AddMonoid G] [SMul F G]
60 |     (coeff : List F) (inputs : List G) : G :=
61 |   (inputs.mapIdx fun n g => (coeff[n]?).getD 0 • g).sum
```

| Line | Explanation |
| --- | --- |
| 59 | Here `G : Type` is a single carrier, not the indexed family from `Groups`. `Zero F` supplies scalar zero, `AddMonoid G` supplies addition and group-value zero, and `SMul F G` supplies the operation `•`. These are typeclass arguments, found by Lean. |
| 60 | The explicit inputs are a coefficient list and a group-value list. The result is one group value, not a proposition. |
| 61 | `mapIdx` visits the received inputs with zero-based indices `n`. `coeff[n]?` safely looks up a coefficient, returning an `Option F`; `.getD 0` chooses scalar zero if it is missing. Each term is that scalar multiplied by `g`; `.sum` adds the terms in list order. |

For ordinary natural-number arithmetic, `evaluate [2, 3] [4, 5] = 23`.
Coefficients past the end of the input list are never visited. Missing coefficients use
scalar zero; **this does not make a short or long vector valid**. The next definition
independently requires exact lengths.

These hypotheses do not assert that `F` is a field, that `G` is a group, or that scalar
multiplication satisfies module laws. In particular, `SMul` by itself does not prove
`0 • g = 0`. Cryptographic instantiations can provide stronger structures.

## Explained.Valid

**In plain English:** Require an explanation for every outgoing group element, with exactly one coefficient per received input of the same sort. Each explanation must reconstruct the actual value being sent.

[Source line 64](../AlgebraicGroupModel/Interaction.lean#L64). Definition, including its body.

```lean
64 | def Explained.Valid {F Data : Type} {G : Tag → Type}
65 |     [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]
66 |     (inputs : Groups G) (out : Explained F Data G) : Prop :=
67 |   ∀ s, List.Forall₂
68 |     (fun g coeff => coeff.length = (inputs s).length ∧ evaluate coeff (inputs s) = g)
69 |     (out.value.groups s) (out.coefficients s)
```

| Line | Explanation |
| --- | --- |
| 64 | The payload type and group family are implicit parameters. `Explained.Valid` is a namespaced definition, which can also be written using dot notation. |
| 65 | Every sort must have an additive monoid and scalar multiplication by the same `F`. `∀ s` makes these requirements uniform across the group family. |
| 66 | The explicit arguments are the received inputs and a claimed outgoing message. The result is a `Prop`: a logical condition, not a runtime Boolean. |
| 67 | `∀ s` checks every sort. `List.Forall₂` relates two lists position by position and also requires them to have the same number of entries. |
| 68 | For each outgoing value `g` and its corresponding vector `coeff`, require both exact input-list length and correct reconstruction. `∧` means both obligations are necessary. |
| 69 | The two lists being matched are the actual outgoing group elements and their claimed vectors, at the same sort `s`. |

Thus there are two separate length checks: one vector per outgoing element, and one
coefficient per received input in each vector. `out.Valid inputs` means
`Explained.Valid inputs out`; the field-style notation does not change the argument order.

The payload `out.value.data` is not checked here. A G2 value cannot use G1 entries as
terms in its representation, but its coefficients may depend on ordinary data and previous
replies of either sort. This is a reconstruction condition, not information-flow isolation.

## Explained.ofVectors

**In plain English:** Construct outgoing values from coefficient vectors whose lengths already match the received lists. Because the values are computed from those vectors, their explanations match by construction.

[Source line 72](../AlgebraicGroupModel/Interaction.lean#L72). Definition, including its body.

```lean
72 | def Explained.ofVectors {F Data : Type} {G : Tag → Type}
73 |     [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]
74 |     (inputs : Groups G) (data : Data) (vectors : (s : Tag) → List (Fin (inputs s).length → F)) :
75 |     Explained F Data G :=
76 |   ⟨⟨data, fun s => (vectors s).map fun v => evaluate (List.ofFn v) (inputs s)⟩,
77 |     fun s => (vectors s).map List.ofFn⟩
```

| Line | Explanation |
| --- | --- |
| 72 | This is a constructor helper for building a valid explained message, rather than manually claiming values and witnesses separately. |
| 73 | It uses the same scalar-zero, addition, and scalar-multiplication requirements as the evaluator. |
| 74 | `inputs` is the current basis and `data` is the payload. For each sort, `vectors` supplies a list of functions `Fin (inputs s).length → F`. `Fin n` contains indices below `n`, so each such function gives exactly one coefficient at every valid input position. |
| 75 | The result is an `Explained` record. |
| 76 | The inner `⟨...⟩` constructs its `Message`: retain `data`, convert each vector function to a list with `List.ofFn`, and evaluate it to compute the actual outgoing group value. |
| 77 | The outer record's second field stores those same coefficient lists as the explanations. |

This helper computes the outgoing values from supplied vectors. It does not take arbitrary
output values and discover representations for them. A vector over `Fin 0` yields an empty
coefficient list and an empty sum.

## Explained.valid_ofVectors

**In plain English:** Guarantee that every output built by `ofVectors` has valid explanations. The caller need not separately establish that the generated values match their coefficients.

[Source line 79](../AlgebraicGroupModel/Interaction.lean#L79). Theorem statement only.

```lean
79 | theorem Explained.valid_ofVectors {F Data : Type} {G : Tag → Type}
80 |     [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]
81 |     (inputs : Groups G) (data : Data) (vectors : (s : Tag) → List (Fin (inputs s).length → F)) :
82 |     (Explained.ofVectors inputs data vectors).Valid inputs
```

| Line | Explanation |
| --- | --- |
| 79 | `theorem` introduces a proved proposition. Its name is attached to the `Explained` namespace. |
| 80 | The same algebraic operations are assumed; no additional field or group laws are introduced. |
| 81 | For any received inputs, payload, and appropriately indexed vectors... |
| 82 | ...the message constructed by `ofVectors` is valid for those exact inputs. This is the conclusion, not another assumption. The proof body is omitted here. |

This is the constructor's correctness guarantee. It does not certify an entire adaptive
program; that requires the recursive condition below.

## plainSpec

**In plain English:** Describe the oracle interface seen by the game: a plain request goes in, and a plain reply comes back. The request's ordinary data determines the type of ordinary data in its reply.

[Source line 90](../AlgebraicGroupModel/Interaction.lean#L90). Definition, including its body.

```lean
90 | abbrev plainSpec (G : Tag → Type) (Query : Type) (Reply : Query → Type) : OracleSpec (Message Query G) :=
91 |   fun q => Message (Reply q.data) G
```

| Line | Explanation |
| --- | --- |
| 90 | `Query` is the ordinary request-data type. `Reply : Query → Type` assigns an ordinary reply-data type to each request. `OracleSpec (Message Query G)` uses whole plain messages as its request indices. |
| 91 | For a request `q`, the reply is a `Message` with ordinary data of type `Reply q.data` and group values from the same family `G`. |

This describes reply **types**, not reply values, a distribution, or an implementation.
For example, one query constructor could expect an integer payload and another could expect
`Unit`. The handler still receives the entire request, including its group arguments, even
though the ordinary reply type is selected only by the request's ordinary data.

## explainedSpec

**In plain English:** Describe the interface seen by the algebraic adversary: outgoing requests carry explanations, but incoming replies do not. A reply can therefore introduce group elements that were not previously available.

[Source line 94](../AlgebraicGroupModel/Interaction.lean#L94). Definition, including its body.

```lean
94 | abbrev explainedSpec (F : Type) (G : Tag → Type) (Query : Type) (Reply : Query → Type) :
95 |     OracleSpec (Explained F Query G) := fun q => Message (Reply q.value.data) G
```

| Line | Explanation |
| --- | --- |
| 94 | Add a coefficient type `F` to the same group family and request/reply-data interface. |
| 95 | Requests now have type `Explained F Query G`. Replies remain plain `Message` values, with ordinary reply type selected by `q.value.data`. |

The direction is crucial:

| Direction | Type | Explanation required? |
| --- | --- | --- |
| Adversary sends a request | `Explained F Query G` | Yes, certified by `IsAlgebraic`. |
| Oracle sends its reply | `Message (Reply q.value.data) G` | No. |
| Adversary returns its final result | `Explained F Result G` | Yes. |

A hash-to-group oracle may supply a fresh value without a representation over earlier inputs.
The oracle's implementation is supplied later; this type does not assume a random oracle.

## IsAlgebraic

**In plain English:** Require every request and final output to be explained using only group elements received before that point. This must hold along every possible reply path, not just the path taken in one run.

[Source line 104](../AlgebraicGroupModel/Interaction.lean#L104). Definition, including its body.

```lean
104 | def IsAlgebraic (inputs : Groups G)
105 |     (program : OracleComp (explainedSpec F G Query Reply) (Explained F Result G)) : Prop :=
106 |   OracleComp.recOn (motive := fun _ => Groups G → Prop) program
107 |     (fun out basis => out.Valid basis)
108 |     (fun q _ next basis => q.Valid basis ∧
109 |       ∀ reply, next reply (extend basis reply.groups)) inputs
```

| Line | Explanation |
| --- | --- |
| 104 | Start with received-input lists `inputs`. This is not a transcript of future values. |
| 105 | `program` is an interactive computation whose requests follow `explainedSpec` and whose final result is explained. `IsAlgebraic` returns a proposition about that entire program. |
| 106 | `OracleComp.recOn` recursively examines the program's return/query structure. The named `motive` says that at each subtree we build a predicate `Groups G → Prop`, waiting for the basis at that point. |
| 107 | Return case: if this subtree returns `out`, require `out.Valid basis` for its current basis. |
| 108 | Query case: `q` is the outgoing request. `_` ignores the raw continuation argument; `next` is the recursively constructed predicate for each reply continuation. First require `q.Valid basis` using the old basis. |
| 109 | For every well-typed reply, apply its continuation's predicate to the basis extended with that reply's group values. The final `inputs` applies the completed predicate to the initial basis. |

### The Whole Condition in Words

Start with the group elements supplied in the initial message. Whenever the program sends
a request, check its explanations against the lists available **before that request**.
After a reply arrives, append its group elements to their respective lists and continue.
When the program returns, check its final explanations against the lists available then.

This is a proposition about a whole interactive program, not an instruction to run the
oracle or a Boolean test. A program may satisfy the proposition without carrying a proof
inside its value; `Adversary.algebraic` is where that proof is required.

### Why the Recursion Returns a Function

An `OracleComp` has two cases: return a result, or make a request and continue after a reply.
The continuation can choose its later requests from earlier replies, so the program is a
branching tree, not a fixed list of queries.

Line 106 recursively builds a predicate for each subtree:

| Expression | Meaning |
| --- | --- |
| `motive := fun _ => Groups G → Prop` | For each subtree, produce a function from received-input lists to a proposition. The `_` ignores which subtree when choosing this return type. |
| `program` | The particular tree being examined. No handler is supplied or executed. |
| `basis : Groups G` | The received-input lists at the point where a subtree is checked. This is a positional list per sort, not necessarily a linearly independent mathematical basis. |
| Final `inputs` on line 109 | Apply the predicate built for the whole program to the starting lists. |

Returning a function lets the same recursively built condition be applied to the correct
lists after each reply. The recursive call follows a smaller program subtree; the
received-input lists are allowed to grow.

### Return Case: Line 107

`fun out basis => out.Valid basis` handles a subtree that immediately returns.

- `out : Explained F Result G` is the final result, including its claimed explanations.
- `basis : Groups G` contains the inputs received along this path.
- `out.Valid basis : Prop` requires a correctly sized coefficient vector reconstructing
  every final group value, separately for each sort.

There are no further requests to check. Ordinary final data is not itself subject to this
reconstruction condition.

### Query Case: Lines 108-109

The recursion provides three arguments before the extra `basis` parameter:

| Argument | Type or role |
| --- | --- |
| `q` | `Explained F Query G`: the outgoing request, with claimed explanations. |
| `_` | The raw continuation, which we can call `k`. It takes a `Message (Reply q.value.data) G` and returns the remaining oracle program. |
| `next` | The recursively constructed predicates: for each reply, `next reply : Groups G → Prop` checks the subtree `k reply`. |
| `basis` | `Groups G`: the received-input lists before this request. |

The raw continuation is ignored in this clause because recursion has already supplied its
algebraicity predicates as `next`. **Here `next reply` is a predicate awaiting a basis, not
another oracle program.** In the theorem `isAlgebraic_query` below, the name `next` instead
denotes the raw continuation.

The conjunction `∧` imposes both obligations:

1. `q.Valid basis`: explain this request now, before receiving its reply.
2. `∀ reply, next reply (extend basis reply.groups)`: for every possible reply, check its
   continuation after adding that reply's inputs.

Equivalently, if we name the raw continuation `k`, the query clause reads as follows.
This is an explanatory expansion, not an additional source quotation:

```text
q.Valid basis ∧
  ∀ reply, IsAlgebraic (extend basis reply.groups) (k reply)
```

The reply is a plain `Message`; it need not explain its own group elements. Only
`reply.groups` extends the lists. Reply data may affect later requests or coefficients,
but does not automatically become a group input. Neither outgoing request values nor
their coefficient vectors are appended by this rule.

### A Concrete Received-So-Far Trace

For illustration, use one ordinary additive group with its usual scalar action.
Let the starting list be `[P, Q]`.

| Point | Available inputs | Example obligation |
| --- | --- | --- |
| Before the first request | `[P, Q]` | Sending `P + Q` with vector `[1, 1]` is valid. |
| After a reply supplies `[R]` | `[P, Q, R]` | A later request can send `R` with vector `[0, 0, 1]`. |
| After another reply supplies `[T]` | `[P, Q, R, T]` | A final output can send `R + T` with vector `[0, 0, 1, 1]`. |

The first request cannot use a coefficient position for `R`: that position does not
exist yet. Receiving `R` later cannot repair an earlier invalid explanation. This does
not forbid sending a value that happens to equal a later reply if it already has a valid
explanation over the current inputs.

With several sorts, the same sequence of replies updates separate lists. An input of
sort G2 does not become a coefficient position in the G1 list. Control flow and
coefficients may nevertheless depend on data or values received in either sort.

### What “Every Reply” Means

`∀ reply` ranges over all messages of the required reply type, including their ordinary
data and all their group lists. It is not restricted to what one chosen oracle handler
would return, or to replies with positive probability. A program valid only for one
handler's replies may therefore fail this stronger all-reply-path condition.

For example, the continuation must accommodate different reply-list lengths: a vector
that fits only a reply with exactly one group value is insufficient unless the program
handles other lengths too. `Explained.ofVectors` helps construct vectors with the right
length for the inputs actually received on each path.

Keep three levels distinct:

| Condition | Scope |
| --- | --- |
| `out.Valid basis` | One outgoing message, checked against one received-input list per sort. |
| `IsAlgebraic inputs program` | Every request and final output on every reply path, from these starting lists. |
| `A.algebraic : ∀ input, IsAlgebraic input.groups (A.main input)` | That whole-program guarantee for every initial message as well. |

None of these conditions bounds query counts or runtime, imposes a reply distribution,
or ensures that ordinary data hides no unlisted group inputs. The runner does not
validate explanations at runtime; the certificate supplies the mathematical guarantee.

## isAlgebraic_pure

**In plain English:** For a program that immediately returns, there is only one obligation: its final output must have valid explanations over the inputs already received.

[Source line 111](../AlgebraicGroupModel/Interaction.lean#L111). Theorem statement only.

```lean
111 | @[simp] theorem isAlgebraic_pure (inputs : Groups G) (out : Explained F Result G) :
112 |     IsAlgebraic (Reply := Reply) inputs (pure out) ↔ out.Valid inputs
```

| Line | Explanation |
| --- | --- |
| 111 | `@[simp]` registers this theorem as a simplification rule. Its explicit arguments are a current basis and an explained final result. |
| 112 | A program that immediately returns `out` is algebraic exactly when that output is valid. `↔` is logical equivalence. `(Reply := Reply)` explicitly supplies an otherwise difficult-to-infer parameter, since this program makes no queries. |

`pure out` makes no oracle calls. It still has to explain its final group elements.
The theorem uses the inherited algebraic-operation assumptions from line 101.

## isAlgebraic_query

**In plain English:** For a program that makes a request, check the request using the current inputs, then check the rest of the program for every reply using the enlarged input lists. This is the one-query unfolding of `IsAlgebraic`.

[Source line 114](../AlgebraicGroupModel/Interaction.lean#L114). Theorem statement only.

```lean
114 | @[simp] theorem isAlgebraic_query (inputs : Groups G) (q : Explained F Query G)
115 |     (next : Message (Reply q.value.data) G →
116 |       OracleComp (explainedSpec F G Query Reply) (Explained F Result G)) :
117 |     IsAlgebraic inputs (OracleComp.queryBind q next) ↔
118 |       q.Valid inputs ∧ ∀ reply, IsAlgebraic (extend inputs reply.groups) (next reply)
```

| Line | Explanation |
| --- | --- |
| 114 | Take the current basis and an explained outgoing request. |
| 115 | `next` accepts the plain reply to this particular request. The reply's ordinary data type depends on `q.value.data`. |
| 116 | Given such a reply, `next` returns the remaining interactive computation. |
| 117 | `OracleComp.queryBind q next` means issue request `q`, then run the continuation chosen by its reply. |
| 118 | The whole program is algebraic exactly when the request is valid now and every continuation is algebraic after adding its reply inputs. |

This theorem exposes the recursive condition in a convenient form for certifying programs.
Unlike the internal recursion argument described above, `next` here is the actual
program continuation. Both sides use the same received-before-output rule.

## Adversary

**In plain English:** Package an interactive program with a proof that it obeys the explanation rule for every initial message and every reply path. The program and its algebraicity certificate are separate fields.

[Source line 121](../AlgebraicGroupModel/Interaction.lean#L121). Definition, including its body.

```lean
121 | structure Adversary (F : Type) (G : Tag → Type) (Input Query : Type) (Reply : Query → Type) (Result : Type)
122 |     [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)] where
123 |   main : Message Input G → OracleComp (explainedSpec F G Query Reply) (Explained F Result G)
124 |   algebraic : ∀ input, IsAlgebraic input.groups (main input)
```

| Line | Explanation |
| --- | --- |
| 121 | Declare a record parameterized by coefficients `F`, group family `G`, ordinary initial data `Input`, request data `Query`, request-dependent reply data `Reply`, and ordinary final data `Result`. `Tag` is inferred from `G`. |
| 122 | Require the scalar-zero and per-sort algebraic operations. `where` begins the record's fields. |
| 123 | `main` receives one initial `Message` and returns an interactive program. `OracleComp` is applied to two arguments: the oracle interface and the final result type. |
| 124 | `algebraic` is evidence that `main input` satisfies `IsAlgebraic` for every initial message, starting from exactly `input.groups`. |

Read the type of `main` in stages:

```text
Message Input G
  -> a program with interface (explainedSpec F G Query Reply)
  -> eventually an output of type (Explained F Result G)
```

The second arrow is explanatory, not an extra Lean function argument.
`A.main input` describes the program; it does not execute the game handler.
There is one program for all group sorts, so later requests in one sort may depend on earlier
replies in another.

The certificate covers all initial messages of this type, not only keys sampled by a chosen
game. Games with restricted initial shapes can define explicit rejection on other shapes.
This record does not claim that `main` is efficient or that the supplied data hides no secrets.

## Adversary.run

**In plain English:** Execute a certified adversary against the game's plain oracle handler.
Start with the initial message's group lists, append incoming group replies, and return the
final explained output together with all received inputs. This is the only execution API.

[Source line 127](../AlgebraicGroupModel/Interaction.lean#L127). Definition, including its body.

```lean
127 | def Adversary.run {Input : Type} {N : Type → Type} [Monad N]
128 |     (A : Adversary F G Input Query Reply Result)
129 |     (impl : QueryImpl (plainSpec G Query Reply) N) (input : Message Input G) :
130 |     N (Explained F Result G × Groups G) :=
131 |   (simulateQ (fun q => StateT.mk fun basis => do
132 |     let reply ← impl q.value
133 |     pure (reply, extend basis reply.groups)) (A.main input)).run input.groups
```

| Line | Explanation |
| --- | --- |
| 127 | Define a method on certified adversaries. `Input` is the initial ordinary-data type. `N : Type → Type` chooses the target computation type, and `[Monad N]` supplies sequencing and return operations. |
| 128 | `A` contains both the interactive program and its all-input, all-reply-path algebraicity certificate. |
| 129 | `impl` implements the plain oracle interface in `N`. It receives actual request data and group arguments, not coefficient vectors. `input` supplies both ordinary initial data and the initial group lists. |
| 130 | Execution returns an effectful pair: the final explained output, then the final received-input lists. |
| 131 | `simulateQ` interprets the program using a stateful handler. `StateT.mk fun basis => ...` describes how each request runs with the received-input lists available at that point. |
| 132 | Call the plain handler with `q.value`, dropping the request's coefficient vectors but preserving its ordinary data and actual group values. The left arrow waits for that handler's reply. |
| 133 | Give the reply to the program and append its group values to the state. Interpret exactly `A.main input`, starting with exactly `input.groups`. |

Read the result type in stages:

```text
Explained F Result G                  final output, including explanations
Groups G                              final received-input lists
Explained F Result G × Groups G       the pair of those values
N (Explained F Result G × Groups G)   that pair inside the chosen computation type
```

For `N := Id`, execution is deterministic. A state monad can also record a query log;
`OracleComp ambient` allows the handler itself to make further oracle calls.

The runner uses the scalar-zero and per-sort operation instances declared at line 101
because its argument is a certified `Adversary`. It does not compute representations or
check them at runtime. The certificate is a proof, not an executable validation procedure;
the next theorem connects that certificate to the result of this interpreter.

There is no separate raw runner or raw-runner soundness theorem. Execution is defined
directly here, with the initial program and initial lists selected from the same message.
On a return, the lists stay unchanged. On a query, the handler runs first, then its reply's
group values extend the lists before the continuation executes. Outgoing values are never
inserted into these lists.

## Adversary.run_valid

**In plain English:** Every structurally reachable result of running a certified adversary
has valid final explanations over the inputs recorded in that result. The adversary already
carries the algebraicity proof, so callers need not supply it again.

[Source line 136](../AlgebraicGroupModel/Interaction.lean#L136). Theorem statement only.

```lean
136 | theorem Adversary.run_valid {Input I : Type} {ambient : OracleSpec I}
137 |     (A : Adversary F G Input Query Reply Result)
138 |     (impl : QueryImpl (plainSpec G Query Reply) (OracleComp ambient)) (input : Message Input G)
139 |     (z : Explained F Result G × Groups G) (hz : z ∈ support (A.run impl input)) :
140 |     z.1.Valid z.2
```

| Line | Explanation |
| --- | --- |
| 136 | Choose the initial ordinary-data type `Input` and an ambient oracle interface. `I` indexes this lower-level interface; `ambient` supplies its reply types. |
| 137 | Take a certified adversary, containing both its program and its algebraicity proof. |
| 138 | Choose its plain handler and actual initial message. The handler produces `OracleComp ambient` computations and can itself make ambient oracle calls. |
| 139 | `z` is a pair of final explained output and received-input lists. `hz` assumes it belongs to the structural support of this execution. |
| 140 | Conclude that the output `z.1` is valid over the actual received lists `z.2`. There is no separate algebraicity argument because `A.algebraic input` supplies it. |

Here `support` means **structurally reachable outputs** of an oracle program. It is not a
claim that a particular probability distribution gives each such output positive probability.
No distribution, field sampler, or numerical security bound occurs in this statement.

The theorem does not assert that an output exists or that execution has a bounded runtime.
Request validity is already required recursively by `A.algebraic`; the conclusion establishes
validity of the final result using the lists recorded by execution.

This is the certified-runner soundness guarantee, proved directly for this interpreter.
It is not an unforgeability theorem or a correctness assertion about the game handler's
cryptographic behavior. Proof bodies remain outside this guide.

## Build and Repository Files

### Public Import

[`AlgebraicGroupModel.lean`](../AlgebraicGroupModel.lean#L1) contains one line:

```lean
1 | import AlgebraicGroupModel.Interaction
```

This is the convenient whole-library import. There is only one implementation module.
Token/output adapters, signature games, and their execution-equivalence proofs live in
[`zksecurity/bls-lean`](https://github.com/zksecurity/bls-lean), not in this repository.

### Lake Configuration

[`lakefile.lean`](../lakefile.lean) describes the build, not the security model.

| Source line | Meaning |
| --- | --- |
| [1](../lakefile.lean#L1) | Import Lake's build configuration API. |
| [2](../lakefile.lean#L2) | Open its configuration syntax. |
| [4](../lakefile.lean#L4) | Declare package `lean-agm`; the quoted identifier permits its hyphen. |
| [5](../lakefile.lean#L5) | Package description. |
| [6](../lakefile.lean#L6) | License metadata. |
| [7](../lakefile.lean#L7) | Begin the array of compiler options. |
| [8](../lakefile.lean#L8) | Disable introducing undeclared identifiers automatically as implicit parameters. Explicitly declared implicit arguments are still inferred normally. |
| [9](../lakefile.lean#L9) | Also disable the relaxed form of that automatic generalization. |
| [10](../lakefile.lean#L10) | End the array. |
| [12](../lakefile.lean#L12) | Declare VCVio as a Git dependency. |
| [13](../lakefile.lean#L13) | Supply its repository URL; `@` introduces the revision. |
| [14](../lakefile.lean#L14) | Pin an exact commit, not a moving branch. |
| [16](../lakefile.lean#L16) | Mark the next library as the default build target. |
| [17](../lakefile.lean#L17) | Declare the public `AlgebraicGroupModel` library. |
| [19](../lakefile.lean#L19) | Declare the separate test library. |
| [20](../lakefile.lean#L20) | Include modules below the `AGMTest` namespace. |
| [21](../lakefile.lean#L21) | Suppress warnings about test files without a `module` header importing module-system dependencies. This does not disable proof checking. |

### Remaining Files

- [`lean-toolchain`](../lean-toolchain) pins Lean to `leanprover/lean4:v4.34.0`.
- [`lake-manifest.json`](../lake-manifest.json) is the generated dependency lockfile. It records resolved revisions, locations, and configuration metadata, including transitive dependencies. Its entries are not extra security hypotheses.
- [`.github/workflows/lean.yml`](../.github/workflows/lean.yml) runs on pushes, pull requests, and manual dispatch. It grants read-only repository-content permission, uses pinned checkout/setup actions, disables their automatic build/cache steps, then explicitly runs `lake exe cache get` and `lake build AlgebraicGroupModel AGMTest`.
- [`.gitignore`](../.gitignore) excludes the local Lake build/dependency directory, compiled `.olean` files, and macOS `.DS_Store` files.
- [`LICENSE`](../LICENSE) contains the Apache-2.0 license.
- [`README.md`](../README.md) is the short entry point. This page supplies the detailed walkthrough instead of enlarging it.

To check the library and its tests:

```sh
lake build AlgebraicGroupModel AGMTest
```

## Review Checklist

- [ ] Distinguish a type constructor, a fully applied type, and a value of that type.
- [ ] Expand `Groups G` and explain why the return type depends on the label.
- [ ] Explain why `Message` has no coefficients and `Explained` contains claims but no proof.
- [ ] Identify both independent length requirements in `Explained.Valid`.
- [ ] Identify the minimal algebraic assumptions without silently assuming field or module laws.
- [ ] Map the two arguments of `OracleComp` to the interface and final result type.
- [ ] Distinguish explained outgoing requests from plain incoming replies.
- [ ] Find the line that checks a request before extending the basis.
- [ ] Explain why the certificate covers all well-typed reply continuations, not just one handler's paths.
- [ ] Explain how ordinary data may affect coefficients without becoming a basis element.
- [ ] Explain why certified execution needs no runtime validation: its input includes an algebraicity proof, and the soundness theorem connects that proof to the result.
- [ ] Distinguish structural support from positive probability.
- [ ] State what remains outside this layer: efficiency, cryptographic hardness, and faithful game inputs.
The separate [test review](review-tests.md) covers concrete executions, rejected explanations,
and the axiom guards.
