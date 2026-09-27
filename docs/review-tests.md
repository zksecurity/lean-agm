# AGM Review: Tests and Guards

This separate walkthrough covers the test fixtures, assertion statements, and build-time
guards. For the definitions and public theorem statements, start with the
[main review](review.md). These tests exercise the same API; they are not a second implementation.

**Proof bodies and proof-valued fields are omitted.** Each quotation uses the actual source
line numbers, written as `number | code`. These numbers are reading annotations, not Lean syntax.
Line tables may also describe omitted proof fields without showing their proofs.

Source quotations and line numbers refer to the source files alongside this guide.

## Reading Route

1. [One-group tests](#one-group-tests)
2. [Two-group tests](#two-group-tests)
3. [Axiom guards](#axiom-guards)
4. [Review checklist](#review-checklist)

## One-Group Tests

[`AGMTest/Interaction.lean`](../AGMTest/Interaction.lean). This file uses `Tag := Unit`. Lines 1-4 import the API and axiom tools and open their names.
Lines 6 and 126 delimit the test namespace. Private fixtures are not additional public APIs.

Proof-valued `algebraic` fields are described, but their implementations are omitted.
All execution examples use certified `Adversary.run`; invalid programs are tested as
negated validity or algebraicity propositions, not executed through an unchecked API.

### One-Group Labels

**In plain English:** Use one group sort with natural-number arithmetic, so the expected representations can be checked with small concrete numbers.

[Source line 8](../AGMTest/Interaction.lean#L8).

```lean
8 | private abbrev Group := fun _ : Unit => Nat
```

| Line | Explanation |
| --- | --- |
| 8 | The only label is `()`; the carrier is `Nat`. These arithmetic test values are not a cryptographic group. |

### No-Oracle Adversary

**In plain English:** Build a certified adversary that cannot make any queries and returns the sum of its initial group inputs.

[Source line 11](../AGMTest/Interaction.lean#L11).

```lean
11 | private def noOracles : Adversary Nat Group Unit Empty (fun _ => Unit) Unit where
12 |   main input := pure (Explained.ofVectors input.groups () (fun _ => [fun _ => 1]))
```

| Line | Explanation |
| --- | --- |
| 11 | Coefficients and group values are natural numbers; input and result payloads are `Unit`. `Query := Empty` makes requests impossible. |
| 12 | Return one value with coefficient 1 on each input. |
| 13 | The omitted proof field certifies that construction for every initial input. |

### Scalar-Reply Adversary

**In plain English:** Make later requests and final coefficients depend on earlier ordinary reply data. This tests adaptivity through data, not only through newly received group elements.

[Source line 19](../AGMTest/Interaction.lean#L19).

```lean
19 | private def measured : Adversary Nat Group Nat Nat (fun _ => Nat) Nat where
20 |   main input := do
21 |     let first ← (explainedSpec Nat Group Nat (fun _ => Nat)).query ⟨⟨input.data, fun _ => []⟩, fun _ => []⟩
22 |     let second ← (explainedSpec Nat Group Nat (fun _ => Nat)).query
23 |       ⟨⟨input.data + first.data, fun _ => []⟩, fun _ => []⟩
24 |     return Explained.ofVectors (extend (extend input.groups first.groups) second.groups)
25 |       second.data (fun _ => [fun _ => first.data])
```

| Line | Explanation |
| --- | --- |
| 19 | Initial, request, ordinary reply, and final data are natural numbers. |
| 20 | Start the interactive program. |
| 21 | Request the initial ordinary payload, with no group arguments or vectors. |
| 22 | Make a second request after receiving the first reply. |
| 23 | Its payload is initial data plus the first reply's data; group arguments remain empty. |
| 24 | Extend the basis with both replies before constructing the final output. |
| 25 | Return the second reply's data and use the first reply's data as every coefficient. |
| 26 | The omitted algebraicity proof covers every reply shape, including replies that carry group values. |

### One-Group Oracle Interface

**In plain English:** Choose a one-sort interface with natural-number request data and no informative ordinary reply data. Replies can still supply new group elements.

[Source line 34](../AGMTest/Interaction.lean#L34).

```lean
34 | private abbrev spec := explainedSpec Nat Group Nat (fun _ => Unit)
```

| Line | Explanation |
| --- | --- |
| 34 | Natural request data and `Unit` reply data. Replies may still contain group values. |

### One-Group Adaptive Program

**In plain English:** Make two requests in sequence, using the first reply to construct the second request, then return a combination of all received inputs.

[Source line 37](../AGMTest/Interaction.lean#L37).

```lean
37 | private def adaptive (inputs : Groups Group) : OracleComp spec (Explained Nat String Group) := do
38 |   let first ← spec.query (Explained.ofVectors inputs 0 (fun _ => [fun _ => 1]))
39 |   let basis := extend inputs first.groups
40 |   let second ← spec.query (Explained.ofVectors basis (first.groups ()).length
41 |     (fun _ => [fun _ => 1, fun _ => 0]))
42 |   return Explained.ofVectors (extend basis second.groups) "done" (fun _ => [fun _ => 1])
```

| Line | Explanation |
| --- | --- |
| 37 | Accept any current basis; the final ordinary payload is a string. |
| 38 | First request: data 0, with one all-ones linear combination of received values. |
| 39 | Extend with the first reply's inputs. |
| 40 | The second request's data is the number of group inputs in the first reply. |
| 41 | Send two group values, constructed using all-ones and all-zeros vectors. |
| 42 | Extend with the second reply; return `"done"` and an all-ones combination. |

### One-Group Program Certificate

**In plain English:** Certify the adaptive program for every initial basis and every possible reply. The claim is stronger than the concrete executions checked below.

[Source line 44](../AGMTest/Interaction.lean#L44).

```lean
44 | private theorem adaptive_algebraic (inputs : Groups Group) : IsAlgebraic inputs (adaptive inputs)
```

| Line | Explanation |
| --- | --- |
| 44 | For every starting basis, this adaptive program satisfies the all-reply-path condition. Proof omitted. |

### One-Group Certified Wrapper

**In plain English:** Expose the adaptive program through the same certified `Adversary` interface that applications use.

[Source line 53](../AGMTest/Interaction.lean#L53).

```lean
53 | private def adversary : Adversary Nat Group Unit Nat (fun _ => Unit) String where
54 |   main input := adaptive input.groups
```

| Line | Explanation |
| --- | --- |
| 53 | Package the program into the generic adversary, with ordinary initial data `Unit`. |
| 54 | Pass the actual initial group's lists to the program. |
| 55 | The omitted proof field uses the preceding certificate for those same lists. |

### One-Group Handler

**In plain English:** Provide a deterministic test handler that logs requests and supplies the values 7 or 11. The log lets the tests inspect what was sent and in what order.

[Source line 58](../AGMTest/Interaction.lean#L58).

```lean
58 | private def impl : QueryImpl (plainSpec Group Nat (fun _ => Unit))
59 |     (StateM (List (Message Nat Group))) := fun q => do
60 |   modify (· ++ [q])
61 |   return ⟨(), fun _ => if q.data = 0 then [7] else [11]⟩
```

| Line | Explanation |
| --- | --- |
| 58 | Implement the plain request/reply interface. |
| 59 | Execute with a state containing the log of plain request messages. |
| 60 | Append the request to that log. |
| 61 | Reply with `[7]` for ordinary request data 0, otherwise `[11]`. Replies have no explanations. |

### Check: No queries

**In plain English:** Inputs `[2, 3]` produce `[5]`. `N := Id` means deterministic execution without extra effects. `nomatch q.data` handles the impossible `Empty` request. `.1` selects the output instead of the recorded basis.

[Source line 15](../AGMTest/Interaction.lean#L15). Statement only.

```lean
15 | example : (noOracles.run (N := Id) (fun q => nomatch q.data) ⟨(), fun _ => [2, 3]⟩).1.value =
16 |     ⟨(), fun _ => [5]⟩
```


### Check: Scalar-dependent requests

**In plain English:** A handler returning request data plus 1 gives replies 3 and 6 from initial data 2. Coefficient 3 over `[4, 5]` yields 27, with final payload 6.

[Source line 31](../AGMTest/Interaction.lean#L31). Statement only.

```lean
31 | example : (measured.run (N := Id) (fun q => pure ⟨q.data + 1, fun _ => []⟩)
32 |     ⟨2, fun _ => [4, 5]⟩).1.value = ⟨6, fun _ => [27]⟩
```


### Check: Final adaptive value

**In plain English:** From `[2, 3]`, replies `[7]` and `[11]` lead to `"done"` with `[23]`. The outer `.run []` initializes the handler's log; `.1.1` selects the explained output inside the runner result.

[Source line 63](../AGMTest/Interaction.lean#L63). Statement only.

```lean
63 | example : ((adversary.run impl ⟨(), fun _ => [2, 3]⟩).run []).1.1.value =
64 |     ⟨"done", fun _ => [23]⟩
```


### Check: Only replies accumulate

**In plain English:** The received list is exactly `[2, 3, 7, 11]`. Outgoing values 5, 12, and 0 are not inserted.

[Source line 67](../AGMTest/Interaction.lean#L67). Statement only.

```lean
67 | example : ((adversary.run impl ⟨(), fun _ => [2, 3]⟩).run []).1.2 () = [2, 3, 7, 11]
```


### Check: Adaptive request log

**In plain English:** The requests are data 0 with `[5]`, then data 1 with `[12, 0]`. The outer `.2` selects the handler's log.

[Source line 69](../AGMTest/Interaction.lean#L69). Statement only.

```lean
69 | example : ((adversary.run impl ⟨(), fun _ => [2, 3]⟩).run []).2 =
70 |     [⟨0, fun _ => [5]⟩, ⟨1, fun _ => [12, 0]⟩]
```


### Check: Incorrect reconstruction

**In plain English:** Coefficient `[1]` over `[2]` cannot explain 7. This negates a validity proposition; it is not a runtime error.

[Source line 73](../AGMTest/Interaction.lean#L73). Statement only.

```lean
73 | example : ¬ (⟨⟨(), fun _ => [7]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group).Valid (fun _ => [2])
```


### Check: Missing output vector

**In plain English:** Two outgoing values require two vectors, even when both values are equal.

[Source line 75](../AGMTest/Interaction.lean#L75). Statement only.

```lean
75 | example : ¬ (⟨⟨(), fun _ => [2, 2]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group).Valid (fun _ => [2])
```


### Check: Short vector

**In plain English:** Two received inputs require two coefficients, even if one coefficient reconstructs the requested value.

[Source line 77](../AGMTest/Interaction.lean#L77). Statement only.

```lean
77 | example : ¬ (⟨⟨(), fun _ => [2]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group).Valid (fun _ => [2, 3])
```


### Check: Long vector

**In plain English:** One received input does not permit two coefficients, even when the extra coefficient is zero.

[Source line 79](../AGMTest/Interaction.lean#L79). Statement only.

```lean
79 | example : ¬ (⟨⟨(), fun _ => [2]⟩, fun _ => [[1, 0]]⟩ : Explained Nat Unit Group).Valid (fun _ => [2])
```


### Check: No outgoing groups

**In plain English:** A string request with no group arguments and no vectors is valid over an empty basis. This permits a hash-style request shape without implementing or assuming hashing.

[Source line 83](../AGMTest/Interaction.lean#L83). Statement only.

```lean
83 | example : (⟨⟨"hash this message", fun _ => []⟩, fun _ => []⟩ : Explained Nat String Group).Valid (fun _ => [])
```


### Check: Fresh replies

**In plain English:** For any carrier with the stated operations, a group-free request can receive fresh inputs and return their all-ones evaluation with a valid explanation. `[One F]` allows writing 1; it does not add scalar-action laws.

[Source line 87](../AGMTest/Interaction.lean#L87). Statement only.

```lean
87 | example {F G : Type} [Zero F] [One F] [AddMonoid G] [SMul F G] :
88 |     IsAlgebraic (Reply := fun _ : String => Unit) (fun _ : Unit => ([] : List G))
89 |       (OracleComp.queryBind (⟨⟨"hash", fun _ => []⟩, fun _ => []⟩ : Explained F String (fun _ : Unit => G))
90 |         (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1]))))
```


### Check: Repeated values

**In plain English:** Two occurrences of 2 have independent positions. Coefficients `[2, 3]` reconstruct 10.

[Source line 97](../AGMTest/Interaction.lean#L97). Statement only.

```lean
97 | example : (⟨⟨(), fun _ => [10]⟩, fun _ => [[2, 3]]⟩ : Explained Nat Unit Group).Valid (fun _ => [2, 2])
```


### Check: Future inputs forbidden

**In plain English:** Sending 7 from an empty basis is invalid, even though the continuation constructs valid outputs from later replies.

[Source line 101](../AGMTest/Interaction.lean#L101). Statement only.

```lean
101 | example : ¬ IsAlgebraic (fun _ : Unit => ([] : List Nat))
102 |     (OracleComp.queryBind (spec := spec) (⟨⟨0, fun _ => [7]⟩, fun _ => [[]]⟩ : Explained Nat Nat Group)
103 |       (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1]))))
```


### Check: Final outputs checked

**In plain English:** Returning 7 with coefficient `[1]` over `[2]` is not algebraic, even without queries.

[Source line 110](../AGMTest/Interaction.lean#L110). Statement only.

```lean
110 | example : ¬ IsAlgebraic (Reply := fun _ : Nat => Unit) (fun _ => [2])
111 |     (pure (⟨⟨(), fun _ => [7]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group))
```


## Two-Group Tests

[`AGMTest/MultiGroup.lean`](../AGMTest/MultiGroup.lean). This is a test file, **not a second implementation**. Line 1 imports the same `Interaction`;
line 3 opens its names; lines 5 and 120 delimit the test namespace. The fixtures test both
different carrier types and different labels with identical carrier types.

Proof-valued `algebraic` fields are described, but their implementations are omitted.

### Two-Group Labels

**In plain English:** Use two labels with different carriers: natural numbers for one sort and integers for the other. Both are handled by the same public interface.

[Source line 8](../AGMTest/MultiGroup.lean#L8).

```lean
8 | private abbrev Group : Bool → Type
9 |   | false => Nat
10 |   | true => Int
```

| Line | Explanation |
| --- | --- |
| 8 | Use `Bool` as the group-label type. |
| 9 | Label `false` has carrier `Nat`. |
| 10 | Label `true` has carrier `Int`, exercising genuinely different types. |

### Per-Sort Addition

**In plain English:** Supply addition separately for the two carriers, allowing the shared evaluator to add values of either sort.

[Source line 12](../AGMTest/MultiGroup.lean#L12).

```lean
12 | private instance (s : Bool) : AddMonoid (Group s)
```

| Line | Explanation |
| --- | --- |
| 12 | Supply an additive-monoid instance for every label. The omitted body selects the existing natural-number or integer structure. |

### Per-Sort Scalar Multiplication

**In plain English:** Supply natural-number scalar multiplication for each carrier, while keeping their group values in separate sorts.

[Source line 15](../AGMTest/MultiGroup.lean#L15).

```lean
15 | private instance (s : Bool) : SMul Nat (Group s)
```

| Line | Explanation |
| --- | --- |
| 15 | Supply natural-number scalar multiplication in both carriers. Instance-construction body omitted. |

### Initial Two-Group Inputs

**In plain English:** Start the natural-number sort with 2 and 3, and the integer sort with 10. These separate lists are the initial inputs for the following executions.

[Source line 18](../AGMTest/MultiGroup.lean#L18).

```lean
18 | private def initial : Groups Group
19 |   | false => [2, 3]
20 |   | true => [10]
```

| Line | Explanation |
| --- | --- |
| 18 | Define a collection of received-input lists. |
| 19 | The natural sort starts with `[2, 3]`. |
| 20 | The integer sort starts with `[10]`. |

### Two-Group Oracle Interface

**In plain English:** Choose one shared request stream for both sorts, with natural-number ordinary request and reply data.

[Source line 22](../AGMTest/MultiGroup.lean#L22).

```lean
22 | private abbrev spec := explainedSpec Nat Group Nat (fun _ => Nat)
```

| Line | Explanation |
| --- | --- |
| 22 | Natural coefficients, the two-carrier family, and natural ordinary request/reply data. |

### Two-Group Adaptive Program

**In plain English:** Make two requests across both sorts. Later coefficients depend on earlier reply data and even on the other sort's reply length, but each value is still reconstructed from inputs of its own sort.

[Source line 24](../AGMTest/MultiGroup.lean#L24).

```lean
24 | private def adaptive (inputs : Groups Group) : OracleComp spec (Explained Nat Nat Group) := do
25 |   let first ← spec.query (Explained.ofVectors inputs 0 (fun _ => [fun _ => 1]))
26 |   let basis := extend inputs first.groups
27 |   let second ← spec.query (Explained.ofVectors basis first.data
28 |     (fun s => [fun _ => if s then (first.groups false).length else first.data]))
29 |   return Explained.ofVectors (extend basis second.groups) second.data (fun _ => [fun _ => 1])
```

| Line | Explanation |
| --- | --- |
| 24 | Accept any two-group basis; return an explained natural-number payload. |
| 25 | First request: data 0 and an all-ones combination at each sort. |
| 26 | Extend each sort's basis with the first reply. |
| 27 | Use the first reply's ordinary data as the second request's data. |
| 28 | The integer sort's coefficient is the natural reply-list length. The natural sort's coefficient is the reply data. This is cross-sort adaptive dependence, not a cross-sort representation. |
| 29 | Extend with the second reply; return its data and an all-ones combination at each sort. |

### Two-Group Certified Wrapper

**In plain English:** Package the two-sort program with its all-input, all-reply-path algebraicity certificate.

[Source line 32](../AGMTest/MultiGroup.lean#L32).

```lean
32 | private def adversary : Adversary Nat Group Unit Nat (fun _ => Nat) Nat where
33 |   main input := adaptive input.groups
```

| Line | Explanation |
| --- | --- |
| 32 | Use the same `Interaction.Adversary` type as the one-group tests. |
| 33 | Pass the actual initial lists to the program. |
| 34 | The omitted proof field certifies all initial inputs and reply paths. |

### First Two-Group Reply

**In plain English:** Define the first handler reply: ordinary data 3, one new natural-number input, and two new integer inputs.

[Source line 39](../AGMTest/MultiGroup.lean#L39).

```lean
39 | private def firstReply : Message Nat Group :=
40 |   ⟨3, fun s => match s with | false => [7] | true => [13, 17]⟩
```

| Line | Explanation |
| --- | --- |
| 39 | Define a plain message with natural ordinary data. |
| 40 | Data 3, natural inputs `[7]`, and integer inputs `[13, 17]`. No explanations. |

### Second Two-Group Reply

**In plain English:** Define the second handler reply: ordinary data 4, no new natural-number inputs, and one new integer input.

[Source line 42](../AGMTest/MultiGroup.lean#L42).

```lean
42 | private def secondReply : Message Nat Group :=
43 |   ⟨4, fun s => match s with | false => [] | true => [19]⟩
```

| Line | Explanation |
| --- | --- |
| 42 | Define another plain reply. |
| 43 | Data 4, no new natural inputs, and integer input `[19]`. |

### Two-Group Handler

**In plain English:** Log each plain request and choose one of the two fixed replies from its ordinary request data.

[Source line 45](../AGMTest/MultiGroup.lean#L45).

```lean
45 | private def impl : QueryImpl (plainSpec Group Nat (fun _ => Nat))
46 |     (StateM (List (Message Nat Group))) := fun q => do
47 |   modify (· ++ [q])
48 |   return if q.data = 0 then firstReply else secondReply
```

| Line | Explanation |
| --- | --- |
| 45 | Implement the two-group plain interface. |
| 46 | The state monad stores a request log. |
| 47 | Record the current request. |
| 48 | Return `firstReply` for data 0 and `secondReply` otherwise. |

### Readable Test Output

**In plain English:** Project a message into an ordinary tuple so test assertions can display its data and both group lists directly.

[Source line 50](../AGMTest/MultiGroup.lean#L50).

```lean
50 | private def inspect (message : Message Nat Group) : Nat × List Nat × List Int :=
51 |   (message.data, message.groups false, message.groups true)
```

| Line | Explanation |
| --- | --- |
| 50 | Convert a message into a triple suitable for comparing both sorts. |
| 51 | Select the ordinary data, natural list, and integer list. |

### Wrong-Sort Claim

**In plain English:** Construct a deliberately invalid explanation: a value received in one sort is claimed in another. Using the same carrier type for both sorts must not erase that distinction.

[Source line 66](../AGMTest/MultiGroup.lean#L66).

```lean
66 | private def wrongSort : Explained Nat Unit (fun _ : Bool => Nat) :=
67 |   ⟨⟨(), fun s => if s then [7] else []⟩, fun s => if s then [[]] else []⟩
```

| Line | Explanation |
| --- | --- |
| 66 | Both labels use `Nat`, so isolation cannot depend only on different carrier types. |
| 67 | Claim output `[7]` at `true` with an empty vector `[[]]`; send no output or vector at `false`. |

### Check: Final two-group output

**In plain English:** Final payload 4, natural output `[12]`, and integer output `[59]`. `inspect` makes both projections explicit.

[Source line 53](../AGMTest/MultiGroup.lean#L53). Statement only.

```lean
53 | example : inspect ((adversary.run impl ⟨(), initial⟩).run []).1.1.value =
54 |     (4, [12], [59])
```


### Check: Separate final bases

**In plain English:** The natural list is `[2, 3, 7]`; the integer list is `[10, 13, 17, 19]`. Empty replies add nothing; outgoing values do not enter either list.

[Source line 57](../AGMTest/MultiGroup.lean#L57). Statement only.

```lean
57 | example : ((adversary.run impl ⟨(), initial⟩).run []).1.2 =
58 |     (fun s => match s with | false => [2, 3, 7] | true => [10, 13, 17, 19])
```


### Check: Cross-sort adaptive requests

**In plain English:** The second natural coefficient is reply data 3, giving `3 * 12 = 36`. The second integer coefficient is the natural reply-list length 1, giving 40.

[Source line 62](../AGMTest/MultiGroup.lean#L62). Statement only.

```lean
62 | example : ((adversary.run impl ⟨(), initial⟩).run []).2.map inspect =
63 |     [(0, [5], [10]), (3, [36], [40])]
```


### Check: Same-carrier isolation

**In plain English:** Receiving 7 at `false` does not justify outputting it at `true`, even with the same carrier type.

[Source line 69](../AGMTest/MultiGroup.lean#L69). Statement only.

```lean
69 | example : ¬ wrongSort.Valid (fun s => if s then [] else [7])
```


### Check: Same-length isolation

**In plain English:** Both bases have length one, but `[1]` over the `true` basis `[7]` cannot explain 2.

[Source line 75](../AGMTest/MultiGroup.lean#L75). Statement only.

```lean
75 | example : ¬ (⟨⟨(), fun s => if s then [2] else []⟩,
76 |     fun s => if s then [[1]] else []⟩ : Explained Nat Unit (fun _ : Bool => Nat)).Valid
77 |       (fun s => if s then [7] else [2])
```


### Check: Per-sort vector length

**In plain English:** The `true` basis has one input, so two coefficients are invalid even when the other sort has two inputs.

[Source line 83](../AGMTest/MultiGroup.lean#L83). Statement only.

```lean
83 | example : ¬ (⟨⟨(), fun s => if s then [7] else []⟩,
84 |     fun s => if s then [[0, 1]] else []⟩ : Explained Nat Unit (fun _ : Bool => Nat)).Valid
85 |       (fun s => if s then [7] else [2, 3])
```


### Check: Missing final witnesses

**In plain English:** Every final group value requires a vector. A matching received value alone is insufficient.

[Source line 91](../AGMTest/MultiGroup.lean#L91). Statement only.

```lean
91 | example : ¬ IsAlgebraic (Reply := fun _ : Unit => Unit) (fun _ : Bool => [7])
92 |     (pure (⟨⟨(), fun _ => [7]⟩, fun _ => []⟩ : Explained Nat Unit (fun _ : Bool => Nat)))
```


### Check: Fresh values in all sorts

**In plain English:** For any label type and group family, an empty-group request may receive new inputs at any sort. Its continuation can construct valid all-ones evaluations at each sort.

[Source line 98](../AGMTest/MultiGroup.lean#L98). Statement only.

```lean
98 | example {Tag F : Type} {G : Tag → Type} [Zero F] [One F]
99 |     [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)] :
100 |     IsAlgebraic (Reply := fun _ : String => Unit) (fun _ => ([] : List (G _)))
101 |       (OracleComp.queryBind (⟨⟨"hash", fun _ => []⟩, fun _ => []⟩ : Explained F String G)
102 |         (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1]))))
```


### Check: Future values cannot repair a query

**In plain English:** The current basis is empty in both sorts; `wrongSort` is already invalid before its continuation receives any values.

[Source line 107](../AGMTest/MultiGroup.lean#L107). Statement only.

```lean
107 | example : ¬ IsAlgebraic (fun _ : Bool => ([] : List Nat))
108 |     (OracleComp.queryBind (spec := explainedSpec Nat (fun _ : Bool => Nat) Unit (fun _ => Unit))
109 |       wrongSort (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1]))))
```


### Check: Repeated positions in each sort

**In plain English:** In each sort, coefficients `[2, 3]` over `[2, 2]` reconstruct 10. The received lists are not sets.

[Source line 115](../AGMTest/MultiGroup.lean#L115). Statement only.

```lean
115 | example : (⟨⟨(), fun _ => [10]⟩, fun _ => [[2, 3]]⟩ :
116 |     Explained Nat Unit (fun _ : Bool => Nat)).Valid (fun _ => [2, 2])
```


## Axiom Guards

These are build-time checks, not theorem proof walkthroughs.

### Whole-Library Guard

**In plain English:** Fail the build if a removed interface reappears or a public declaration depends on an unapproved axiom, including an admitted proof. This protects the library boundary and proof completeness, not the faithfulness of the model to a paper.

[`AGMTest/Axioms.lean`](../AGMTest/Axioms.lean) checks the public namespace.

| Source line | Meaning |
| --- | --- |
| [1](../AGMTest/Axioms.lean#L1) | Import the complete public library. |
| [2](../AGMTest/Axioms.lean#L2) | Import the tool that collects axioms used by declarations and their dependencies. |
| [3](../AGMTest/Axioms.lean#L3) | Import command-elaboration tools. |
| [5](../AGMTest/Axioms.lean#L5) | Document the intended standard-axiom boundary. |
| [7](../AGMTest/Axioms.lean#L7) | Open Lean's metaprogramming namespaces locally. |
| [8](../AGMTest/Axioms.lean#L8) | Run the check during compilation, with term-elaboration capabilities. |
| [9](../AGMTest/Axioms.lean#L9) | Begin a list of removed adversary interfaces that must not reappear. |
| [10](../AGMTest/Axioms.lean#L10) | Include token-output and transcript helpers moved to the signature consumer. |
| [11](../AGMTest/Axioms.lean#L11) | Include the removed generic erasure and shared-core runners. |
| [12](../AGMTest/Axioms.lean#L12) | Reject the removed raw runner and its return equation. |
| [13](../AGMTest/Axioms.lean#L13) | Reject its query equation and separate soundness theorem. Certified execution is the only runner API. |
| [14](../AGMTest/Axioms.lean#L14) | Check whether each forbidden name exists in the current environment. |
| [15](../AGMTest/Axioms.lean#L15) | Fail compilation if one exists. |
| [16](../AGMTest/Axioms.lean#L16) | Visit all declarations in the current environment. |
| [17](../AGMTest/Axioms.lean#L17) | Restrict the scan to names starting with `AlgebraicGroupModel`. |
| [18](../AGMTest/Axioms.lean#L18) | Collect each declaration's axiom dependencies. |
| [19](../AGMTest/Axioms.lean#L19) | Allow only `propext`, `Classical.choice`, and `Quot.sound`. |
| [20](../AGMTest/Axioms.lean#L20) | Fail on other axioms, including an admitted proof's `sorryAx`. |

`propext` is propositional extensionality; `Classical.choice` is classical choice;
`Quot.sound` supports identifying related values in quotients.
A declaration may use a **subset** of this allowed set; it need not use all three.
This guard does not prove that a model matches a paper or that a cryptographic protocol is secure.

### Focused Guard

**In plain English:** Check the central validity theorems for unapproved axioms and keep signature-specific and pairing infrastructure out of this generic test environment.

At [lines 116-124 of the one-group tests](../AGMTest/Interaction.lean#L116):

- Line 116 opens metaprogramming names locally.
- Line 117 starts a compile-time check.
- Line 118 selects `Adversary.run_valid` and `Explained.valid_ofVectors`.
- Lines 119-121 collect their axiom dependencies and enforce the same allowed set.
- Lines 122-124 reject accidental imports of the signature oracle interface or bilinear-pairing infrastructure.

## Review Checklist

- [ ] Follow the one-group request log: the second request uses the first reply, so the interaction is adaptive.
- [ ] Distinguish received inputs from outgoing values: only the initial inputs and incoming group replies accumulate.
- [ ] Check both vector counts and vector lengths: each output needs a vector, and each vector needs one coefficient per received input.
- [ ] Follow the two-group example: reply data can influence either sort's coefficients, but reconstruction uses only inputs of the output's own sort.
- [ ] Read the fresh-reply statements universally: incoming group values need no explanations, including in sorts not previously populated.
- [ ] Read the negative examples as logical claims: invalid explanations fail `Valid` or `IsAlgebraic`; the runner does not reject them dynamically.
- [ ] Check the proof boundary: guards reject unapproved axioms, but do not certify cryptographic security or paper fidelity.

Return to the [public definitions and theorem statements](review.md).
