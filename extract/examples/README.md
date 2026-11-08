# Representative relational programs

These examples focus on logical behavior and search scheduling. They are
regression examples, not performance benchmarks. Build with
`make -C extract all` from the repository root, then run:

```sh
extract/mk-search --fuel 200 extract/examples/appendo-splits.sexp
```

`(relations standard)` loads the definitions from
`src/Examples/Relations.v`, extracted into the executable. It is a parser
shorthand; the resulting definitions still go through the ordinary certified
validator. Relation indices are:

| Index | Relation | Arguments |
| --- | --- | --- |
| 0 | `appendo` | prefix, suffix, concatenation |
| 1 | `membero` | element, pair chain |
| 2 | `listo` | proper list |

The ordinary explicit `(relations (relation ARITY BODY) ...)` form remains
available for custom programs.

| File | Query in familiar notation | Expected result |
| --- | --- | --- |
| `appendo-forward.sexp` | append([1,2], [3], q0) | q0 = [1,2,3]; complete |
| `appendo-backward.sexp` | append(q0, [3], [1,2,3]) | q0 = [1,2]; complete |
| `appendo-splits.sexp` | append(q0, q1, [1,2]) | ([],[1,2]), ([1],[2]), ([1,2],[]); complete |
| `appendo-partial.sexp` | append([q0], [2], q1) | q0 remains free and q1 = [q0,2]; complete |
| `membero.sexp` | member(q0, [1,2,3]) | q0 = 1, 2, 3; complete |
| `membero-generate.sexp` | member(7, q0) | symbolic pair chains with 7 at successive positions; infinite search |
| `listo.sexp` | proper-list(q0) | [], [a], [a,b], ... with independent fresh elements; infinite search |

The CLI displays lists using pairs: `[1,2]` appears as `(1 . (2 . nil))`.
Names `_N` are residual existential variables; their numeric IDs may change
with allocation details. Shared occurrences of a name within an answer
refer to the same variable. The partial append example tests this sharing
without depending on the actual IDs.

`membero` has the usual relational definition that stops constraining the
tail once a match is found. Its generative query therefore returns open
pair chains such as `(7 . _N)`, not exclusively proper lists. To require
proper lists, conjoin a `listo` call. Membership in a list containing the
same value twice produces two answers: search preserves derivation
multiplicity, while the denotation is a set of ground solutions.

`listo` has an infinite ground solution space, but answers remain symbolic:
a single length-two answer represents every proper two-element ground list.
It does not enumerate element values. Infinite examples normally report
`fuel exhausted` and exit 3 while retaining the answers found so far.

`seven.sexp`, `sevens.sexp`, `residual.sexp`, and `bad-call.sexp` are smaller
interface examples. `bad-call.sexp` is deliberately invalid and exits 2.

`relation_tests.ml` checks all seven representative files, append boundary
and failure cases, suffix recovery, duplicate membership, independent fresh
list elements, and answer-prefix persistence with additional fuel. The Rocq
module also proves that ground list concatenations satisfy `appendo`, list
members satisfy `membero`, and finite proper lists satisfy `listo`. These
are source-level inclusion lemmas; they do not claim converse
characterizations of the library relations. General search soundness and
completeness apply through the existing well-formedness theorem.
