# Unification measurements, 2026-11-10

The current structural replacement is slower on the representative relational
queries in this suite, despite being substantially faster on deep ground-term
unification. This is a measurement of the current runtime conversion strategy,
not a general conclusion about structurally recursive unification.

The benchmark ran on an AMD Ryzen 7 5800X, pinned to logical CPU 2, with OCaml
5.4.1. It compares the two extracted solver instances in the same machine.
There are 22 cases, two measurement modes, two backends, and seven samples per
solver per case: 1,232 recorded samples. Repetition counts are calibrated toward
50 ms of CPU time per sample, capped at 100,000 calls. The normal executable uses
bytecode; native results are included to check whether the pattern depends on
that backend. See [the methodology](../README.md) and [environment](environment.txt).

Every case passed checks for equal completion status, reduction-step counts and
ordered projected answers, comparing residual variables up to renaming while
preserving sharing. Search-only answers also agree with checked-interface answers.

## Checked-interface CPU time

These are median microseconds per query, including validation, search and answer
projection. Parsing, printing, program construction and process startup are
excluded. A structural/reference ratio above one means structural is slower.
The raw samples also retain wall times; the summary retains sample minima and
maxima. Do not interpret small differences on the single-binding case as a
meaningful general speed advantage.

### Bytecode

| Workload | Size | Reference (µs) | Structural (µs) | Structural/reference |
| --- | ---: | ---: | ---: | ---: |
| `single_binding` | 1 | 1.04 | 1.06 | 1.021× |
| `unused_scope` | 64 | 1.03 | 3.58 | 3.462× |
| `unused_scope` | 256 | 1.03 | 11.52 | 11.231× |
| `ground_chain` | 16 | 48.66 | 5.18 | 0.106× |
| `ground_chain` | 64 | 645.20 | 18.83 | 0.029× |
| `ground_chain` | 256 | 9846.25 | 72.66 | 0.007× |
| `ground_balanced` | 6 | 44.42 | 18.71 | 0.421× |
| `ground_balanced` | 9 | 339.33 | 148.44 | 0.437× |
| `binding_chain` | 8 | 20.63 | 91.62 | 4.442× |
| `binding_chain` | 24 | 209.52 | 1772.38 | 8.459× |
| `binding_chain` | 48 | 1372.42 | 16011.50 | 11.667× |
| `appendo_forward` | 4 | 88.83 | 419.30 | 4.720× |
| `appendo_forward` | 12 | 592.87 | 6525.50 | 11.007× |
| `appendo_forward` | 24 | 3323.44 | 55715.00 | 16.764× |
| `appendo_splits` | 4 | 120.54 | 752.46 | 6.242× |
| `appendo_splits` | 8 | 400.88 | 4042.75 | 10.085× |
| `membero` | 8 | 113.38 | 795.75 | 7.018× |
| `membero` | 24 | 939.31 | 18882.25 | 20.102× |
| `listo_prefix` | 128 | 273.80 | 1901.94 | 6.947× |
| `listo_prefix` | 256 | 2369.66 | 23335.75 | 9.848× |
| `occurs_failure` | 64 | 8.65 | 6.84 | 0.790× |
| `occurs_failure` | 256 | 31.59 | 25.33 | 0.802× |

### Native

| Workload | Size | Reference (µs) | Structural (µs) | Structural/reference |
| --- | ---: | ---: | ---: | ---: |
| `single_binding` | 1 | 0.11 | 0.10 | 0.930× |
| `unused_scope` | 64 | 0.11 | 0.39 | 3.638× |
| `unused_scope` | 256 | 0.11 | 1.09 | 10.272× |
| `ground_chain` | 16 | 5.06 | 0.53 | 0.105× |
| `ground_chain` | 64 | 67.26 | 1.96 | 0.029× |
| `ground_chain` | 256 | 1014.28 | 7.66 | 0.008× |
| `ground_balanced` | 6 | 4.86 | 1.95 | 0.402× |
| `ground_balanced` | 9 | 38.92 | 17.06 | 0.438× |
| `binding_chain` | 8 | 1.54 | 6.45 | 4.193× |
| `binding_chain` | 24 | 16.27 | 198.41 | 12.197× |
| `binding_chain` | 48 | 105.78 | 1848.94 | 17.479× |
| `appendo_forward` | 4 | 5.60 | 32.01 | 5.711× |
| `appendo_forward` | 12 | 44.49 | 753.77 | 16.944× |
| `appendo_forward` | 24 | 256.28 | 6741.38 | 26.305× |
| `appendo_splits` | 4 | 7.98 | 63.49 | 7.954× |
| `appendo_splits` | 8 | 29.14 | 470.76 | 16.155× |
| `membero` | 8 | 7.69 | 74.98 | 9.747× |
| `membero` | 24 | 72.84 | 2483.94 | 34.099× |
| `listo_prefix` | 128 | 20.75 | 206.34 | 9.942× |
| `listo_prefix` | 256 | 182.25 | 2713.31 | 14.888× |
| `occurs_failure` | 64 | 1.04 | 0.99 | 0.943× |
| `occurs_failure` | 256 | 4.08 | 3.55 | 0.869× |

## Interpretation

For two lists of length 24, checked `appendo_forward` takes 3.32 ms with the
reference solver and 55.72 ms with structural unification in bytecode: 16.8 times
slower. Native compilation reduces both times to 0.256 ms and 6.74 ms, respectively,
but structural remains 26.3 times slower. All nine representative relational
cases (`appendo_forward`, `appendo_splits`, `membero`, `listo_prefix`) favor the
reference implementation in both backends.

This is not solely validation or answer-projection overhead. Search-only
`appendo_forward/24` also favors reference; its exact ratios are in
[summary.csv](summary.csv). Bytecode checked allocation for that case is about
0.262 MB per reference query and 59.77 MB per structural query. This is total
allocated storage, not peak live memory. The structural wrapper reconstructs an
indexed accumulator from the entire current substitution on every equality,
then decodes the result back into a binding list. That code path is a clear
optimization target. The benchmark does not isolate individual conversion
functions, so it does not assign a measured percentage to each internal cost.

The controlled cases support that interpretation: with the same one-variable
equality, raising the allocation counter from 1 to 256 leaves reference close
to 1 µs but raises structural to about 11.5 µs in bytecode. Alias chains also
increasingly favor reference as the store grows.

Deep ground chains show the opposite pattern. At depth 256, checked bytecode
time drops from 9.85 ms to 0.0727 ms, about 135 times faster. Native improves
from 1.01 ms to 0.00766 ms, about 132 times faster. Structural descent avoids
the reference implementation's repeated increasing-fuel attempts; this benefit
is visible without the cost of reconstructing a large existing store. Balanced
ground trees and the tested occurs-check failures also favor structural.

The results do not justify calling the current replacement an overall speedup.
A useful next experiment is to avoid rebuilding the indexed state for every
unification, or to reduce the scope to relevant variables, and then rerun this
same suite. Such changes need to preserve the existing solver contract. No solver
default was changed as part of the benchmark.

## Files

- [Bytecode samples](unification-bytecode.csv)
- [Native samples](unification-native.csv)
- [Median/range/allocation summary for both modes](summary.csv)
- [Bytecode verification log](verification-bytecode.txt)
- [Native verification log](verification-native.txt)
