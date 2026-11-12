# Direct unification on native term representations

Measured 2026-11-11 on the same Ryzen 7 5800X workstation, pinned to CPU 2,
using OCaml 5.4.1. This is a conversion-free kernel test, distinct from the
previous end-to-end query benchmarks. There are 26 workloads, seven samples
per solver and two compilation backends. CPU timing targets 30 ms per sample,
with the same 100,000-call repetition cap and alternating order as before.

Inputs for each algorithm are prepared before timing. Reference operates on
natural-number-ID terms and binding lists. Structural operates on indexed terms
and AList accumulators. Each batch retains the accumulator between equations;
it never decodes and re-encodes the substitution between calls. Pre-existing
stores are also constructed before timing, separately using each algorithm.
`index_term` is used only while preparing inputs. `decode_acc` and projection
are used only while checking results. Neither is called by the timed loops.

The timed functions are the extracted reference `unify_fn_cert` and structural
`amgu`, plus their small batch-driving loops. There is no goal validation,
search scheduling, answer printing, or projection in the measurements. Input
construction and garbage collection before each sample are excluded. Collections
triggered during the calls are included. Measurements are per complete equation
batch, not per equation, when a case contains multiple equations.

Before timing, the harness verifies that both initial stores and both final
results project to the same symbolic values on all allocated variables, allowing
consistent renaming of residual variables. Success/failure must agree too.
All 26 cases passed these checks in both backends.

## Results

Times are median CPU microseconds per call or batch. Ratios above one mean
structural is slower. Very small calls include batch-loop and call overhead;
the useful conclusions come from patterns across sizes, not tiny differences.

### Bytecode

| Workload | Size | Equations | Reference (µs) | Structural (µs) | Structural/reference |
| --- | ---: | ---: | ---: | ---: | ---: |
| `single_binding` | 1 | 1 | 0.421 | 0.169 | 0.402× |
| `unused_scope` | 64 | 1 | 0.411 | 0.170 | 0.415× |
| `unused_scope` | 256 | 1 | 0.399 | 0.165 | 0.413× |
| `ground_chain` | 16 | 1 | 45.503 | 2.453 | 0.054× |
| `ground_chain` | 64 | 1 | 629.422 | 9.457 | 0.015× |
| `ground_chain` | 256 | 1 | 9694.000 | 38.954 | 0.004× |
| `ground_balanced` | 6 | 1 | 40.668 | 10.369 | 0.255× |
| `ground_balanced` | 9 | 1 | 312.602 | 82.463 | 0.264× |
| `alias_batch` | 8 | 8 | 9.766 | 7.697 | 0.788× |
| `alias_batch` | 24 | 24 | 147.121 | 69.197 | 0.470× |
| `alias_batch` | 48 | 48 | 1042.094 | 276.641 | 0.265× |
| `alias_batch` | 96 | 96 | 7870.000 | 1106.000 | 0.141× |
| `constant_batch` | 8 | 8 | 4.409 | 6.615 | 1.500× |
| `constant_batch` | 24 | 24 | 42.095 | 56.805 | 1.349× |
| `constant_batch` | 48 | 48 | 269.250 | 219.332 | 0.815× |
| `constant_batch` | 96 | 96 | 2067.812 | 889.734 | 0.430× |
| `list_spine_batch` | 8 | 9 | 10.881 | 11.147 | 1.024× |
| `list_spine_batch` | 24 | 25 | 125.578 | 86.016 | 0.685× |
| `list_spine_batch` | 48 | 49 | 827.469 | 328.766 | 0.397× |
| `read_oldest_binding` | 32 | 1 | 1.380 | 0.396 | 0.287× |
| `read_newest_binding` | 32 | 1 | 0.943 | 6.288 | 6.666× |
| `read_oldest_binding` | 96 | 1 | 3.186 | 0.396 | 0.124× |
| `read_newest_binding` | 96 | 1 | 1.767 | 18.491 | 10.464× |
| `occurs_failure` | 64 | 1 | 6.689 | 2.146 | 0.321× |
| `occurs_failure` | 256 | 1 | 25.103 | 8.089 | 0.322× |
| `constructor_clash` | 1 | 1 | 0.271 | 0.089 | 0.329× |

### Native

| Workload | Size | Equations | Reference (µs) | Structural (µs) | Structural/reference |
| --- | ---: | ---: | ---: | ---: | ---: |
| `single_binding` | 1 | 1 | 0.047 | 0.013 | 0.264× |
| `unused_scope` | 64 | 1 | 0.047 | 0.013 | 0.279× |
| `unused_scope` | 256 | 1 | 0.047 | 0.013 | 0.282× |
| `ground_chain` | 16 | 1 | 4.621 | 0.163 | 0.035× |
| `ground_chain` | 64 | 1 | 60.449 | 0.614 | 0.010× |
| `ground_chain` | 256 | 1 | 945.406 | 2.419 | 0.003× |
| `ground_balanced` | 6 | 1 | 4.038 | 0.685 | 0.170× |
| `ground_balanced` | 9 | 1 | 33.343 | 5.767 | 0.173× |
| `alias_batch` | 8 | 8 | 0.814 | 0.659 | 0.809× |
| `alias_batch` | 24 | 24 | 11.439 | 6.131 | 0.536× |
| `alias_batch` | 48 | 48 | 85.080 | 23.854 | 0.280× |
| `alias_batch` | 96 | 96 | 639.922 | 96.074 | 0.150× |
| `constant_batch` | 8 | 8 | 0.459 | 0.597 | 1.302× |
| `constant_batch` | 24 | 24 | 3.541 | 5.411 | 1.528× |
| `constant_batch` | 48 | 48 | 20.568 | 20.766 | 1.010× |
| `constant_batch` | 96 | 96 | 150.902 | 84.562 | 0.560× |
| `list_spine_batch` | 8 | 9 | 0.929 | 0.949 | 1.021× |
| `list_spine_batch` | 24 | 25 | 9.765 | 7.597 | 0.778× |
| `list_spine_batch` | 48 | 49 | 65.812 | 29.144 | 0.443× |
| `read_oldest_binding` | 32 | 1 | 0.102 | 0.029 | 0.283× |
| `read_newest_binding` | 32 | 1 | 0.070 | 0.564 | 8.005× |
| `read_oldest_binding` | 96 | 1 | 0.210 | 0.029 | 0.137× |
| `read_newest_binding` | 96 | 1 | 0.129 | 1.726 | 13.378× |
| `occurs_failure` | 64 | 1 | 0.753 | 0.260 | 0.345× |
| `occurs_failure` | 256 | 1 | 3.085 | 0.947 | 0.307× |
| `constructor_clash` | 1 | 1 | 0.028 | 0.009 | 0.313× |

## What this changes about the earlier conclusion

Removing conversion changes the picture substantially. A batch of 48 alias
bindings takes about 1.04 ms for reference and 0.277 ms for structural in bytecode,
so structural is about 3.8 times faster. At 96 bindings, structural is about
7.1 times faster. Growing a 48-link list spine is about 2.5 times faster with
structural. Native-code results show the same direction for these cases.

There are genuine algorithm/representation tradeoffs beyond conversion. Reading
the newest binding from a 96-binding store favors reference by about 10.5 times
in bytecode, while reading the oldest favors structural. The reference list
places newer bindings at the front; structural postponement traverses earlier
eliminations first. Small batches of independent constant bindings also favor
reference. Ground chains strongly favor structural, as in the earlier test.
The `unused_scope` penalty largely disappears once input conversion is excluded.

This supports investigating a persistent indexed runtime representation rather
than repeatedly reconstructing one. It does not establish that a complete indexed
search engine would outperform the current engine: this test excludes opening,
fresh allocation, branching, input conversion, and answer projection. The previous
end-to-end results remain valid for the existing wrapper.

The source language does not have to become indexed. A future executable could
use indexed terms and accumulators internally while preserving the existing
source syntax and public API, with a correspondence proof to the abstract search
machine. That runtime integration is a separate implementation and proof task.

## Reproduction

```sh
make -C extract unifier-benchmark-bytecode unifier-benchmark-native
taskset -c 2 extract/unifier-benchmark-bytecode --samples 7 --target-seconds 0.03 > bytecode.csv
taskset -c 2 extract/unifier-benchmark-native --backend native --samples 7 --target-seconds 0.03 > native.csv
python3 benchmarks/summarize.py bytecode.csv native.csv > summary.csv
```

The harness is [unifier_benchmark.ml](../../extract/unifier_benchmark.ml).
Raw [bytecode](native-terms-bytecode.csv) and [native](native-terms-native.csv)
samples, the [summary](native-terms-summary.csv),
[environment](native-terms-environment.txt), and verification logs
([bytecode](native-terms-bytecode-verification.txt),
[native](native-terms-native-verification.txt)) are included.
