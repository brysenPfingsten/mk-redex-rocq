# Comparing extracted unification implementations

The [recorded results](results/README.md) compare both implementations on this
working tree and include the raw samples.

The benchmark extracts the reference and structural solver instances into one
OCaml module. Both use the same reduction machine, relation definitions,
validator and answer projection. The only selected component is the solver.
Production extraction and the public interface are unchanged.

Build the opt-in executables from the repository root:

```sh
make -C extract benchmark-bytecode benchmark-native
```

`benchmark-bytecode` uses `ocamlc`, as the normal CLI does. `benchmark-native`
uses `ocamlopt`. Each executable supports `--samples`, `--target-seconds`, and
`--case WORKLOAD_NAME`. The backend label is recorded with `--backend`.
For example:

```sh
extract/benchmark-bytecode --samples 7 --target-seconds 0.05 > bytecode.csv
extract/benchmark-native --backend native --samples 7 --target-seconds 0.05 > native.csv
python3 benchmarks/summarize.py bytecode.csv native.csv > summary.csv
```

The committed results use CPU affinity on a Linux workstation. They can be
repeated with `taskset -c 2` before each executable command if CPU 2 is available.
Run the two backends sequentially to avoid competing benchmark processes.

## What is measured

`search` runs the extracted reporting stepper with tracing disabled, from an
already constructed valid initial expression. It includes unification and
scheduling, but excludes input validation and answer projection.

`checked` runs the extracted checked interface. It includes environment/goal/query
validation, search, status reporting and answer projection. Parsing, printing,
program construction and process startup are excluded in both modes. Inputs
are built once and reused, so these are repeated-call measurements rather than
cold-start CLI timings.

Before timing a case, the harness checks completion status, executed step count,
ordered projected answers, and agreement between search-only and checked runs.
Residual variables are renamed canonically within each answer, jointly across
its query bindings, so comparisons retain sharing without requiring identical
raw variable IDs. Finite cases must finish. `listo_prefix` intentionally measures
an infinite search at a fixed step budget. Failure cases have zero answers.

Calibration chooses separate repetition counts for the two solvers to reach
the target CPU time per sample, capped at 100,000 calls. Each sample begins with
a full major collection outside the timed region. Solver order alternates
between paired samples. Timed execution includes garbage collection caused by
the measured calls, and opaque result consumption prevents removal of the
computation. The CSV records CPU and wall time per call, repetition counts, and
allocated bytes calculated as minor words plus major words minus promoted words.
The summary uses median CPU time and retains sample minima and maxima.

## Workloads

- `single_binding` is a one-variable equality.
- `unused_scope` changes the allocated counter while keeping that equality fixed.
  It isolates sensitivity to allocated but unused IDs.
- `ground_chain` unifies two equal right-nested ground pair chains; size is depth.
- `ground_balanced` unifies equal balanced ground trees; size is tree depth.
- `binding_chain` builds aliases followed by a ground binding; size is variable count.
- `appendo_forward` appends two lists of the stated length into a query variable.
- `appendo_splits` enumerates all splits of a list of the stated length.
- `membero` enumerates membership derivations in a list of the stated length.
- `listo_prefix` generates symbolic proper lists; size is the reduction budget.
- `occurs_failure` rejects an equality with an occurrence at the end of a chain.

These cases cover the expected cost tradeoff, rather than estimating an average
over all possible miniKanren programs. In particular, equal reduction-step counts
do not imply equal CPU time: an abstract unification action can contain different
amounts of implementation work. The results describe this wrapper, which rebuilds
the indexed accumulator on every call; they do not establish a general ranking
of McBride's algorithm against other unification algorithms.

## Direct algorithm comparison without conversion

The [native-term kernel results](results/native-terms.md) repeat the comparison
with the two term representations prepared before timing. The structural
accumulator is retained between equations, so the timed path does not call the
runtime conversion wrapper. Build with:

```sh
make -C extract unifier-benchmark-bytecode unifier-benchmark-native
```

Both binaries accept `--samples`, `--target-seconds`, and `--backend`. Their
CSV records the number of equations per batch; the same summarizer handles
these files. These measurements isolate unification and do not replace the
end-to-end search measurements above.
