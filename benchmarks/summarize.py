#!/usr/bin/env python3
"""Summarize paired solver benchmark samples; ratios above one favor reference."""

import csv
import statistics
import sys


def main(paths):
    groups = {}
    for path in paths:
        with open(path, newline="") as source:
            for row in csv.DictReader(source):
                key = tuple(row[k] for k in ("backend", "mode", "workload", "size"))
                groups.setdefault(key, {}).setdefault(row["solver"], []).append(row)
    fields = ["backend", "mode", "workload", "size", "equations", "steps", "answers", "samples",
              "reference_us", "structural_us", "structural_over_reference",
              "reference_min_us", "reference_max_us", "structural_min_us", "structural_max_us",
              "reference_allocated_bytes", "structural_allocated_bytes"]
    output = csv.DictWriter(sys.stdout, fieldnames=fields)
    output.writeheader()
    for key, solvers in groups.items():
        reference, structural = solvers["reference"], solvers["structural"]
        assert len(reference) == len(structural)
        assert {r["sample"] for r in reference} == {r["sample"] for r in structural}
        times_r = [float(r["cpu_us"]) for r in reference]
        times_s = [float(r["cpu_us"]) for r in structural]
        median_r, median_s = statistics.median(times_r), statistics.median(times_s)
        row = dict(zip(fields[:4], key))
        row.update(equations=reference[0].get("equations", ""),
                   steps=reference[0].get("steps", ""), answers=reference[0].get("answers", ""),
                   samples=len(reference), reference_us=f"{median_r:.6f}",
                   structural_us=f"{median_s:.6f}",
                   structural_over_reference=f"{median_s / median_r:.6f}",
                   reference_min_us=f"{min(times_r):.6f}",
                   reference_max_us=f"{max(times_r):.6f}",
                   structural_min_us=f"{min(times_s):.6f}",
                   structural_max_us=f"{max(times_s):.6f}",
                   reference_allocated_bytes=f"{statistics.median(float(r['allocated_bytes']) for r in reference):.1f}",
                   structural_allocated_bytes=f"{statistics.median(float(r['allocated_bytes']) for r in structural):.1f}")
        output.writerow(row)


if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit("usage: summarize.py SAMPLE.csv [SAMPLE.csv ...]")
    main(sys.argv[1:])
