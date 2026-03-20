#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path


def write_csv(path: Path, header: list[str], rows: list[list[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        writer.writerows(rows)


def coarse_fine_rows() -> list[list[object]]:
    examples = [
        # value, coarse(A,m), fine(a,n), split t where A=a^t and n=t*m
        (16, 4, 2, 2),
        (81, 9, 2, 3),
        (64, 8, 2, 2),
        (729, 27, 2, 3),
        (256, 16, 2, 4),
        (625, 25, 2, 5),
        (1296, 36, 2, 6),
    ]

    rows: list[list[object]] = []
    for value, coarse_base, coarse_exp, fine_base in examples:
        # infer split ratio t from coarse_base = fine_base^t
        # t is integer in these designed examples
        split_ratio = round(math.log(coarse_base, fine_base))
        fine_exp = coarse_exp * split_ratio

        coarse_value = coarse_base**coarse_exp
        fine_value = fine_base**fine_exp
        valid = coarse_value == fine_value == value

        rows.append(
            [
                value,
                f"{coarse_base}^{coarse_exp}",
                f"{fine_base}^{fine_exp}",
                split_ratio,
                int(valid),
            ]
        )
    return rows


def multiresolution_rows() -> list[list[object]]:
    rows: list[list[object]] = []
    value = 64**2
    rows.append([value, "64^2", "4096", 1])
    rows.append([value, "8^4", "4096", 1])
    rows.append([value, "4^6", "4096", 1])
    rows.append([value, "2^12", "4096", 1])
    return rows


def powerswap_rows(ts: list[float]) -> list[list[object]]:
    rows: list[list[object]] = []
    for t in ts:
        if t <= 0 or abs(t - 1.0) < 1e-12:
            continue
        a = t ** (1.0 / (t - 1.0))
        b = t ** (t / (t - 1.0))

        lhs = a**b
        rhs = b**a
        rel_err = abs(lhs - rhs) / max(abs(lhs), abs(rhs), 1.0)

        rows.append(
            [
                t,
                a,
                b,
                lhs,
                rhs,
                rel_err,
                int(rel_err < 1e-10),
            ]
        )
    return rows


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate coarse↔fine exchange and powerswap-balance sample CSVs"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).parent / "docs",
        help="Output directory for generated CSV files",
    )
    parser.add_argument(
        "--t-list",
        type=str,
        default="0.5,2,3,4",
        help="Comma-separated t values for continuous powerswap family",
    )
    return parser.parse_args()


def parse_t_list(raw: str) -> list[float]:
    ts: list[float] = []
    for token in raw.split(","):
        tok = token.strip()
        if not tok:
            continue
        ts.append(float(tok))
    return ts


def main() -> None:
    args = parse_args()
    out_dir = args.output_dir

    coarse_rows = coarse_fine_rows()
    coarse_path = out_dir / "exchange_coarse_fine_examples.csv"
    write_csv(
        coarse_path,
        ["value", "coarse_expr", "fine_expr", "split_ratio", "valid"],
        coarse_rows,
    )

    multi_rows = multiresolution_rows()
    multi_path = out_dir / "exchange_multiresolution_chain.csv"
    write_csv(multi_path, ["value", "expr", "eval", "valid"], multi_rows)

    t_values = parse_t_list(args.t_list)
    ps_rows = powerswap_rows(t_values)
    ps_path = out_dir / "powerswap_continuous_samples.csv"
    write_csv(
        ps_path,
        ["t", "a", "b", "a_pow_b", "b_pow_a", "relative_error", "balanced"],
        ps_rows,
    )

    print(f"Wrote coarse/fine examples -> {coarse_path}")
    print(f"Wrote multiresolution chain -> {multi_path}")
    print(f"Wrote powerswap continuous samples -> {ps_path}")


if __name__ == "__main__":
    main()
