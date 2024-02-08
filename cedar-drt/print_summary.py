#!/usr/bin/env python3

"""
Process the tables output by `get_timings.rs` and print summary statistics.
"""

import csv
import sys
import numpy as np

# Returns the median runtime over all trials for each input
def process_file(filename):
    print(f"Processing {filename}...")
    data = []
    with open(filename) as csvfile:
        for row in csv.reader(csvfile):
            row = np.array([int(i) for i in row[1:]])
            median = np.percentile(row, 50)
            data.append(median)
    return data


def print_summary_stats(data):
    for k,v in data.items():
        print(k)
        v = np.array(v)
        median = np.percentile(v, 50)
        p90 = round(np.percentile(v, 90),1)
        p99 = round(np.percentile(v, 99),1)
        print(f"\tmin: {np.min(v)}, median: {median}, p90: {p90}, p99: {p99}, max: {np.max(v)}")

def main():
    # input data, output by `get_timings.rs`
    rust_auth_data = process_file("rust_auth.csv")
    rust_total_data = process_file("rust_total.csv")
    lean_auth_data = process_file("lean_auth.csv")
    lean_total_data = process_file("lean_total.csv")
    dafny_auth_data = process_file("dafny_auth_parse.csv")
    dafny_total_data = process_file("dafny_total.csv")
    rust_auth_data_td = process_file("rust_auth_type_directed.csv")
    rust_total_data_td = process_file("rust_total_type_directed.csv")
    lean_auth_data_td = process_file("lean_auth_type_directed.csv")
    lean_total_data_td = process_file("lean_total_type_directed.csv")
    dafny_auth_data_td = process_file("dafny_auth_parse_type_directed.csv")
    dafny_total_data_td = process_file("dafny_total_type_directed.csv")

    data = {"rust_auth": rust_auth_data, 
            "rust_total": rust_total_data,
            "lean_auth": lean_auth_data,
            "lean_total": lean_total_data,
            "dafny_auth_parse": dafny_auth_data,
            "dafny_total": dafny_total_data,
            "rust_auth_type_directed": rust_auth_data_td, 
            "rust_total_type_directed": rust_total_data_td,
            "lean_auth_type_directed": lean_auth_data_td,
            "lean_total_type_directed": lean_total_data_td,
            "dafny_auth_parse_type_directed": dafny_auth_data_td,
            "dafny_total_type_directed": dafny_total_data_td}
    print_summary_stats(data)

if __name__ == '__main__':
    sys.exit(main())