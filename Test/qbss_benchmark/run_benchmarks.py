#!/bin/env python
import subprocess
import csv
import numpy as np
from math import sqrt

import matplotlib
matplotlib.use('PS')
import matplotlib.pyplot as plt

queue_capacity = 512
num_iterations = 1000

def run_benchmark(bench_name):
    outfilename = bench_name + "_data.csv"
    with open(outfilename, 'w') as fp:
        result = subprocess.run(["./" + bench_name,
                str(queue_capacity),
                str(num_iterations)],
            stdout=fp)
    return outfilename

def parse_benchmark_results(csvfilename):
    with open(csvfilename, 'r') as csvfile:
        reader = csv.reader(csvfile, delimiter=',')
        next(reader)
        values = []
        for row in reader:
            values.append(int(row[1]))
        return values

def mean_confidence_interval(data):
    a = 1.0 * np.array(data)
    n = len(a)

    m = np.mean(a)
    h = 1.96 * np.std(a)/sqrt(n)  # 95% confidence interval
    return m, h


def get_benchmark_statistics(bench_name):
    csvfilename = run_benchmark(bench_name)
    v = parse_benchmark_results(csvfilename)
    s = mean_confidence_interval(v)
    return s

def plot(values):
    plt.rc('text', usetex='True')
    plt.rc('font', family='Serif', size=11)


    w = 6
    h = 4
    d = 70
    plt.figure(figsize=(w, h), dpi=d)

    means = [values[0][0], values[1][0], values[2][0], values[3][0]]
    xs = ["liblfds (GCC)", "liblfds-modulo (GCC)", "Anon (GCC)",
          "Anon (CompCert)"]
    std = [values[0][1], values[1][1], values[2][1], values[3][1]]

    plt.ylabel("Throughput (ops/sec)")
    plt.xticks(rotation=10)
    plt.grid(True, "major", axis="y")
    plt.bar(xs, means, color="#FF8000", edgecolor="000000", yerr=std,
            capsize=5, width=0.3)
    plt.tight_layout()
    plt.savefig("qbss_performance_graph.pdf")


def main():
    subprocess.run(["make", "all"])
    print("\n\nFinished building\nRunning benchmarks now")
    values = [get_benchmark_statistics("benchmark_lfds"),
              get_benchmark_statistics("benchmark_lfds_modulo"),
              get_benchmark_statistics("benchmark"),
              (0, 0)
              ]
    plot(values)

#values = [(1e7, 1e5), (1.5e7, 0.5e5),
#        (1.2e7, 1e5), (1.3e7, 1.4e5)
#        ]
if __name__ == '__main__':
    main()
