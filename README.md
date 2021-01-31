# Overview

Safely writing high-performance concurrent programs is notoriously difficult. To aid developers, we
introduce Armada, a language and tool designed to formally verify such programs with relatively
little effort. Via a C-like language that compiles to the C subset ClightTSO and a small-step,
state-machine-based semantics, Armada gives developers the flexibility to choose arbitrary memory
layout and synchronization primitives so they are never constrained in their pursuit of
performance. To reduce developer effort, Armada leverages SMT-powered automation and a library of
powerful reasoning techniques, including rely-guarantee, TSO elimination, reduction, and alias
analysis. All these techniques are proven sound, and Armada can be soundly extended with additional
strategies over time. Using Armada, we verify four concurrent case studies and show that we can
achieve performance equivalent to that of unverified code.

You can read more about Armada in our PLDI '20 paper, which ACM will publish on June 17, 2020:

Jacob R. Lorch, Yixuan Chen, Manos Kapritsos, Bryan Parno, Shaz Qadeer, Upamanyu Sharma, James
R. Wilcox, and Xueyuan Zhao. 2020. Armada: Low-Effort Verification of High-Performance Concurrent
Programs. In Proceedings of the 41st ACM SIGPLAN International Conference on Programming Language
Design and Implementation (PLDI '20), June 15-20, 2020, London, UK. ACM, New York, NY, USA, 14
pages. https://doi.org/10.1145/3385412.3385971


# Getting started

To build Armada, please follow the detailed instructions documented in [BUILD.md](BUILD.md).

To use Armada, you'll need the following tools:

  * .NET 5.0 (runtime for both Armada and Dafny)
  * pip (needed for installing scons)
  * scons (installable by running `pip install scons`)
  * Dafny v3.0.0 (available at https://github.com/dafny-lang/dafny)


# Generating and testing proofs

To use the Armada tool to generate proofs for all the included test Armada files (`Test/*/*.arm`),
run, from the Armada top-level directory, `scons -j <n> -f SConstruct1` where `<n>` is the number of
threads you want scons to use.

To verify all the generated proofs, run, from the same directory, `scons -j <n> -f SConstruct2
--DAFNYPATH=<dafny-path>` where `<dafny-path>` is the directory containing the `Dafny.exe`/`Dafny.dll`
binary you installed.

If this second scons finishes without printing an error message, this means that everything worked.
If it reports an error, this is likely due to running on a machine without enough memory, so try
again with fewer threads.


# Compilation, performance evaluation, and graph generation

To build the queue benchmarks, run them, and generate the performance graphs, run `python3
run_benchmarks.py` in the `Test/qbss_benchmark/` directory. This will produce a file
`qbss_performance_graph.pdf` with the performance graph.


# Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.
