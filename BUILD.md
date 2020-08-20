Using the Artifact Package
===
Our PLDI'20 paper is published with an artifact package. It is a self-contained package with all dependencies installed. You can find the package as well as the instructions [here](https://dl.acm.org/do/10.1145/3395653/abs/).

Building on Linux
===
This instruction is adapted from the [INSTALL.md](https://github.com/dafny-lang/dafny/blob/master/INSTALL.md) from dafny repo. `BASE-DIRECTORY` is assumed to be your base directory for building Armada.

0. Dependencies: [Install Mono](https://www.mono-project.com/download/stable/#download-lin) from the official repositories; the version in most distribution repositories is too out of date. The `mono-devel` package is what you need. On Fedora, you'll also need the `msbuild` package.

1. Create an empty base directory and download nuget

       mkdir BASE-DIRECTORY
       cd BASE-DIRECTORY
       wget https://dist.nuget.org/win-x86-commandline/v3.3.0/nuget.exe

   Alternatively, you can also use the `nuget` binaries provided your package manager. Make sure the version is at least `2.12`.

2. Download and build Boogie:

       git clone --branch v2.4.21 https://github.com/boogie-org/boogie
       cd boogie
       mono ../nuget.exe restore Source/Boogie.sln
       msbuild Source/Boogie.sln
       cd ..

3. Download and build Armada:

       cd BASE-DIRECTORY
       git clone https://github.com/microsoft/armada
       mono ./nuget.exe restore armada/Source/Armada.sln
       msbuild armada/Source/Armada.sln

4. An executable named `Armada.exe` should be built in directory `armada/Binaries/`. You will also need [scons](https://scons.org/), [Dafny@d16450](https://github.com/dafny-lang/dafny/commit/d16450), and [Z3@4.8.4](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.4) to run the tests.

Building on Windows/Mac OS
===
Building on other platforms is similar to building on Linux. Make sure that you put both boogie and Armada repositories in the same folder, and you build the boogie binaries before building Armada.

You can use Visual Studio 2017 (any version, including the free Community one available from Microsoft) on Windows platforms or `mono` on Mac OS platforms to build Armada.
