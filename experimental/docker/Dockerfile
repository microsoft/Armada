# This Dockerfile should be run from the root FStar directory

# Build the package
ARG ocaml_version=4.12
ARG CI_THREADS=24

FROM ocaml/opam:ubuntu-20.04-ocaml-$ocaml_version AS fstarbuild

# FIXME: the `opam depext` command should be unnecessary with opam 2.1
RUN opam depext conf-gmp conf-m4

ADD --chown=opam:opam ./fstar.opam fstar.opam

# Install opam dependencies only, but not z3
RUN grep -v z3 < fstar.opam > fstar-no-z3.opam && \
    rm fstar.opam && \
    opam install --deps-only ./fstar-no-z3.opam && \
    rm fstar-no-z3.opam

# Install .NET
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
  libicu66

# (for .NET, cf. https://aka.ms/dotnet-missing-libicu )
# CI dependencies: .NET Core
# Repository install may incur some (transient?) failures (see for instance https://github.com/dotnet/sdk/issues/27082 )
# So, we use manual install instead, from https://docs.microsoft.com/en-us/dotnet/core/install/linux-scripted-manual#manual-install
ENV DOTNET_ROOT /home/opam/dotnet
RUN sudo apt-get install --yes --no-install-recommends \
    wget scons \
    && \
    wget https://download.visualstudio.microsoft.com/download/pr/cd0d0a4d-2a6a-4d0d-b42e-dfd3b880e222/008a93f83aba6d1acf75ded3d2cfba24/dotnet-sdk-6.0.400-linux-x64.tar.gz && \
    mkdir -p $DOTNET_ROOT && \
    tar xf dotnet-sdk-6.0.400-linux-x64.tar.gz -C $DOTNET_ROOT

ENV PATH=${PATH}:$DOTNET_ROOT:$DOTNET_ROOT/tools

# Download and extract z3, but do not add it in the PATH
# We download a z3 that does not depend on libgomp
ADD --chown=opam:opam https://github.com/tahina-pro/z3/releases/download/z3-4.8.5-linux-clang/z3-4.8.5-linux-clang-x86_64.tar.gz z3.tar.gz
RUN tar xf z3.tar.gz

RUN git clone https://github.com/FStarLang/FStar.git -b v2024.01.13
WORKDIR FStar/ 
RUN eval $(opam env) && env OTHERFLAGS='--admit_smt_queries true' PATH=$HOME/z3:$PATH make -j $CI_THREADS 
ENV PATH=${PATH}:/home/opam/FStar/bin:/home/opam/z3

RUN sudo wget https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
RUN sudo dpkg -i packages-microsoft-prod.deb
RUN sudo apt-get update
RUN sudo apt-get install -y dotnet-sdk-5.0 aspnetcore-runtime-5.0 dotnet-runtime-5.0
RUN sudo apt-get install -y dotnet-sdk-6.0 aspnetcore-runtime-6.0 dotnet-runtime-6.0

WORKDIR $HOME
RUN wget https://github.com/dafny-lang/dafny/releases/download/v3.0.0/dafny-3.0.0-x64-debian-8.11.zip
RUN unzip dafny-3.0.0-x64-debian-8.11.zip
RUN git clone https://github.com/microsoft/Armada.git
WORKDIR $HOME/Armada
RUN dotnet build Source/Armada.sln

ADD --chown=opam . $HOME/starmada
WORKDIR $HOME/starmada
RUN dotnet build Source/Armada.sln
# RUN scons --generate-fstar -j8
# RUN scons --run-fstar -j8

ENV PATH=${PATH}:/home/opam/starmada/Binary
