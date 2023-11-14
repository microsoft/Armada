# Starmada

## Installation

Starmada requires the following prerequisites to run:
- dotnet 6.0
- FStar

To build and check everything, run
```
scons --all
```

After installing the above applications, you can compile Starmada using either of the following commands:

```
dotnet build Source/Armada.sln
scons --build
```


In order to generate fstar files (.fst) from .arm files, you can run the following command (N is the level of parallelism to run the commands):
```
scons --generate-fstar [-jN]
```

Afterwards, to verify the correctness of the generated files, and run FStar, you can run the following command:
```
scons --run-fstar [-jN]
```

To verify the sample proofs that exercise the library, you can run the following command (N is the level of parallelism):
```
scons --verify-lib [-jN]
```

# Build using docker

In order to build Starmada using docker, you can use the following instructions:
```
cd docker
sudo docker build ../ -f Dockerfile
```