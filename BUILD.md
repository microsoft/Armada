Building on Linux
===
These instructions are adapted from the [Dafny Wiki](https://github.com/dafny-lang/dafny/wiki/INSTALL). They assume that `BASE-DIRECTORY` is the base directory in which you want to build Armada.

1. Install .NET 5.0 following the instructions [here](https://docs.microsoft.com/en-us/dotnet/core/install/).

2. Create the base directory with
```
       mkdir BASE-DIRECTORY
```

3. Download Dafny v3.0.0 with
```
       cd BASE-DIRECTORY
       wget https://github.com/dafny-lang/dafny/releases/download/v3.0.0/dafny-3.0.0-x64-debian-8.11.zip
       unzip dafny-3.0.0-x64-debian-8.11.zip
```

4. Download and build Armada with:
```
       cd BASE-DIRECTORY
       git clone https://github.com/microsoft/armada
       dotnet build armada/Source/Armada.sln
```

   You should then find an executable named `Armada.dll` in the directory `armada/Binaries/`.

5. To run the tests, you'll also need to install [scons](https://scons.org).

Building on Windows/Mac OS
===
Building on other platforms is similar to building on Linux. You will need to download the correct Dafny binaries for your platform in step 3. On the Windows platform, the produced binary is `Armada.exe` instead of `Armada.dll`.
