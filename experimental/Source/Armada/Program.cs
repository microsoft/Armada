using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using Microsoft.Starmada;
using CommandLine;

using CommandLineParser = CommandLine.Parser;
using StarmadaParser = Microsoft.Starmada.Parser;

namespace Starmada
{
    class Program
    {
        public class Options
        {
            [Option('v', "verbose", Required = false, HelpText = "Set output to verbose messages.")]
            public bool Verbose { get; set; }

            [Option('c', "ccode", Required = false, HelpText = "Print emitted C output.")]
            public bool CCode { get; set; }

            [Option('f', "fstar", Required = false, HelpText = "Print emitted FStar output.")]
            public bool FStarCode { get; set; }

            [Option('a', "atomic", Required = false, HelpText = "Print emitted FStar atomic output.")]
            public bool AtomicCode { get; set; }

            [Value(0, Required = true, MetaName = "input_file", HelpText = "Input file.")]
            public IEnumerable<string> InputFiles { get; set; }
        }

        static void Main(string[] args)
        {
            CommandLineParser.Default.ParseArguments<Options>(args).WithParsed<Options>(o =>
            {
                foreach (var inputFile in o.InputFiles)
                {
                    IncludeProcessor ip = new IncludeProcessor(inputFile);
                    string includeFile = ip.processIncludes();

                    Scanner scanner = new Scanner(includeFile);
                    StarmadaParser p = new StarmadaParser(scanner, inputFile);
                    p.Parse();
                    if (p.errors.ErrorCount > 0)
                    {
                        Console.WriteLine($"program has {p.errors.ErrorCount} parse errors");
                        Environment.ExitCode = -1;
                        return;
                    }

                    if (o.CCode)
                    {
                        var cCodeOutputPath = Path.GetDirectoryName(inputFile) + "/" + Path.GetFileNameWithoutExtension(inputFile) + ".c";
                        System.IO.File.WriteAllText(cCodeOutputPath, p.program.ToCProgram(0));
                    }

                    p.program.SetProgramCounter("", 0);
                    Resolver resolver = new Resolver();
                    resolver.Resolve(p.program);
                    ProofResolver proofResolver = new();
                    proofResolver.Resolve(p.program);

                    if (o.Verbose)
                    {
                        Console.WriteLine(p.program.ToString(0, true));
                    }

                    if (p.errors.ErrorCount > 0)
                    {
                        Console.WriteLine($"program has {p.errors.ErrorCount} type resolution errors");
                        Environment.ExitCode = -1;
                        return;
                    }

                    var Capitalized = (string s) => char.ToUpper(s[0]) + s.Substring(1);

                    var fstarOutputPath = Path.GetDirectoryName(inputFile) + "/";
                    var globalDeclFileName = Capitalized(Path.GetFileNameWithoutExtension(inputFile));

                    var GetOpenModules = (List<string> moduleNames) =>
                        String.Join("", moduleNames.Select(s => $"open {s}\n"));

                    if (o.FStarCode || o.AtomicCode)
                    {
                        System.IO.File.WriteAllText(Path.Combine(fstarOutputPath, globalDeclFileName + ".fst"), p.program.ToFStarLang(0));
                        foreach (var level in p.program.Levels)
                        {
                            var moduleName = Capitalized(level.Name.ToString(0, false));
                            var header = Printer.GetFStarHeaderForModule(moduleName);
                            header += GetOpenModules(new() { globalDeclFileName });
                            var levelStr = level.ToFStarLang(0) + "\n";
                            System.IO.File.WriteAllText(fstarOutputPath + moduleName + ".fst", header + '\n' + levelStr);
                        }
                    }

                    if (o.AtomicCode)
                    {
                        var atomicPrinter = new AtomicPrinter();
                        var proofPrinter = new ProofPrinter();
                        foreach (var level in p.program.Levels)
                        {
                            var levelName = Capitalized(level.Name.ToString(0, false));
                            var moduleName = "Atomic" + levelName;
                            var header = Printer.GetFStarHeaderForModule(moduleName);
                            header += Printer.GetFStarAtomicHeader();
                            header += GetOpenModules(new() { globalDeclFileName, levelName });
                            var levelStr = atomicPrinter.ToFStarAtomic(level, 0, levelName) + "\n";
                            System.IO.File.WriteAllText(fstarOutputPath + moduleName + ".fst", header + '\n' + levelStr);
                            foreach (var (name, body) in proofPrinter.GetProofs(level, 0)) {
                                System.IO.File.WriteAllText(fstarOutputPath + name + ".fst", body);
                            }
                        }

                        LevelDecl L = proofResolver.GetLLevel();
                        LevelDecl H = proofResolver.GetHLevel();
                        if (L != null)
                        {
                            var moduleName = Capitalized(L.Name.ToString(0, false));
                            moduleName = "RegularToAtomicRefinement" + moduleName;
                            var header = Printer.GetFStarHeaderForModule(moduleName);
                            header += Printer.GetFStarAtomicHeader();
                            var bodyStr = atomicPrinter.RegularToAtomic(L, 0) + "\n";
                            System.IO.File.WriteAllText(fstarOutputPath + moduleName + ".fst", header + '\n' + bodyStr);
                        }
                        if (H != null)
                        {
                            var moduleName = Capitalized(H.Name.ToString(0, false));
                            moduleName = "AtomicToRegularRefinement" + moduleName;
                            var header = Printer.GetFStarHeaderForModule(moduleName);
                            header += Printer.GetFStarAtomicHeader();
                            var bodyStr = atomicPrinter.AtomicToRegular(H, 0) + "\n";
                            System.IO.File.WriteAllText(fstarOutputPath + moduleName + ".fst", header + '\n' + bodyStr);
                        }

                        foreach (var proof in proofResolver.ProofRefinements)
                        {
                            LevelDecl low = proofResolver.Levels[proof.LLevelName.Name];
                            LevelDecl high = proofResolver.Levels[proof.HLevelName.Name];
                            var moduleNameLow = Capitalized(low.Name.ToString(0, false));
                            var moduleNameHigh = Capitalized(high.Name.ToString(0, false));
                            foreach (var (name, body) in proofPrinter.GetProofs(proof, low, high, 0)) {
                                System.IO.File.WriteAllText(fstarOutputPath + name + ".fst", body);
                            }
                        }
                    }
                }
            });
        }
    }
}
