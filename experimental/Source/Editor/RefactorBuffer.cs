using Editor;
using System;
using System.Collections.Generic;
using System.Linq;
using System.IO;
using System.Text;
using Microsoft.Starmada;

using StarmadaParser = Microsoft.Starmada.Parser;

namespace Starmada
{
    class RefactorBuffer
    {
        public string Buffer;
        public string OutFileName;
        public SortedDictionary<int, (int, int, string)> Schema;
        public string GetIndent(int charPos)
        {
            string s = Buffer.Remove(charPos);
            int last = s.LastIndexOf('\n');
            return new(' ', charPos - last - 1);
        }
        public RefactorBuffer(string buffer, string dumpName)
        {
            Buffer = buffer;
            OutFileName = dumpName;
            Schema = new();
        }
        public void Add((int, int) charPosRange, string candidate)
        {
            var (a, b) = charPosRange;
            Schema.Add(a, (a, b, candidate));
        }
        public void Dump()
        {
            // always replace the ones in the back
            foreach (var (_, (a, b, candidate)) in Schema.Reverse())
            {
                Buffer = Buffer.Remove(a, b - a).Insert(a, candidate);
            }
        }
    }

    class RefactorProjectBuffer
    {
        public Dictionary<string, RefactorBuffer> RefactorBuffers;
        public string OutputRoot;
        public RefactorProjectBuffer(List<string> inputs, string input, string output)
        {
            RefactorBuffers = new();
            string inputRoot = input;
            OutputRoot = output.Length == 0 ? input : output;

            input = Path.GetFullPath(input);
            output = Path.GetFullPath(output);

            // Remove overlapping check
            // if (input.StartsWith(output) || output.StartsWith(input))
            // {
            //     throw new FatalError($"Input overlaps with Output ({inputRoot}, {OutputRoot})");
            // }

            foreach (var fileName in inputs)
            {
                string fileBuffer = File.ReadAllText(fileName);

                string dumpName = fileName.Remove(0, input.Length).Insert(0, output);
                RefactorBuffers[fileName] = new(fileBuffer, dumpName);
            }
        }

        public List<string> ReadFromStdin(string checkMode)
        {
            string buffer = "";
            string tmp;
            while ((tmp = System.Console.ReadLine()) != null && tmp != "")
            {
                buffer += $"{tmp}\n";
            }
            return ReadFromString(buffer, checkMode);
        }

        public List<string> ReadFromFile(string file, string checkMode)
        {
            string buffer = File.ReadAllText(file);
            return ReadFromString(buffer, checkMode);
        }

        public List<string> ReadFromString(string buffer, string checkMode)
        {
            buffer = buffer.TrimEnd();
            List<string> res;

            if (checkMode == "deferred")
            {
                // defer the check
                res = new(buffer.Split('\n'));
            }
            else
            {
                // eager check; only parser
                string raw = $"level A {{ method main() {{ {buffer} }} }}";

                string tmpFileName = "<internal>";

                List<StmtToken> candidateTokens;
                {
                    Scanner scanner = new(
                        new MemoryStream(
                            Encoding.Default.GetBytes(raw)));
                    StarmadaParser sp = new(scanner, tmpFileName);
                    sp.Parse();
                    StarmadaProgram p = sp.program;
                    List<Statement> s = (p.Levels[0].Members[0] as MethodDecl).Stmts;
                    candidateTokens = s.Select(
                        stmt => new StmtToken(tmpFileName, stmt.FirstTok, stmt.LastTok)
                    ).ToList();
                }

                res = new(candidateTokens.Select(st => st.GetStringFromBuffer(raw)));
            }


            return res;
        }

        public void FineGrainedReplacement(List<StmtGroupToken> groupToks, List<string> candidates)
        {
            // Check if the stmtGroupTokens are all clustered; or if they all fit the candidate length
            bool allClustered = true;
            bool aligned = true;
            foreach (var groupTok in groupToks)
            {
                allClustered = (groupTok.Clustered is not null) && allClustered;
                aligned = (groupTok.Tokens.Count == candidates.Count) && aligned;
            }
            if (allClustered)
            {
                foreach (var groupTok in groupToks)
                {
                    StmtToken clustered = groupTok.Clustered;
                    string indent = RefactorBuffers[clustered.File].GetIndent(clustered.GetCharPosRange().Item1);
                    string candidate = String.Join('\n',
                        candidates.Select(c => c.Insert(0, indent))
                    ).Remove(0, indent.Length);
                    RefactorBuffers[clustered.File].Add(clustered.GetCharPosRange(), candidate);
                }
            }
            else if (aligned)
            {
                foreach (var groupTok in groupToks)
                {
                    for (int i = 0; i < groupTok.Tokens.Count; i++)
                    {
                        var tok = groupTok.Tokens[i];
                        RefactorBuffers[tok.File].Add(tok.GetCharPosRange(), candidates[i]);
                    }
                }
            }
            else
            {
                throw new FatalError("Neither all clustered nor aligned with the candidates in length");
            }
        }

        public void Dump(string outputMode, string checkMode)
        {
            // div
            string div = String.Concat(Enumerable.Repeat("=", 40));

            foreach (var (fileName, buf) in RefactorBuffers)
            {
                buf.Dump();
                if (outputMode == "file")
                {
                    // ensures that the directory exists
                    Directory.CreateDirectory(Path.GetDirectoryName(buf.OutFileName));

                    // write the file
                    Console.WriteLine($"Dumping {buf.OutFileName}.");
                    File.WriteAllLines(buf.OutFileName, new List<String> { buf.Buffer });

                    // check if deferred
                    if (checkMode == "deferred")
                    {
                        string tmpFileName = buf.OutFileName;
                        Scanner scanner = new Scanner(tmpFileName);
                        StarmadaParser sp = new StarmadaParser(scanner, tmpFileName);
                        sp.Parse();
                        // type check can be done here
                        // sp.program.TypeResolve();
                    }
                }
                else
                {
                    System.Console.WriteLine($"Output file {buf.OutFileName}:");
                    System.Console.WriteLine(div);
                    System.Console.WriteLine(buf.Buffer);
                    System.Console.WriteLine(div);
                }
            }
        }
    }
}
