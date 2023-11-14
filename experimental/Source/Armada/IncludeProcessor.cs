
using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;

namespace Microsoft.Starmada {
    public class IncludeProcessor {
        string inputFile;

        HashSet<string> seenFiles;

        public IncludeProcessor(string inputFile) {
            seenFiles = new HashSet<string>();
            this.inputFile = inputFile;
        }

        public string processIncludes() {
            Queue<string> includeFiles = new Queue<string>();
            includeFiles.Enqueue(inputFile);
            seenFiles.Add(inputFile);
            string workingDir = inputFile.Substring(0, inputFile.LastIndexOf("/") + 1);

            string outputFilename = Path.GetTempFileName();
            StreamWriter sw = File.AppendText(outputFilename);

            while (includeFiles.Count > 0) {
                string currFile = includeFiles.Dequeue();
                Scanner scanner = new Scanner(currFile);

                Token tok = scanner.Peek();
                int lastPos = 0;
                while (tok.val == "include") {
                    string nextFilename = scanner.Peek().val;
                    string nextFile = workingDir + nextFilename.Substring(1, nextFilename.Length-2);
                    if (!seenFiles.Contains(nextFile)) {
                        includeFiles.Enqueue(nextFile);
                    }
                    seenFiles.Add(nextFile);
                    lastPos = (int)scanner.buffer.Pos;
                    tok = scanner.Peek();
                }
                string fileContent = File.ReadAllText(currFile);
                sw.Write(scanner.buffer.GetString(lastPos, fileContent.Length));
            }
            sw.Close();
            return outputFilename;
        }
    }
}