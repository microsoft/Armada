using System.Collections.Generic;
using System.IO;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using Editor;

namespace Starmada
{
    class IOUtils
    {
        public static void DeleteArm(DirectoryInfo dir)
        {
            // Cache directories before we start copying
            DirectoryInfo[] dirs = dir.GetDirectories();

            // Get the files in the source directory and copy to the destination directory
            foreach (FileInfo file in dir.GetFiles())
            {
                if (file.Extension == ".arm")
                {
                    file.Delete();
                }
            }

            // Recursively call this method into subDir
            foreach (DirectoryInfo subDir in dirs)
            {
                // Jump the .build dir
                if (subDir.Name == ".build")
                {
                    continue;
                };
                DeleteArm(subDir);
            }
        }

        public static void CopyArm(DirectoryInfo dir, DirectoryInfo dest)
        {
            // Cache destination directory string
            string destDir = dest.FullName;

            // Cache directories before we start copying
            DirectoryInfo[] dirs = dir.GetDirectories();

            // Create the destination directory
            Directory.CreateDirectory(destDir);

            // Get the files in the source directory and copy to the destination directory
            foreach (FileInfo file in dir.GetFiles())
            {
                if (file.Extension == ".arm")
                {
                    string targetFilePath = Path.Combine(destDir, file.Name);
                    file.CopyTo(targetFilePath);
                }
            }

            // Recursively call this method into subDir
            foreach (DirectoryInfo subDir in dirs)
            {
                // Jump the .build dir
                if (subDir.Name == ".build")
                {
                    continue;
                };
                string newDestinationDir = Path.Combine(destDir, subDir.Name);
                CopyArm(subDir, new(newDestinationDir));
            }
        }

        public class Cache
        {

            public List<string> InputFiles { get; }
            public List<StmtGroupToken> StmtGroupTokens { get; }

            [JsonConstructor]
            public Cache(List<string> inputFiles, List<StmtGroupToken> stmtGroupTokens)
            {
                InputFiles = inputFiles;
                StmtGroupTokens = stmtGroupTokens;
            }

            public static string PathBuild()
            {
                return ".build";
            }
            public static string PathCache()
            {
                Directory.CreateDirectory(PathBuild());
                return ".build/.cache.json";
            }

            public void MemDump()
            {
                string jsonCache = JsonSerializer.Serialize(this);
                File.WriteAllText(PathCache(), jsonCache);
            }

            public static Cache MemLoad()
            {
                string jsonCache = File.ReadAllText(PathCache());
                Cache c = JsonSerializer.Deserialize<Cache>(jsonCache);
                return c;
            }
        }
    }
}