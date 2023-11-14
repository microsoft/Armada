using System.Collections.Generic;
using System.IO;
using CommandLine;

using CommandLineParser = CommandLine.Parser;
using Editor;

namespace Starmada
{
    class Editor
    {
        [Verb("backup", HelpText = "Clean `.build` and duplicate the current project.")]
        public class BackupOpts
        {
            public string Destination { get; set; } = ".build/backup";
        }

        // Clean `.build` and duplicate the current project. Effectively `cp -f`.
        public static int Backup(BackupOpts o)
        {
            if (Directory.Exists(o.Destination))
            {
                Directory.Delete(o.Destination, true);
            }

            DirectoryInfo cur = new(Directory.GetCurrentDirectory());
            DirectoryInfo dest = Directory.CreateDirectory(o.Destination);
            if (!dest.Exists || !cur.Exists)
            {
                throw new DirectoryNotFoundException(
                    $"One of the directories involved not valid:\n\t{cur.FullName}\n\t{dest.FullName}"
                );
            }

            IOUtils.CopyArm(cur, dest);

            return 0;
        }

        [Verb("extract", HelpText = "Given a caret position, extract information for the refactor process.")]
        public class ExtractOpts
        {
            // the caret information
            [Option('f', "file", Required = true, HelpText = "Select file.")]
            public string FileName { get; set; }
            [Option('p', "position", Required = true, HelpText = "Select position.")]
            public string Position { get; set; }

            // level of propagation
            [Option('l', "low", Required = false, HelpText = "Set lowest propagating level.")]
            public IdentStr LLevel { get; set; }
            [Option('h', "high", Required = false, HelpText = "Set highest propagating level.")]
            public IdentStr HLevel { get; set; }

            // caret source code
            public string CaretCandidates { get; set; } = ".build/candidates";
        }

        // Given a caret position, extract information for the refactor process.
        // Needs most of the user's input.
        public static int Extract(ExtractOpts o)
        {
            // init driver
            Driver d = new Driver(Directory.GetCurrentDirectory()).Run(
                new PositionSelection(o.FileName, o.Position),
                (o.LLevel, o.HLevel)
            );
            // init mapper and perform mapping
            Mapper m = new(d.Project, d.LevelRange);
            List<StmtGroupLoc> groupLocs = m.IdentifyByStatementSelection(d.CaretRangeLoc);
            List<StmtGroupToken> groupToks = d.StmtGroupLocToToken(groupLocs);

            d.DumpCaretCandidates(o.CaretCandidates);

            IOUtils.Cache c = new(d.InputFiles, groupToks);
            c.MemDump();

            return 0;
        }

        [Verb("apply", HelpText = "Apply the refactor from candidates.")]
        public class ApplyOpts
        {
            public string Candidates { get; set; } = ".build/candidates";
        }

        // Apply the refactor from candidates.
        public static int Apply(ApplyOpts o)
        {
            string current = Directory.GetCurrentDirectory();
            IOUtils.Cache c = IOUtils.Cache.MemLoad();
            // perform refactor
            RefactorProjectBuffer r = new(c.InputFiles, current, current);
            List<string> candidates = r.ReadFromFile(o.Candidates, "deferred");
            r.FineGrainedReplacement(c.StmtGroupTokens, candidates);
            r.Dump("file", "deferred");
            return 0;
        }

        [Verb("restore", HelpText = "Clean current project and restore previous state.")]
        public class RestoreOpts
        {
            public string Source { get; set; } = ".build/backup";
        }

        // Restore the old project if something went wrong.
        // Clean current project and restore previous state.
        public static int Restore(RestoreOpts o)
        {
            DirectoryInfo src = new(o.Source);
            DirectoryInfo cur = new(Directory.GetCurrentDirectory());
            if (!src.Exists || !cur.Exists)
            {
                throw new DirectoryNotFoundException(
                    $"One of the directories involved not valid:\n\t{cur.FullName}\n\t{src.FullName}"
                );
            }

            IOUtils.DeleteArm(cur);
            IOUtils.CopyArm(src, cur);

            return 0;
        }

        [Verb("shoot", HelpText = "One pass mode with all options.")]
        public class Options
        {
            // level of propagation
            [Option('l', "low", Required = false, HelpText = "Set lowest propagating level.")]
            public IdentStr LLevel { get; set; }
            [Option('h', "high", Required = false, HelpText = "Set highest propagating level.")]
            public IdentStr HLevel { get; set; }

            // the new input arguments
            [Option('f', "file", Required = true, HelpText = "Select file.")]
            public string FileName { get; set; }
            [Option('p', "position", Required = true, HelpText = "Select position.")]
            public string Position { get; set; }

            // output mode
            [Option('m', "mode", Default = "file", Required = false, HelpText = "Choose output mode [stdout/file].")]
            public string OutputMode { get; set; }

            // deferred check
            [Option('c', "check", Default = "deferred", Required = false, HelpText = "Choose parser and type check mode [eager/deferred].")]
            public string CheckMode { get; set; }

            // input dir
            [Value(0, Required = true, MetaName = "input_dir", HelpText = "Input dir of the project")]
            public string Input { get; set; }
            // output dir
            [Option('o', "output", Required = false, HelpText = "Output dir of the project")]
            public string Output { get; set; }
        }

        static void Main(string[] args)
        {
            CommandLineParser.Default
            .ParseArguments<ExtractOpts, ApplyOpts, BackupOpts, RestoreOpts, Options>(args)
            .MapResult(
                (BackupOpts o) => Backup(o),
                (ExtractOpts o) => Extract(o),
                (ApplyOpts o) => Apply(o),
                (RestoreOpts o) => Restore(o),
                (Options o) =>
                {
                    // init driver
                    Driver d = new Driver(o.Input).Run(
                        new PositionSelection(o.FileName, o.Position),
                        (o.LLevel, o.HLevel)
                    );
                    // init mapper and perform mapping
                    Mapper m = new(d.Project, d.LevelRange);
                    List<StmtGroupLoc> groupLocs = m.IdentifyByStatementSelection(d.CaretRangeLoc);
                    List<StmtGroupToken> groupToks = d.StmtGroupLocToToken(groupLocs);

                    // perform refactor
                    RefactorProjectBuffer r = new(d.InputFiles, o.Input, o.Output);
                    List<string> candidates = r.ReadFromStdin(o.CheckMode);
                    r.FineGrainedReplacement(groupToks, candidates);
                    r.Dump(o.OutputMode, o.CheckMode);
                    return 0;
                },
                err => 1
            );
        }
    }
}
