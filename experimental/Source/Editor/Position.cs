namespace Editor
{
    public class PositionSelection
    {
        public string File;
        public (int, int) Start;
        public bool Selection;
        public (int, int) End;
        public PositionSelection(string path, string s)
        {
            System.IO.FileInfo file = new(path);
            File = file.FullName;
            if (s.Contains('-'))
            {
                var x = s.Split('-');
                Start = parsePosition(x[0]);
                End = parsePosition(x[1]);
                Selection = true;
            }
            else
            {
                Start = parsePosition(s);
                Selection = false;
            }
        }
        private (int, int) parsePosition(string s)
        {
            var x = s.Split(':');
            return (int.Parse(x[0]), int.Parse(x[1]));
        }
    }
}