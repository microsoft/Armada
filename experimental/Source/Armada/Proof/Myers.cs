using System.Collections.Generic;

namespace Microsoft.Starmada
{
    public class Diff<S, T> where S : IList<T>
    {
        private S a, b;
        private bool[,] identityMatrix;
        public class Pos
        {
            public int x, y;
            public Pos(int x, int y)
            {
                this.x = x;
                this.y = y;
            }
            public Pos(Pos pos)
            {
                this.x = pos.x;
                this.y = pos.y;
            }
            public override string ToString()
            {
                return $"({x.ToString()}, {y.ToString()})";
            }
        }
        private bool isIdentity(Pos pos)
        {
            return identityMatrix[pos.x, pos.y];
        }
        private List<(Pos, bool)> next(Pos pos)
        {
            List<(Pos, bool)> res = new();
            if (pos.x < a.Count)
            {
                res.Add((new Pos(pos.x + 1, pos.y), false));
            }
            if (pos.y < b.Count)
            {
                res.Add((new Pos(pos.x, pos.y + 1), false));
            }
            if (pos.x < a.Count && pos.y < b.Count && isIdentity(pos))
            {
                res.Add((new Pos(pos.x + 1, pos.y + 1), true));
            }
            return res;
        }
        public class Route
        {
            public List<Pos> T { get; set; }
            public int Length;
            public Route(int length = int.MaxValue)
            {
                this.T = new List<Pos>();
                this.Length = length;
            }
            /// Move forward by 1
            public Route(Route route)
            {
                this.T = new List<Pos>(route.T);
                this.Length = route.Length + 1;
            }
            public Route(Route route, Pos keyPos)
            {
                this.T = new List<Pos>(route.T);
                this.T.Add(new Pos(keyPos));
                this.Length = route.Length + 1;
            }
            /// Returns -1 if not matched
            public int MapExactForward(int index)
            {
                int l = 0;
                int r = T.Count;
                while (l < r)
                {
                    int k = (l + r) / 2;
                    if (T[k].x < index)
                    {
                        l = k + 1;
                    } else if (T[k].x > index) {
                        r = k;
                    } else {
                        return T[k].y;
                    }
                }
                return -1;
            }
            /// Returns -1 if not matched
            public int MapExactBackward(int index)
            {
                int l = 0;
                int r = T.Count;
                while (l < r)
                {
                    int k = (l + r) / 2;
                    if (T[k].y < index)
                    {
                        l = k + 1;
                    } else if (T[k].y > index) {
                        r = k;
                    } else {
                        return T[k].x;
                    }
                }
                return -1;
            }
            public override string ToString()
            {
                string res = "";
                foreach (var item in this.T)
                {
                    res += item;
                    res += " -> ";
                }
                res += "end";
                return res;
            }
        }

        private Route keyRoute;

        private void search()
        {
            int lenA = a.Count;
            int lenB = b.Count;
            Route[,] rs = new Route[lenA + 1, lenB + 1];
            for (int i = 0; i <= lenA; i++)
            {
                for (int j = 0; j <= lenB; j++)
                {
                    rs[i, j] = new Route();
                }
            }
            rs[0, 0] = new Route(0);

            for (int i = 0; i <= lenA; i++)
            {
                for (int j = 0; j <= lenB; j++)
                {
                    Pos current = new Pos(i, j);
                    foreach (var (pos, isDiag) in next(current))
                    {
                        Route r;
                        if (isDiag)
                        {
                            r = new Route(rs[i, j], current);
                        }
                        else
                        {
                            r = new Route(rs[i, j]);
                        }
                        if (rs[pos.x, pos.y].Length > r.Length)
                        {
                            rs[pos.x, pos.y] = r;
                        }
                    }
                }
            }
            keyRoute = rs[lenA, lenB];
        }

        // Init Diff
        public Diff(S a, S b, EqualityComparer<T> comparator)
        {
            this.a = a;
            this.b = b;
            int lenA = a.Count;
            int lenB = b.Count;
            this.identityMatrix = new bool[lenA, lenB];
            for (int i = 0; i < lenA; i++)
            {
                for (int j = 0; j < lenB; j++)
                {
                    this.identityMatrix[i, j] = comparator.Equals(a[i], b[j]);
                }
            }
            this.search();
        }

        public int MapExactForward(int index)
        {
            return keyRoute.MapExactForward(index);
        }
        public int MapExactBackward(int index)
        {
            return keyRoute.MapExactBackward(index);
        }
    }
}