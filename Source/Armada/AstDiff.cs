using System;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Armada {
  // helper class for ASTNode
  [Flags]
  public enum ASTFlag {
    NONE = 0x0,
    LHS = 0x1,
    VAR = 0x2,
    FIELD = 0x4,
    ASSIGN = 0x8,
    VARDECL = 0x10,
    ASSUME = 0x20
  }

  public abstract class ASTNode: IComparable {
    public abstract int SelfHash {get; }
    public int Height = 0;
    public int TraverseId = -1;
    public ASTFlag Flags = ASTFlag.NONE;
    public MemberDecl Var = null;
    public ArmadaPC startPC = null;
    public ArmadaPC endPC = null;
    protected List<ASTNode> children = new List<ASTNode>();
    public ASTNode parent = null;
    public bool exploreExpr = true;

    public abstract IEnumerable<ASTNode> EnumerateChildren {
      get;
    }

    public abstract string Value {
      get;
    }

    public virtual string Stringify() {
      return Value;
    }

    public int TreeHash {
      get {
        return 0; //TODO
      }
    }

    protected ASTNode(ASTNode parent) {
      this.parent = parent;
    }

    protected void initHeight() {
      foreach (var child in EnumerateChildren) {
        this.Height = this.Height < child.Height + 1 ? child.Height + 1 : this.Height;
      }
    }

    public int CompareTo(Object rhs) {
      if (rhs == null) {
        return 1;
      }
      if (! (rhs is ASTNode)) {
        throw new ArgumentException("Not designed for other cases!");
      }

      if (this.Height.CompareTo(((ASTNode) rhs).Height) != 0) {
        return this.Height.CompareTo(((ASTNode) rhs).Height);
      }
      else {
        return 1;
      }
    }

    protected ASTNode root() {
      if (this.parent != null) {
        return this.parent.root();
      }
      else {
        return this;
      }
    }

    protected bool ExploreExpr {
      get {
        return root().exploreExpr;
      }
    }
  }

  public class ASTClassNode: ASTNode {
    ClassDecl Class;
    public ASTClassNode(ClassDecl Class, ASTNode parent, bool exploreExpr = true) : base(parent) {
      this.Class = Class;
      this.exploreExpr = exploreExpr;
      initHeight();
    }
    public override int SelfHash {
      get {
        return 0; //TODO:
      }
    }

    public override IEnumerable<ASTNode> EnumerateChildren {
      get {
        if (this.children.Any()) {
          foreach (var member in this.children) {
            yield return member;
          }
          yield break;
        }
        foreach (var member in Class.Members) {
          this.children.Add(new ASTMemberNode(member, this));
          yield return this.children.Last();
        }
      }
    }

    public override string Value {
      get {
        return Class.tok.val;
      }
    }
  }

  public class ASTMemberNode: ASTNode {
    MemberDecl Member;

    public ASTMemberNode(MemberDecl Member, ASTNode parent) : base(parent) {
      if (Member is Field) {
        Flags = Flags | ASTFlag.FIELD;
        Var = Member;
      }
      this.Member = Member;
      initHeight();
    }

    public override int SelfHash {
      get {
        return 0;
      }
    }

    public override IEnumerable<ASTNode> EnumerateChildren {
      get {
        if (this.children.Any()) {
          foreach (var member in this.children) {
            yield return member;
          }
          yield break;
        }
        if (exploreExpr) {
          foreach (var expression in Member.SubExpressions) {
            if (expression == null) {
              Console.WriteLine("NULL!!!!");
            }
            this.children.Add(new ASTExpressionNode(expression, this));
            yield return this.children.Last();
          }
        }
        if (Member is Method && ((Method)Member).Body != null) {
          this.children.Add(new ASTStatementNode(((Method)Member).Body, this));
          yield return this.children.Last();
        }
      }
    }

    public IEnumerable<string> EnumerateFormals {
      get {
        if (Member is Method) {
          var mthd = (Method) Member;
          foreach (var formal in mthd.Ins) {
            yield return formal.Tok.val;
          }
          foreach (var formal in mthd.Outs) {
            yield return formal.Tok.val;
          }
        }
      }
    }

    public override string Value {
      get {
        return Member.Name;
      }
    }
  }

  public class ASTExpressionNode: ASTNode {
    Expression Exp;

    public ASTExpressionNode(Expression Exp, ASTNode parent, ASTFlag flags = ASTFlag.NONE) : base(parent) {
      if (Exp.Resolved is MemberSelectExpr) {
        Flags = Flags | ASTFlag.VAR | flags;
        Var = ((MemberSelectExpr)Exp.Resolved).Member;
      }
      this.Exp = Exp;
      initHeight();
    }

    public override int SelfHash {
      get {
        return 0; //TODO
      }
    }

    public override IEnumerable<ASTNode> EnumerateChildren {
      get {
        if (this.children.Any()) {
          foreach (var member in this.children) {
            yield return member;
          }
          yield break;
        }
        foreach (var expression in Exp.SubExpressions) {
          this.children.Add(new ASTExpressionNode(expression, this));
          yield return this.children.Last();
        }
        if (Exp is ApplySuffix) {
          this.children.Add(new ASTExpressionNode(((ApplySuffix)Exp).Lhs, this));
          yield return this.children.Last();
        }
      }
    }

    public override string Value {
      get {
        return Exp.tok.val;
      }
    }
  }

  public class ASTStatementNode: ASTNode {
    Statement Stmt;
    public ASTStatementNode(Statement Stmt, ASTNode parent) : base(parent) {
      if (Stmt is UpdateStmt) {
        Flags = Flags | ASTFlag.ASSIGN;
      }
      if (Stmt is VarDeclStmt) {
        Flags = Flags | ASTFlag.VARDECL;
      }
      if (Stmt is AssumeStmt) {
        Flags = Flags | ASTFlag.ASSUME;
      }
      this.Stmt = Stmt;
      this.startPC = Stmt.Parsed.StartPC;
      this.endPC = Stmt.Parsed.EndPC;
      initHeight();
    }

    public override int SelfHash {
      get {
        return 0; //TODO
      }
    }

    public override IEnumerable<ASTNode> EnumerateChildren {
      get {
        if (this.children.Any()) {
          foreach (var member in this.children) {
            yield return member;
          }
          yield break;
        }

        if (Stmt is UpdateStmt update) {
          foreach (var ss in update.ResolvedStatements) {
            if (ExploreExpr) {
              foreach (var expression in ss.SubExpressions)
              {
                this.children.Add(new ASTExpressionNode(expression, this));
                yield return this.children.Last();
              }
            }
            foreach (var stmt in ss.SubStatements)
            {
              this.children.Add(new ASTStatementNode(stmt, this));
              yield return this.children.Last();
            }
          }
          yield break;
        }

        if (ExploreExpr) {
          foreach (var expression in Stmt.SubExpressions) {
            this.children.Add(new ASTExpressionNode(expression, this));
            yield return this.children.Last();
          }
        }

        // Enumerate through substatements unless this is a VarDeclStmt.
        // After all, the Update substatement of a VarDeclStmt isn't
        // really a statement in our model.

        if (!(Stmt is VarDeclStmt)) {
          foreach (var s in Stmt.SubStatements) {
            foreach (var stmt in UnwrapAtomicBlock(s)) {
              this.children.Add(new ASTStatementNode(stmt, this));
              yield return this.children.Last();
            }
          }
        }
      }
    }

    private static IEnumerable<Statement> UnwrapAtomicBlock(Statement stmt) {
      if (stmt is ExplicitYieldBlockStmt) {
        foreach (var s in stmt.SubStatements) {
          yield return s;
        }
      }
      else {
        yield return stmt;
      }
    }

    public override string Value {
      get {
        if (Stmt is VarDeclStmt varDecl) {
          return "vardecl: " + String.Join(",", varDecl.Locals.Select(local => local.Name));
        }
        else if (Stmt is UpdateStmt update) {
          var prefix = "update: ";
          if (update.Rhss.Count >= 1) {
            var rhs = update.Rhss[0];
            if (rhs is CreateThreadRhs) {
              prefix = "create_thread: ";
            }
            else if (rhs is MallocRhs) {
              prefix = "malloc: ";
            }
            else if (rhs is CallocRhs) {
              prefix = "calloc: ";
            }
            else if (rhs is ExprRhs expr && expr.Expr is ApplySuffix suffix &&
                     suffix.Lhs is NameSegment) {
              prefix = "call: ";
            }
          }
          return prefix + String.Join(",", update.Lhss.Select(lhs => Printer.ExprToString(lhs)));
        }
        else if (Stmt is BlockStmt block) {
          return $"block";
        }
        return Stmt.Tok.val;
      }
    }

    public override string Stringify() {
      if (Value.Length > 20) {
        return Value.Substring(0, 17) + "... #";
      }
      else return Value + " #";
    }
  }

  public class ASTHelper {
    // Enumerate only the declaration that are represented in
    public static int indent = 0;

    public static IEnumerable<ASTNode> Traverse(ASTNode node, bool postOrder = false, bool statementOnly = false) {
      if (statementOnly && (node is ASTExpressionNode || node is ASTStatementNode && (node.startPC == null || node.endPC == null))) {
        yield break;
      }
      if (! postOrder) {
        yield return node;
      }
      indent += 2;
      foreach(var child in node.EnumerateChildren) {
        foreach(var descendant in Traverse(child, postOrder, statementOnly)) {
          yield return descendant;
        }
      }

      indent -= 2;
      if (postOrder) {
        yield return node;
      }
    }

    public static void Print(ASTNode root, bool postOrder = false) {
      indent = 0;
      foreach (var node in Traverse(root, postOrder, true)) {
        Console.Write(new string(' ', indent) + node.Stringify() + $": {node.TraverseId}");
        if (node.startPC != null && node.endPC != null) {
          Console.WriteLine($" - [{node.startPC} to {node.endPC}]");
        }
        else {
          Console.WriteLine();
        }
      }
    }

    public static void InitId(ASTNode root, bool postOrder = false) {
      var id = 0;
      foreach (var node in Traverse(root, postOrder)) {
        node.TraverseId = id ++;
      }
    }
  }

  // Currently not using
  public class RTEDAlgorithm {
    private List<ASTNode> srcList, dstList;
    public RTEDAlgorithm(ASTNode source, ASTNode destination) {
      srcList = new List<ASTNode>{source};
      dstList = new List<ASTNode>{destination};
    }

    private static ASTNode Expand(List<ASTNode> list) {
      ASTNode rightmost = list.Last();
      list.RemoveAt(list.Count() - 1);

      list.InsertRange(list.Count(), rightmost.EnumerateChildren);

      return rightmost;
    }

    private static void Restore(List<ASTNode> list, ASTNode node) {
      foreach (var child in node.EnumerateChildren) {
        list.Remove(child);
      }

      list.Insert(list.Count(), node);
    }

    public int CalcMap() {
      ASTNode u, v;
      int cost;
      if (srcList.Count() == 0) {
        if (dstList.Count() == 0) {
          return 0;
        }
        else {
          v = Expand(dstList);
          cost = CalcMap();
          Restore(dstList, v);
          return cost + 2;
        }
      }
      else if (dstList.Count() == 0){
        u = Expand(srcList);
        cost = CalcMap();
        Restore(srcList, u);
        return cost + 2;
      }

      int minCost = int.MaxValue;
      v = Expand(dstList);
      cost = CalcMap();
      Restore(dstList, v);
      minCost = cost + 2 < minCost ? cost + 2 : minCost;
      u = Expand(srcList);
      cost = CalcMap();
      Restore(srcList, u);
      minCost = cost + 2 < minCost ? cost + 2 : minCost;

      // Tree situation
      if (srcList.Count() == 1 && dstList.Count() == 1) {
        Expand(srcList);
        Expand(dstList);
        cost = CalcMap();
        Restore(srcList, u);
        Restore(dstList, v);
        if (u.GetType() == v.GetType()) {
          if (u.Value == v.Value) {
            minCost = cost < minCost ? cost : minCost;
          }
          else {
            minCost = cost + 1 < minCost ? cost + 1 : minCost;
          }
        }
        else {
          minCost = cost + 2 < minCost ? cost + 2 : minCost;
        }
      }
      else {
        srcList.RemoveAt(srcList.Count() - 1);
        dstList.RemoveAt(dstList.Count() - 1);
        cost = CalcMap();
        List<ASTNode> backupSrc = srcList, backupDst = dstList;
        srcList = new List<ASTNode>{u};
        dstList = new List<ASTNode>{v};
        cost += CalcMap();
        srcList = backupSrc;
        dstList = backupDst;
        srcList.Insert(srcList.Count(), u);
        dstList.Insert(dstList.Count(), v);
        minCost = cost < minCost ? cost : minCost;
      }

      return minCost;
    }
  }

  public class ASTDiff {
    public ASTNode src, tgt;
    private static int minHeight = -1;
    public Dictionary<ASTNode, ASTNode> map = new Dictionary<ASTNode, ASTNode>();
    public List<ASTNode> unmatched = new List<ASTNode>();
    public ASTDiff(ClassDecl src, ClassDecl tgt, bool exploreExpr = true) {
      this.src = new ASTClassNode(src, null, exploreExpr);
      this.tgt = new ASTClassNode(tgt, null, exploreExpr);
    }

    // Pop all the most heighted nodes from the queue
    private List<ASTNode> Pop(SortedSet<ASTNode> queue) {
      var maxHeight = queue.Max().Height;

      var maxList = new List<ASTNode>();

      while ((queue.Max()?.Height ?? -1) == maxHeight) {
        maxList.Add(queue.Max());
        queue.Remove(queue.Max());
      }

      return maxList;
    }

    // Add all the children of the nodes in the list into the queue
    private void Open(SortedSet<ASTNode> queue, IList<ASTNode> list) {
      foreach(var node in list) {
        foreach(var subNode in node.EnumerateChildren) {
          queue.Add(subNode);
        }
      }
    }

    // calculate the weight function
    private double Dice(ASTNode src, ASTNode tgt, IDictionary<ASTNode, ASTNode> map) {
      int denominator = 0, numerator = 0;
      foreach(var srcNode in ASTHelper.Traverse(src)) {
        foreach (var tgtNode in ASTHelper.Traverse(tgt)) {
          if (map.ContainsKey(srcNode) && Object.ReferenceEquals(map[srcNode], tgtNode)) {
            ++ numerator;
          }
        }
      }

      denominator = ASTHelper.Traverse(src).Count() + ASTHelper.Traverse(tgt).Count() - 2; // deleting themselves

      return 2.0 * ((double) numerator) / ((double) denominator);
    }

    // Decide whether two tree are isomorphic
    // TODO(luke): use hash algorithm to optimize the time complexity
    private bool Isomorphic(ASTNode src, ASTNode tgt) {
      if (src.Height != tgt.Height) {
        return false;
      }
      if (src.Value != tgt.Value) {
        return false;
      }
      var srcChildren = src.EnumerateChildren.ToList();
      var tgtChildren = tgt.EnumerateChildren.ToList();

      if (srcChildren.Count() != tgtChildren.Count()) {
        return false;
      }

      for (int i = 0; i < srcChildren.Count(); ++ i) {
        if (! Isomorphic(srcChildren[i], tgtChildren[i])) {
          return false;
        }
      }

      return src.Value == tgt.Value;
    }

    private IEnumerable<ASTNode> FindCandidates(ASTNode node, ASTNode root) {
      foreach(var candidate in ASTHelper.Traverse(root)) {
        if (candidate.Value == node.Value && ! map.ContainsValue(candidate)) {
          foreach(var child in node.EnumerateChildren) {
            if (map.ContainsKey(child) && map[child].parent == candidate) {
              yield return candidate;
              break;
            }
          }
        }
      }
    }

    // Top-Down(preOrder) scan of the AST tree, finish course matches
    private void TopDown() {
      var prioritySrc = new SortedSet<ASTNode>();
      var priorityTgt = new SortedSet<ASTNode>();

      var candidates = new List<Tuple<ASTNode, ASTNode>>();

      prioritySrc.Add(this.src);
      priorityTgt.Add(this.tgt);

      while (Math.Min(prioritySrc.Max()?.Height ?? -1, priorityTgt.Max()?.Height ?? -1) > minHeight) {
        if (prioritySrc.Max().Height != priorityTgt.Max().Height) {
          if (prioritySrc.Max().Height > priorityTgt.Max().Height) {
            var maxList = Pop(prioritySrc);
            Open(prioritySrc, maxList);
          }
          else {
            var maxList = Pop(priorityTgt);
            Open(priorityTgt, maxList);
          }
        }
        else {
          var srcList = Pop(prioritySrc);
          var tgtList = Pop(priorityTgt);
          foreach (var srcNode in srcList) {
            foreach (var tgtNode in tgtList) {
              if (Isomorphic(srcNode, tgtNode)) {
                bool flag = false;
                foreach (var node in ASTHelper.Traverse(tgt)) {
                  if (Isomorphic(srcNode, node) && tgtNode.TraverseId != node.TraverseId) {
                    flag = true;
                    break;
                  }
                }
                if (! flag) {
                  foreach (var node in ASTHelper.Traverse(src)) {
                    if (Isomorphic(node, tgtNode) && srcNode.TraverseId != node.TraverseId) {
                      flag = true;
                      break;
                    }
                  }
                }
                if (! flag) {
                  map.Add(srcNode, tgtNode);
                }
                else {
                  candidates.Add(Tuple.Create(srcNode, tgtNode));
                }
              }
            }
          }
          Open(prioritySrc, srcList);
          Open(priorityTgt, tgtList);
        }
      }

      candidates = new List<Tuple<ASTNode, ASTNode>>(candidates.OrderBy(tuple => {
          if (tuple.Item1.parent == null || tuple.Item2.parent == null) { // TODO(luke): what about root?
            return Dice(tuple.Item1, tuple.Item2, map);
          }
          else {
            return Dice(tuple.Item1.parent, tuple.Item2.parent, map);
          }
          }).Where(tuple => Dice(tuple.Item1.parent, tuple.Item2.parent, map) > 0));

      while(candidates.Count() > 0) {
        var pair = candidates.Last();
        var src = pair.Item1;
        var tgt = pair.Item2;
        foreach(var srcNode in ASTHelper.Traverse(src)) {
          foreach (var tgtNode in ASTHelper.Traverse(tgt)) {
            if (Isomorphic(srcNode, tgtNode) && ! map.ContainsKey(srcNode) && !map.ContainsValue(tgtNode)) {
              map.Add(srcNode, tgtNode);
            }
          }
        }
        candidates.RemoveAt(candidates.Count() - 1);
      }
    }

    private void bottomUp() {
      foreach (var node in ASTHelper.Traverse(src, true)) {
        if (! map.ContainsKey(node)) {
          bool flag = false;
          foreach (var child in node.EnumerateChildren) {
            if (map.ContainsKey(child)) {
              flag = true;
              break;
            }
          }
          if (flag) {
            List<ASTNode> candidates = FindCandidates(node, tgt).ToList();

            double dice = 0;
            ASTNode elected = null;
            foreach(var candidate in candidates) {
              double temp = Dice(node, candidate, map);
              if (temp > dice) {
                elected = candidate;
                dice = temp;
              }
            }

            if (elected != null && dice > 0.5) {
              map.Add(node, elected);
              // TODO(luke): For transformation-specific algorithms
            }
            else if (elected != null) {
              Console.WriteLine($"{elected.TraverseId} elected for {node.TraverseId}, but dice=${dice} failed");
            }
          }
        }
      }
    }

    public void Diff() {
      ASTHelper.InitId(this.src);
      ASTHelper.InitId(this.tgt);

      TopDown();
      bottomUp();

      foreach(var srcNode in ASTHelper.Traverse(src)) {
        if (! map.ContainsKey(srcNode)) {
          unmatched.Add(srcNode);
          map.Add(srcNode, null);
        }
      }
    }

    private bool AdjacentPC(ArmadaPC lhs, ArmadaPC rhs) {
      if (lhs.methodName == null || rhs.methodName == null) {
        Console.WriteLine("Invalid PC");
        return false;
      }

      return lhs.methodName == rhs.methodName && lhs.instructionCount + 1 == rhs.instructionCount;
    }

    private ArmadaPC GetRoot(ArmadaPC key, Dictionary<ArmadaPC, ArmadaPC> unionFind) {
      if (unionFind.ContainsKey(key)) {
        unionFind[key] = GetRoot(unionFind[key], unionFind);
      }
      else {
        return key;
      }

      return unionFind[key];
    }

    public Dictionary<ArmadaPC, ArmadaPC> VariableHiding() {
      Diff();

      Dictionary<ArmadaPC, ArmadaPC> pcMap = new Dictionary<ArmadaPC, ArmadaPC>();
      Dictionary<ArmadaPC, ArmadaPC> unionFind = new Dictionary<ArmadaPC, ArmadaPC>();

      foreach (var pair in map) {
        if (pair.Value != null &&
            pair.Key.startPC != null && pair.Key.endPC != null &&
            pair.Value.startPC != null && pair.Value.endPC != null) {
          if (pcMap.ContainsKey(pair.Key.startPC) && pcMap[pair.Key.startPC] != pair.Value.startPC) {
            Console.WriteLine($"pc {pair.Key.startPC} is mapped to {pcMap[pair.Key.startPC]} previously and mapped to {pair.Value.startPC} now");
          }
          else {
            pcMap[pair.Key.startPC] = pair.Value.startPC;
          }
          if (pcMap.ContainsKey(pair.Key.endPC) && pcMap[pair.Key.endPC] != pair.Value.endPC) {
            Console.WriteLine($"pc {pair.Key.endPC} is mapped to {pcMap[pair.Key.endPC]} previously and mapped to {pair.Value.endPC} now");
          }
          else {
            pcMap[pair.Key.endPC] = pair.Value.endPC;
          }
        }
        else if (pair.Value == null && pair.Key.startPC != null && pair.Key.endPC != null && AdjacentPC(pair.Key.startPC, pair.Key.endPC)) {
          // we need merge the pcs into a set
          var startRoot = GetRoot(pair.Key.startPC, unionFind);
          var endRoot = GetRoot(pair.Key.endPC, unionFind);
          if (pcMap.ContainsKey(startRoot)) {
            unionFind[endRoot] = startRoot;
          }
          else {
            unionFind[startRoot] = endRoot;
            if (! pcMap.ContainsKey(endRoot)) {
              Console.WriteLine($"{startRoot} merged with {endRoot} without existing PC map");
            }
          }
         }
      }

      foreach (var pair in unionFind) {
        // the root should be always have a mapped pc
        if (!pcMap.ContainsKey(pair.Value)) {
          Console.WriteLine($"the root ({pair.Value}) of set is not mapped");
        }
        else if (pcMap.ContainsKey(pair.Key) && pcMap[pair.Key] != pcMap[pair.Value]) {
          Console.WriteLine($"the root ({pair.Value}) of the set ({pair.Key}) maps to different pc ({pcMap[pair.Value]}) ({pcMap[pair.Key]})");
        }
        else {
          pcMap[pair.Key] = pcMap[pair.Value];
        }
      }

      return pcMap;
    }

    public HashSet<ArmadaPC> AssumeIntro(Dictionary<ArmadaPC, ArmadaPC> pcMap) {
      Diff();

      HashSet<ArmadaPC> assumeIntroduced = new HashSet<ArmadaPC>();
      // introduced assume statements should not be mapped from any low-level assume statement

      foreach (var pair in map) {
        if (pair.Value != null &&
            pair.Key.startPC != null && pair.Key.endPC != null &&
            pair.Value.startPC != null && pair.Value.endPC != null) {
          if (pcMap.ContainsKey(pair.Key.startPC) && pcMap[pair.Key.startPC] != pair.Value.startPC) {
          }
          else {
            pcMap[pair.Key.startPC] = pair.Value.startPC;
          }
          if (pcMap.ContainsKey(pair.Key.endPC) && pcMap[pair.Key.endPC] != pair.Value.endPC) {
          }
          else {
            pcMap[pair.Key.endPC] = pair.Value.endPC;
          }
        }
      }

      foreach (var node in ASTHelper.Traverse(tgt, false, true)) {
        if (! map.ContainsValue(node)) {
          // this statement is not in the map, therefore it should be an assume statement
          if ((node.Flags & ASTFlag.ASSUME) != ASTFlag.ASSUME) {
            Console.WriteLine($"{node.TraverseId} is not in the map, but not an assume statement");
          }
          else {
            assumeIntroduced.Add(node.startPC);
            assumeIntroduced.Add(node.endPC);
          }
        }
      }

      return assumeIntroduced;
    }
  }
}
