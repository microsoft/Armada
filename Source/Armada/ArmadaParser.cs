using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada
{
  public class ParseInfo
  {
    public Program prog;
    public ArmadaSymbolTable symbols;
    public MethodInfo methodInfo;
    public ArmadaWhileStatement innermostEnclosingWhile;

    public ParseInfo(Program i_prog, ArmadaSymbolTable i_symbols, MethodInfo i_methodInfo)
    {
      prog = i_prog;
      symbols = i_symbols;
      methodInfo = i_methodInfo;
      innermostEnclosingWhile = null;
    }

    public ParseInfo Clone()
    {
      var other = new ParseInfo(prog, symbols, methodInfo);
      other.innermostEnclosingWhile = this.innermostEnclosingWhile;
      return other;
    }
  }

  public abstract class ArmadaStatement
  {
    protected ParseInfo parse;
    protected ArmadaPC startPC;
    protected ArmadaPC endPC;

    public virtual Statement Stmt { get { return null; } }
    public ArmadaPC StartPC { get { return startPC; } }
    public ArmadaPC EndPC { get { return endPC; } }

    public ArmadaStatement(ParseInfo i_parse)
    {
      parse = i_parse;
      startPC = null;
      endPC = null;
    }

    public static ArmadaStatement ParseStatementInternal(ParseInfo parse, Statement stmt)
    {
      if (stmt == null)
      {
        return null;
      }
      else if (stmt is BlockStmt)
      {
        var s = (BlockStmt)stmt;
        return new ArmadaBlockStatement(parse, s);
      }
      else if (stmt is UpdateStmt)
      {
        var s = (UpdateStmt)stmt;

        if (s.Rhss.Count == 1) {
          var rhs = s.Rhss[0];
          if (rhs is ExprRhs) {
            var ex = (ExprRhs)rhs;
            if (ex.Expr is ApplySuffix) {
              var suffix = (ApplySuffix)ex.Expr;
              if (suffix.Lhs is NameSegment) {
                var suffixName = (NameSegment)suffix.Lhs;
                if (parse.symbols.DoesMethodNameExist(suffixName.Name)) {
                  return new ArmadaCallStatement(parse, s, suffixName.Name);
                }
              }
            }
          }
          else if (rhs is CreateThreadRhs) {
            return new ArmadaCreateThreadStatement(parse, s);
          }
          else if (rhs is MallocRhs) {
            return new ArmadaMallocStatement(parse, s);
          }
          else if (rhs is CallocRhs) {
            return new ArmadaCallocStatement(parse, s);
          }
          else if (rhs is CompareAndSwapRhs) {
            return new ArmadaCompareAndSwapStatement(parse, s);
          }
          else if (rhs is AtomicExchangeRhs) {
            return new ArmadaAtomicExchangeStatement(parse, s);
          }
        }

        return new ArmadaUpdateStatement(parse, s);
      }
      else if (stmt is IfStmt)
      {
        var s = (IfStmt)stmt;
        return new ArmadaIfStatement(parse, s);
      }
      else if (stmt is WhileStmt)
      {
        var s = (WhileStmt)stmt;
        parse = parse.Clone();
        return new ArmadaWhileStatement(parse, s);
      }
      else if (stmt is VarDeclStmt)
      {
        var s = (VarDeclStmt)stmt;
        return new ArmadaVarDeclStatement(parse, s);
      }
      else if (stmt is ReturnStmt)
      {
        var s = (ReturnStmt)stmt;
        return new ArmadaReturnStatement(parse, s);
      }
      else if (stmt is AssertStmt)
      {
        var s = (AssertStmt)stmt;
        return new ArmadaAssertStatement(parse, s);
      }
      else if (stmt is AssumeStmt)
      {
        var s = (AssumeStmt)stmt;
        return new ArmadaAssumeStatement(parse, s);
      }
      else if (stmt is SomehowStmt)
      {
        var s = (SomehowStmt)stmt;
        return new ArmadaSomehowStatement(parse, s);
      }
      else if (stmt is FenceStmt)
      {
        var s = (FenceStmt)stmt;
        return new ArmadaFenceStatement(parse, s);
      }
      else if (stmt is GotoStmt)
      {
        var s = (GotoStmt)stmt;
        return new ArmadaGotoStatement(parse, s);
      }
      else if (stmt is DeallocStmt)
      {
        var s = (DeallocStmt)stmt;
        return new ArmadaDeallocStatement(parse, s);
      }
      else if (stmt is JoinStmt)
      {
        var s = (JoinStmt)stmt;
        return new ArmadaJoinStatement(parse, s);
      }
      else if (stmt is BreakStmt)
      {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          AH.PrintError(parse.prog, stmt.Tok, "Armada doesn't support breaks with statement labels");
        }
        if (s.BreakCount != 1) {
          AH.PrintError(parse.prog, stmt.Tok, "Armada doesn't support breaks with counts other than 1");
        }
        if (parse.innermostEnclosingWhile == null) {
          AH.PrintError(parse.prog, stmt.Tok, "Can't have a break that isn't inside of a while loop");
        }
        return new ArmadaBreakStatement(parse, s);
      }
      else if (stmt is ContinueStmt)
      {
        var s = (ContinueStmt)stmt;
        if (parse.innermostEnclosingWhile == null) {
          AH.PrintError(parse.prog, stmt.Tok, "Can't have a continue that isn't inside of a while loop");
        }
        return new ArmadaContinueStatement(parse, s);
      }
      else if (stmt is YieldStmt)
      {
        var s = (YieldStmt)stmt;
        return new ArmadaYieldStatement(parse, s);
      }
      else
      {
        AH.PrintWarning(parse.prog, stmt.Tok, "Armada doesn't yet support this statement type");
        return null;
      }
    }

    public static ArmadaStatement ParseStatement(ParseInfo parse, Statement stmt)
    {
      if (stmt == null) {
        return null;
      }
      stmt.Parsed = ParseStatementInternal(parse, stmt);
      return stmt.Parsed;
    }

    public virtual IEnumerator<ArmadaStatement> GetEnumerator()
    {
      yield return this;
    }

    public virtual ArmadaPC AssignPCs(ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      endPC = parse.methodInfo.GenerateOnePC();
      return endPC;
    }

    public string UpdatePC(string s, string tid, ArmadaPC newPC)
    {
      return $"Armada_UpdatePC({s}, {tid}, {newPC})";
    }

    public virtual void AssociateLabelsWithPCs()
    {
      Statement stmt = Stmt;
      if (stmt != null) {
        for (var lbl = stmt.Labels; lbl != null; lbl = lbl.Next) {
          if (lbl.Data != null && lbl.Data.Name != null) {
            parse.symbols.AssociateLabelWithPC(lbl.Data.Name, startPC);
          }
        }
      }
    }

    public virtual void GenerateEnablingConstraints()
    {
    }

    public virtual void GenerateNextRoutines()
    {
    }

    public virtual void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                   HashSet<ArmadaPC> yieldPCs)
    {
      if (inExplicitYieldBlock) {
        potentiallyNonyieldingPCs.Add(startPC);
      }
    }

    public static void ComputeNonyieldingPCs(ArmadaStatement stmt, HashSet<ArmadaPC> nonyieldingPCs)
    {
      var potentiallyNonyieldingPCs = new HashSet<ArmadaPC>();
      var yieldPCs = new HashSet<ArmadaPC>();

      stmt.ComputeNonyieldAndYieldPCs(false, potentiallyNonyieldingPCs, yieldPCs);

      foreach (var pc in potentiallyNonyieldingPCs) {
        if (!yieldPCs.Contains(pc)) {
          nonyieldingPCs.Add(pc);
        }
      }
    }

    protected void GetStackFrameForCallOrCreateThread(NextRoutineConstructor next, ResolutionContext resolutionContext,
                                                      string calleeName, IEnumerable<Expression> args, ref string s_current,
                                                      out string new_frame, out string new_ptrs)
    {
      // First, allocate new pointers to represent the addressable stack variables:
      //
      // s_current := s.(mem := s.mem.(heap := s.mem.heap.(valid := s.mem.heap.valid + new_ptrs)))

      new_ptrs = next.AddFormal(new NextFormal($"new_ptrs_{startPC}", "new_ptrs", "set<Armada_Pointer>"));

      var mem = $"({s_current}).mem";
      var h = $"{mem}.heap";
      s_current = $"({s_current}).(mem := {mem}.(heap := {h}.(valid := {h}.valid + new_ptrs)))";
      s_current = next.AddVariableDeclaration("s", s_current);

      // The new_ptrs don't overlap the previous valid pointers

      next.AddDefinedBehaviorConjunct($"new_ptrs !! {h}.valid");

      // Nothing that was freed has become valid

      next.AddDefinedBehaviorConjunct($"new_ptrs !! {h}.freed");

      var h_current = $"{s_current}.mem.heap";

      // Next, compute the parameters to the new-frame
      // constructor. For each input field, get its value from the
      // arguments; for each non-input field, model its initial
      // value as non-deterministic.

      List<string> new_frame_elements = new List<string>();
      var smst = parse.symbols.GetMethodSymbolTable(calleeName);
      List<string> p_in_new_ptrs = new List<string>();
      List<string> addressesOfAddressables = new List<string>();
      var argumentEnumerator = args.GetEnumerator();
      foreach (var v in smst.AllVariablesInOrder)
      {
        if (v.varType is ArmadaVarType.Input) {
          if (!argumentEnumerator.MoveNext()) {
            next.Fail("Not enough input arguments provided to method");
          }
          else {
            var arg = argumentEnumerator.Current;
            var argVal = resolutionContext.ResolveAsRValue(arg);
            next.AddUndefinedBehaviorAvoidanceConstraint(argVal.UndefinedBehaviorAvoidance);
            new_frame_elements.Add(argVal.Val);
          }
          continue;
        }

        var varName = v.name;
        var ty = parse.symbols.FlattenType(v.ty);
        if (v is AddressableArmadaVariable) {
          // For addressable variables, we have to not only add a pointer to the new-frame constructor, we also
          // have to make sure the pointed-to values are allocated

          var new_ptr = next.AddFormal(new NextFormal($"newframe_{startPC}_{varName}", $"newframe_{varName}", "Armada_Pointer"));
          new_frame_elements.Add(new_ptr);

          // new_ptr is among new_ptrs

          next.AddDefinedBehaviorConjunct($"{new_ptr} in new_ptrs");

          // new_ptr is in s.mem.heap.tree

          var tree = $"{h}.tree";
          next.AddDefinedBehaviorConjunct($"{new_ptr} in {tree}");

          // new_ptr is a stack-based root in s.mem.heap, i.e.,
          //    && s.mem.heap.tree[new_ptr].child_type.Armada_ChildTypeRoot?
          //    && s.mem.heap.tree[new_ptr].child_type.rt.Armada_RootTypeStack?

          next.AddDefinedBehaviorConjunct($"{tree}[{new_ptr}].child_type.Armada_ChildTypeRoot?");
          next.AddDefinedBehaviorConjunct($"{tree}[{new_ptr}].child_type.rt.Armada_RootTypeStack?");

          /*
          if (v.ty is SizedArrayType) {
          }
          else {
            p_in_new_ptrs += $"p in {AH.GetNameOfAllocator(v.ty)}(s2.mem.heap, newframe_{varName})";
          }
          */
          var descendants = AH.GetInvocationOfDescendants(h_current, new_ptr, v.ty);
          p_in_new_ptrs.Add($"p in ({descendants})");
          addressesOfAddressables.Add(new_ptr);
          // new_ptr is a valid pointer in s_current.mem.heap

          var pointer_valid = AH.GetInvocationOfValidPointer(h_current, new_ptr, v.ty);
          next.AddDefinedBehaviorConjunct(pointer_valid);
        }
        else {
          var elt = next.AddFormal(new NextFormal($"newframe_{startPC}_{varName}", $"newframe_{varName}", ty, parse.symbols));
          new_frame_elements.Add(elt);
        }
      }

      if (p_in_new_ptrs.Count > 0) {
        next.AddDefinedBehaviorConjunct($"forall p :: p in new_ptrs <==> ({AH.CombineStringsWithOr(p_in_new_ptrs)})");
      }
      else {
        next.AddDefinedBehaviorConjunct("|new_ptrs| == 0");
      }

      for (int i = 0; i < addressesOfAddressables.Count; i++) {
        for (int j = i + 1; j < addressesOfAddressables.Count; j++) {
          next.AddDefinedBehaviorConjunct($"({addressesOfAddressables[i]}) != ({addressesOfAddressables[j]})");
        }
      }

      // new_ptrs == Armada_Allocator_type1(local1) + ...
      // Equivalently, forall x :: x in new_ptrs <==> x in Armada_Allocator_type1(local1)

      // Finally, create the frame.
      // var new_vars := Armada_StackVars_{calleeName}(input..., output..., normal..., reads...);
      // var new_frame := Armada_StackFrame_{calleeName}(new_vars);

      var new_frame_elements_list = String.Join(", ", new_frame_elements);
      new_frame = $"Armada_StackFrame_{calleeName}(Armada_StackVars_{calleeName}({new_frame_elements_list}))";
      new_frame = next.AddVariableDeclaration("new_frame", new_frame);
    }

    protected void PerformStackFrameInitializations(NextRoutineConstructor next, string calleeName,
                                                    string tid, ref string s_current, ArmadaPC pc)
    {
      var smst = parse.symbols.GetMethodSymbolTable(calleeName);
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.InitialValue != null))
      {
        var resolutionContext = new ResolutionContext(s_current, s_current, tid, calleeName, parse.symbols, next);
        var ty = parse.symbols.FlattenType(v.ty);
        var lhs = v.GetLValue(v.InitialValue.tok, resolutionContext);
        var rhsRVal = resolutionContext.ResolveAsRValue(v.InitialValue);
        next.AddUndefinedBehaviorAvoidanceConstraint(rhsRVal.UndefinedBehaviorAvoidance);
        var rhs = rhsRVal.Val;

        bool bypassStoreBuffers = (v is MethodStackFrameAddressableLocalArmadaVariable) &&
                                  ((MethodStackFrameAddressableLocalArmadaVariable)v).TSOBypassingInitialization;

        // var s_current := lhs.update_state(s_current, rhs);
        s_current = bypassStoreBuffers ? lhs.UpdateTotalStateBypassingStoreBuffer(resolutionContext, next, rhs)
                                       : lhs.UpdateTotalStateWithStoreBufferEntry(resolutionContext, next, rhs, pc);
        s_current = next.AddVariableDeclaration("s", s_current);
      }
    }

    public virtual bool RoughlyMatches(ArmadaStatement other)
    {
      return false;
    }

    public virtual IEnumerable<ArmadaStatement> GetStatementsInBody()
    {
      yield return this;
    }
  }

  public class ArmadaBlockStatement : ArmadaStatement
  {
    private BlockStmt stmt;
    private List<ArmadaStatement> statements;

    public ArmadaBlockStatement(ParseInfo i_parse, BlockStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
      statements = stmt.Body.Select(x => ParseStatement(parse, x)).ToList();
    }

    public override Statement Stmt { get { return stmt; } }

    public override IEnumerable<ArmadaStatement> GetStatementsInBody()
    {
      foreach (var statement in statements) {
        foreach (var substatement in statement.GetStatementsInBody()) {
          yield return substatement;
        }
      }
    }

    public override IEnumerator<ArmadaStatement> GetEnumerator()
    {
      yield return this;
      foreach (var statement in statements) {
        foreach (var substatement in statement) {
          yield return substatement;
        }
      }
    }

    public override ArmadaPC AssignPCs(ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      var currentPC = startPC;
      foreach (var statement in statements)
      {
        currentPC = statement.AssignPCs(currentPC);
      }
      endPC = currentPC;
      return endPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
      if (stmt is ExplicitYieldBlockStmt && !inExplicitYieldBlock) {
        yieldPCs.Add(startPC);
        yieldPCs.Add(endPC);
        inExplicitYieldBlock = true;
      }

      foreach (var statement in statements) {
        statement.ComputeNonyieldAndYieldPCs(inExplicitYieldBlock, potentiallyNonyieldingPCs, yieldPCs);
      }
    }

    public override void GenerateNextRoutines()
    {
      foreach (var statement in statements) {
        statement.GenerateNextRoutines();
      }
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaBlockStatement;
    }
  }

  public class ArmadaIfStatement : ArmadaStatement
  {
    private IfStmt stmt;
    private ArmadaStatement thenClause;
    private ArmadaStatement elseClause;

    public ArmadaIfStatement(ParseInfo i_parse, IfStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
      thenClause = ParseStatement(parse, stmt.Thn);
      elseClause = ParseStatement(parse, stmt.Els);
    }

    public override Statement Stmt { get { return stmt; } }

    public ArmadaStatement ThenClause { get { return thenClause; } }
    public ArmadaStatement ElseClause { get { return elseClause; } }

    public override IEnumerator<ArmadaStatement> GetEnumerator()
    {
      yield return this;
      foreach (var statement in thenClause) {
        yield return statement;
      }
      if (elseClause != null) {
        foreach (var statement in elseClause) {
          yield return statement;
        }
      }
    }

    public override ArmadaPC AssignPCs(ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      var thenPC = parse.methodInfo.GenerateOnePC();
      var thenEndPC = thenClause.AssignPCs(thenPC);
      Debug.Assert(thenEndPC == thenClause.EndPC);

      if (elseClause == null) {
        endPC = thenEndPC;
      }
      else {
        var elsePC = parse.methodInfo.GenerateOnePC();
        endPC = elseClause.AssignPCs(elsePC);
      }
      return endPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
      if (inExplicitYieldBlock) {
        potentiallyNonyieldingPCs.Add(startPC);
        if (elseClause != null) {
          potentiallyNonyieldingPCs.Add(thenClause.EndPC);
        }
      }

      foreach (var statement in thenClause) {
        statement.ComputeNonyieldAndYieldPCs(inExplicitYieldBlock, potentiallyNonyieldingPCs, yieldPCs);
      }

      if (elseClause != null) {
        foreach (var statement in elseClause) {
          statement.ComputeNonyieldAndYieldPCs(inExplicitYieldBlock, potentiallyNonyieldingPCs, yieldPCs);
        }
      }
    }

    public override void AssociateLabelsWithPCs()
    {
      base.AssociateLabelsWithPCs();
      if (elseClause != null) {
        parse.symbols.AssociateLabelWithPC($"JumpPastElse_{thenClause.EndPC.Name}", thenClause.EndPC);
      }
    }

    public override void GenerateNextRoutines()
    {
      //
      // First, we generate the next routine for evaluating the guard at
      // startPC and going to either thenClause.StartPC or (elseClause.StartPC or thenClause.EndPC),
      // or failing because the guard evaluation crashes.
      //

      var elsePC = stmt.Els != null ? elseClause.StartPC : thenClause.EndPC;
      var nextThen = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.IfTrue, parse.methodInfo,
                                                this, stmt, startPC, thenClause.StartPC);
      var nextElse = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.IfFalse, parse.methodInfo,
                                                this, stmt, startPC, elsePC);

      var contextThen = new NormalResolutionContext(nextThen, parse.symbols);
      var contextElse = new NormalResolutionContext(nextElse, parse.symbols);

      if (stmt.Guard != null) { // A null guard means a non-deterministic choice, i.e., *
        var guardRValue = contextThen.ResolveAsRValue(stmt.Guard);
        nextThen.AddUndefinedBehaviorAvoidanceConstraint(guardRValue.UndefinedBehaviorAvoidance);
        nextThen.AddDefinedBehaviorConjunct(guardRValue.Val);

        guardRValue = contextElse.ResolveAsRValue(stmt.Guard);
        // There's need for an "undefined behavior" branch of the false case, since it matches the true case.
        nextElse.AddUBAvoidanceConstraintAsDefinedBehaviorConjunct(guardRValue.UndefinedBehaviorAvoidance);
        nextElse.AddDefinedBehaviorConjunct($"!({guardRValue.Val})");
      }

      // s' == Armada_UpdatePC(s, tid, {then/else PC})

      var s_then = UpdatePC(nextThen.s, nextThen.tid, thenClause.StartPC);
      nextThen.SetNextState(s_then);

      var s_else = UpdatePC(nextElse.s, nextElse.tid, elsePC);
      nextElse.SetNextState(s_else);

      parse.symbols.AddNextRoutineConstructor(nextThen);
      parse.symbols.AddNextRoutineConstructor(nextElse);

      //
      // Second, we generate the next routines for the then clause.
      //

      thenClause.GenerateNextRoutines();

      if (elseClause != null) {

        //
        // Third, if there's an else clause, we generate the next
        // routine for jumping from thenClause.EndPC directly and
        // unconditionally to endPC.
        //

        var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.JumpPastElse, parse.methodInfo,
                                              this, stmt, thenClause.EndPC, endPC);
        var s_prime = UpdatePC(next.s, next.tid, endPC);
        next.SetNextState(s_prime);
        parse.symbols.AddNextRoutineConstructor(next);

        //
        // Fourth, if there's an else clause, we generate the next routines for that clause
        //

        elseClause.GenerateNextRoutines();
      }
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaIfStatement;
    }
  }

  public class ArmadaWhileStatement : ArmadaStatement
  {
    private WhileStmt stmt;
    private ArmadaStatement body;

    public ArmadaWhileStatement(ParseInfo i_parse, WhileStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
      parse = parse.Clone();
      parse.innermostEnclosingWhile = this;
      body = ParseStatement(parse, stmt.Body);
    }

    public override Statement Stmt { get { return stmt; } }

    public ArmadaStatement Body { get { return body; } }

    public override IEnumerator<ArmadaStatement> GetEnumerator()
    {
      yield return this;
      foreach (var statement in body) {
        yield return statement;
      }
    }

    public override ArmadaPC AssignPCs(ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      var loopHeadPC = parse.methodInfo.GenerateOnePC();
      var loopEndPC = body.AssignPCs(loopHeadPC);
      endPC = parse.methodInfo.GenerateOnePC();
      return endPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
      if (inExplicitYieldBlock) {
        potentiallyNonyieldingPCs.Add(startPC);
        potentiallyNonyieldingPCs.Add(body.EndPC);
      }
      foreach (var statement in body) {
        statement.ComputeNonyieldAndYieldPCs(inExplicitYieldBlock, potentiallyNonyieldingPCs, yieldPCs);
      }
    }

    public override void AssociateLabelsWithPCs()
    {
      base.AssociateLabelsWithPCs();
      parse.symbols.AssociateLabelWithPC($"JumpBack_{body.EndPC.Name}", body.EndPC);
    }

    public override void GenerateEnablingConstraints()
    {
      foreach (var inv in stmt.Invariants)
      {
        parse.methodInfo.AddEnablingConstraint(parse.prog, startPC, inv.E);
      }
    }

    public override void GenerateNextRoutines()
    {
      // First, make a next routine for conditionally jumping from the statement beginning to either the loop head or the statement end.

      var nextTrue = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.WhileTrue, parse.methodInfo,
                                                this, stmt, startPC, body.StartPC);
      var nextFalse = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.WhileFalse, parse.methodInfo,
                                                 this, stmt, startPC, endPC);

      var contextTrue = new NormalResolutionContext(nextTrue, parse.symbols);
      var contextFalse = new NormalResolutionContext(nextFalse, parse.symbols);

      if (stmt.Guard != null) { // A null guard means a non-deterministic choice, i.e., *
        var guardRValue = contextTrue.ResolveAsRValue(stmt.Guard);
        nextTrue.AddUndefinedBehaviorAvoidanceConstraint(guardRValue.UndefinedBehaviorAvoidance);
        nextTrue.AddDefinedBehaviorConjunct(guardRValue.Val);

        guardRValue = contextFalse.ResolveAsRValue(stmt.Guard);
        // There's need for an "undefined behavior" branch of the false case, since it matches the true case.
        nextFalse.AddUBAvoidanceConstraintAsDefinedBehaviorConjunct(guardRValue.UndefinedBehaviorAvoidance);
        nextFalse.AddDefinedBehaviorConjunct($"!({guardRValue.Val})");
      }

      // s' == Armada_UpdatePC(s, tid, {head/end PC})

      var s_true = UpdatePC(nextTrue.s, nextTrue.tid, body.StartPC);
      nextTrue.SetNextState(s_true);
      var s_false = UpdatePC(nextFalse.s, nextFalse.tid, endPC);
      nextFalse.SetNextState(s_false);

      parse.symbols.AddNextRoutineConstructor(nextTrue);
      parse.symbols.AddNextRoutineConstructor(nextFalse);

      // Second, make next routines for the body

      body.GenerateNextRoutines();

      // Third, make a next routine for unconditionally jumping from the loop end to the statement beginning.

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.WhileEnd, parse.methodInfo,
                                            this, stmt, body.EndPC, startPC);
      var s_with_new_PC = UpdatePC(next.s, next.tid, startPC);
      next.SetNextState(s_with_new_PC);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaWhileStatement;
    }
  }

  public class ArmadaCallStatement : ArmadaStatement
  {
    private UpdateStmt stmt;
    private string calleeName;

    public ArmadaCallStatement(ParseInfo i_parse, UpdateStmt i_stmt, string i_calleeName) : base(i_parse)
    {
      stmt = i_stmt;
      calleeName = i_calleeName;
    }

    public override Statement Stmt { get { return stmt; } }

    public string CalleeName { get {return calleeName; } }

    private void GenerateCallNextRoutine()
    {
      //
      // The first next routine for a call statement is the one for the call itself.
      //

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Call, parse.methodInfo,
                                            this, stmt, startPC, new ArmadaPC(parse.symbols, calleeName, 0));
      var resolutionContext = new NormalResolutionContext(next, parse.symbols);
      var ex = (ExprRhs)stmt.Rhss[0];
      var suffix = (ApplySuffix)ex.Expr;

      int numArgsExpected = parse.symbols.GetNumInputVariables(calleeName);
      if (numArgsExpected != suffix.Args.Count) {
        next.Fail(stmt.Tok, $"Incorrect number of arguments to {calleeName} ({suffix.Args.Count} instead of {numArgsExpected})");
        return;
      }
      int numReturnValuesExpected = parse.symbols.GetNumOutputVariables(calleeName);
      if (numReturnValuesExpected != stmt.Lhss.Count) {
        next.Fail(stmt.Tok,
                  $"Incorrect number of return values assigned from {calleeName} ({stmt.Lhss.Count} instead of {numReturnValuesExpected}");
        return;
      }

      // Set up the new stack frame

      string s_current = next.s, new_frame, new_ptrs;
      GetStackFrameForCallOrCreateThread(next, resolutionContext, calleeName, suffix.Args, ref s_current, out new_frame, out new_ptrs);

      var newPC = new ArmadaPC(parse.symbols, calleeName, 0);
      var t = $"({next.t})";
      s_current = next.AddVariableDeclaration("s", $@"
        ({s_current}).(threads := ({next.s}).threads[{next.tid} := Armada_Thread({newPC}, {new_frame}, {new_ptrs},
          [Armada_ExtendedFrame({endPC}, {t}.top, {t}.new_ptrs)] + {t}.stack, {t}.storeBuffer)])
      ");

      PerformStackFrameInitializations(next, calleeName, next.tid, ref s_current, startPC);

      next.SetNextState(s_current);

      parse.symbols.AddNextRoutineConstructor(next);
    }

    private void GenerateReturnNextRoutines()
    {
      //
      // The second type of next routine for a call statement is the one for the return from the call,
      // including assignment of returned values.
      //

      var method = parse.methodInfo.method;
      var calleeMethodInfo = parse.symbols.AllMethods.LookupMethod(calleeName);

      var returnPC = calleeMethodInfo.ReturnPC;
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Return, calleeMethodInfo,
                                            this, stmt, returnPC, endPC);

      var t = $"({next.t})";
      var s = $"({next.s})";

      next.AddConjunct($"|{t}.stack| > 0");
      next.AddConjunct($"{t}.stack[0].return_pc == {endPC}");
      next.AddConjunct($"{t}.stack[0].frame.Armada_StackFrame_{method.Name}?");

      // First, we update the state by popping the thread's top stack frame.

      var s_current = $@"
        {s}.(threads := {s}.threads[{next.tid} := Armada_Thread({endPC}, {t}.stack[0].frame, {t}.stack[0].new_ptrs,
                                                                {t}.stack[1..], {t}.storeBuffer)])
      ";
      s_current = next.AddVariableDeclaration("s", s_current);

      // Now, we need to free the new_ptrs.

      s = s_current;
      s_current = $@"
        {s}.(mem := {s}.mem.(heap := {s}.mem.heap.(valid := {s}.mem.heap.valid - {t}.new_ptrs, freed := {s}.mem.heap.freed + {t}.new_ptrs)))
      ";
      s_current = next.AddVariableDeclaration("s", s_current);

      // We need a context to compute the values of returned values, a callee_context.

      var callee_context = new NormalResolutionContext(next, parse.symbols);

      // When computing caller contexts (for use in computing lvalues to use for storing return values), we'll need to
      // know the state of various objects as they appear right after popping the stack frame.  So, compute those now.

      var state_after_pop = s_current;
      var ghosts_after_pop = $"{s_current}.ghosts";
      var top_after_pop = $"{s_current}.threads[{next.tid}].top";

      int numReturnValuesExpected = parse.symbols.GetNumOutputVariables(calleeName);
      for (int i = 0; i < numReturnValuesExpected; ++i) {
        // We need a context for the caller to use when computing lvalues to use for storing return
        // values into local variables.  The hard part of this is computing the local view of the
        // state.  A shortcut to this is to observe that the local view of the state doesn't change
        // due to a pop, so we can just use next.locv.

        var caller_context = new CustomResolutionContext(s_current, state_after_pop, next.locv, top_after_pop,
                                                         ghosts_after_pop, next.tid, method.Name, parse.symbols, next);

        var av = parse.symbols.GetOutputVariableByIndex(calleeName, i);
        var rhs = av.GetRValue(Token.NoToken, callee_context);
        next.AddUndefinedBehaviorAvoidanceConstraint(rhs.UndefinedBehaviorAvoidance);
        var lhs = stmt.Lhss.ElementAt(i);
        var newLhs = caller_context.ResolveAsLValue(lhs);
        if (!(newLhs is ArmadaLValue)) {
          next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        s_current = stmt.BypassStoreBuffers ?
          newLhs.UpdateTotalStateBypassingStoreBuffer(caller_context, next, rhs.Val) :
          newLhs.UpdateTotalStateWithStoreBufferEntry(caller_context, next, rhs.Val, returnPC);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      next.SetNextState(s_current);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override void GenerateNextRoutines()
    {
      GenerateCallNextRoutine();
      GenerateReturnNextRoutines();
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      if (other is ArmadaCallStatement acs) {
        return calleeName == acs.CalleeName;
      }
      else {
        return false;
      }
    }
  }

  public class ArmadaCreateThreadStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaCreateThreadStatement(ParseInfo i_parse, UpdateStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      if (stmt.Lhss.Count > 1) {
        AH.PrintError(parse.prog, stmt.Tok,
                      $"Number of left-hand sides for create_thread must be 0 or 1, since the only thing returned is a thread handle");
        return;
      }

      var rhs = (CreateThreadRhs)stmt.Rhss[0];
      var calleeName = rhs.MethodName.val;

      if (!parse.symbols.DoesMethodNameExist(calleeName)) {
        AH.PrintError(parse.prog, stmt.Tok, $"Call to create_thread on non-existent method {calleeName}");
        return;
      }

      if (calleeName.Equals("main")) {
        AH.PrintError(parse.prog, stmt.Tok, $"It's illegal to create a thread using main as the routine");
        return;
      }

      parse.symbols.UseMethodAsThreadRoutine(calleeName);

      int numInputs = parse.symbols.GetNumInputVariables(calleeName);
      if (numInputs != rhs.Args.Count) {
        AH.PrintError(parse.prog, stmt.Tok,
                      $"Call to create_thread has {rhs.Args.Count} input variables but {calleeName} takes {numInputs} input parameters");
        return;
      }

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.CreateThread, parse.methodInfo,
                                            this, stmt, startPC, endPC);
      var resolutionContext = new NormalResolutionContext(next, parse.symbols);

      var new_tid = next.AddFormal(new NextFormal($"newtid_{startPC}", "newtid", "Armada_ThreadHandle"));
      var s = $"({next.s})";

      next.AddConjunct($"{new_tid} !in {s}.threads");
      next.AddConjunct($"{new_tid} !in {s}.joinable_tids");
      next.AddConjunct($"{new_tid} != 0");

      // Set up the new stack frame

      string s_current = next.s, new_frame, new_ptrs;
      GetStackFrameForCallOrCreateThread(next, resolutionContext, calleeName, rhs.Args, ref s_current, out new_frame, out new_ptrs);

      var calleePC = new ArmadaPC(parse.symbols, calleeName, 0);
      s_current = $@"
        ({s_current}).(threads := s.threads[{new_tid} := Armada_Thread({calleePC}, {new_frame}, {new_ptrs}, [], [])])
      ";
      s_current = next.AddVariableDeclaration("s", s_current);

      PerformStackFrameInitializations(next, calleeName, new_tid, ref s_current, startPC);

      // s_current := Armada_UpdatePC(s_current, next.tid, endPC);

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // If there's a return value, set it to new_tid

      if (stmt.Lhss.Count > 0) {
        var current_context = new NormalResolutionContext(s_current, next, parse.symbols);
        var lhs = stmt.Lhss[0];
        var newLhs = current_context.ResolveAsLValue(lhs);
        if (!(newLhs is ArmadaLValue)) {
          next.Fail(lhs.tok, "Where to store the returned thread handle from create_thread is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        // var s_current := lhs.update_state(s_current, new_tid);
        s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, new_tid)
                                            : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, new_tid, startPC);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      next.SetNextState(s_current);

      // We're done creating the next routine, so add it to the list

      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      if (other is ArmadaCreateThreadStatement) {
        return ((CreateThreadRhs)stmt.Rhss[0]).MethodName.val == ((CreateThreadRhs)((UpdateStmt)other.Stmt).Rhss[0]).MethodName.val;
      }
      else {
        return false;
      }
    }
  }

  public class ArmadaMallocStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaMallocStatement(ParseInfo i_parse, UpdateStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      if (stmt.Lhss.Count != 1) {
        AH.PrintError(parse.prog, stmt.Tok, $"Number of left-hand sides for malloc must be 1");
        return;
      }

      var lhs = stmt.Lhss[0];
      if (!(lhs.Type is PointerType)) {
        AH.PrintError(parse.prog, stmt.Tok, $"Result of malloc must be stored in a ptr");
        return;
      }

      var rhs = (MallocRhs)stmt.Rhss[0];
      var lhsPointerType = (PointerType)lhs.Type;
      if (!lhsPointerType.Arg.Equals(rhs.AllocatedType)) {
        AH.PrintError(parse.prog, stmt.Tok, $"Result of malloc must be stored in a ptr<{rhs.AllocatedType}>");
        return;
      }

      // First, create a next routine for the case where malloc succeeds.

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.MallocSuccess, parse.methodInfo,
                                            this, stmt, startPC, endPC);

      var s = $"({next.s})";
      var h = $"{s}.mem.heap";
      var tree = $"{h}.tree";

      var new_ptr = next.AddFormal(new NextFormal($"new_ptr_{startPC}", "new_ptr", "Armada_Pointer"));
      var new_ptrs = next.AddFormal(new NextFormal($"new_ptrs_{startPC}", "new_ptrs", "set<Armada_Pointer>"));

      // new_ptr != 0
      // new_ptr in new_ptrs
      // new_ptrs == Armada_Allocator_{ty}(new_ptr)
      // new_ptr is in s.mem.heap.tree
      // new_ptr is a root in s.mem.heap, i.e., s.mem.heap.tree[new_ptr].child_type.Armada_ChildTypeRoot?
      // new_ptr is a dynamic-heap root, i.e., s.mem.heap.tree[new_ptr].child_type.rt.Armada_RootTypeDynamicHeap?
      // The new_ptrs don't overlap the previous valid pointers, i.e., new_ptrs !! s.mem.heap.valid
      // Nothing that was freed has become valid, i.e., new_ptrs !! s.mem.heap.freed

      next.AddDefinedBehaviorConjunct($"{new_ptr} != 0");
      next.AddDefinedBehaviorConjunct($"{new_ptr} in {new_ptrs}");
      next.AddDefinedBehaviorConjunct(AH.GetInvocationOfValidPointer(h, new_ptr, rhs.AllocatedType));
      next.AddDefinedBehaviorConjunct($"{new_ptr} in {tree}");
      next.AddDefinedBehaviorConjunct($"{tree}[{new_ptr}].child_type.Armada_ChildTypeRoot?");
      next.AddDefinedBehaviorConjunct($"{tree}[{new_ptr}].child_type.rt.Armada_RootTypeDynamicHeap?");
      next.AddDefinedBehaviorConjunct($"{new_ptrs} !! {h}.valid");
      next.AddDefinedBehaviorConjunct($"{new_ptrs} !! {h}.freed");

      // s_current := s.(mem := s.mem.(heap := s.mem.heap.(valid := s.mem.heap.valid + new_ptrs)))

      var s_current = $"{s}.(mem := {s}.mem.(heap := {s}.mem.heap.(valid := {s}.mem.heap.valid + {new_ptrs})))";
      s_current = next.AddVariableDeclaration("s", s_current);

      // new_ptr is a valid pointer in s_current.mem.heap

      var h_current = $"{s_current}.mem.heap";
      next.AddDefinedBehaviorConjunct(AH.GetInvocationOfValidPointer(h_current, new_ptr, rhs.AllocatedType));

      var descendants = AH.GetInvocationOfDescendants(h_current, new_ptr, rhs.AllocatedType);
      next.AddDefinedBehaviorConjunct($"(forall p :: p in {new_ptrs} <==> p in {descendants})");

      // s_current := lhs.update_state(s_current, new_ptr);

      var current_context = new NormalResolutionContext(s_current, next, parse.symbols);
      var newLhs = current_context.ResolveAsLValue(lhs);
      if (!(newLhs is ArmadaLValue)) {
        next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
        return;
      }
      next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

      s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, new_ptr)
                                          : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, new_ptr, startPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      parse.symbols.AddNextRoutineConstructor(next);

      //////////////////////////////////////////////////////////////////////////////
      // Now, create a next routine for the case where malloc fails.
      //////////////////////////////////////////////////////////////////////////////

      next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.MallocFailure, parse.methodInfo,
                                        this, stmt, startPC, endPC);
      current_context = new NormalResolutionContext(next.s, next, parse.symbols);

      // s_current := lhs.update_state(s_current, new_ptr);

      newLhs = current_context.ResolveAsLValue(lhs);
      if (!(newLhs is ArmadaLValue)) {
        next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
        return;
      }
      next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());
      s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, "0")
                                          : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, "0", startPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      if (other is ArmadaMallocStatement ams) {
        return AH.TypesMatch(((MallocRhs)stmt.Rhss[0]).AllocatedType, ((MallocRhs)((UpdateStmt)ams.Stmt).Rhss[0]).AllocatedType);
      }
      else {
        return false;
      }
    }
  }

  public class ArmadaCallocStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaCallocStatement(ParseInfo i_parse, UpdateStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      if (stmt.Lhss.Count != 1) {
        AH.PrintError(parse.prog, stmt.Tok, $"Number of left-hand sides for calloc must be 1");
        return;
      }

      var lhs = stmt.Lhss[0];
      if (!(lhs.Type is PointerType)) {
        AH.PrintError(parse.prog, stmt.Tok, $"Result of calloc must be stored in a ptr");
        return;
      }

      var rhs = (CallocRhs)stmt.Rhss[0];
      var lhsPointerType = (PointerType)lhs.Type;
      if (!lhsPointerType.Arg.Equals(rhs.AllocatedType)) {
        AH.PrintError(parse.prog, stmt.Tok, $"Result of calloc must be stored in a ptr<{rhs.AllocatedType}>");
        return;
      }

      // First, create a next routine for the case where calloc succeeds.

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.CallocSuccess, parse.methodInfo,
                                            this, stmt, startPC, endPC);
      var resolutionContext = new NormalResolutionContext(next, parse.symbols);

      var countRValue = resolutionContext.ResolveAsRValue(rhs.Count);
      next.AddUndefinedBehaviorAvoidanceConstraint(countRValue.UndefinedBehaviorAvoidance);
      var count = $"({countRValue.Val}) as int";

      var s = $"({next.s})";
      var h = $"{s}.mem.heap";
      var tree = $"{h}.tree";

      var new_ptr = next.AddFormal(new NextFormal($"new_ptr_{startPC}", "new_ptr", "Armada_Pointer"));
      var new_ptrs = next.AddFormal(new NextFormal($"new_ptrs_{startPC}", "new_ptrs", "set<Armada_Pointer>"));

      // new_ptr != 0
      // new_ptr in new_ptrs
      // new_ptr is in s.mem.heap.tree
      // new_ptr is a root in s.mem.heap, i.e., s.mem.heap.tree[new_ptr].child_type.Armada_ChildTypeRoot?
      // new_ptr is a dynamic-heap root, i.e., s.mem.heap.tree[new_ptr].child_type.rt.Armada_RootTypeDynamicHeap?
      // The new_ptrs don't overlap the previous valid pointers, i.e., new_ptrs !! s.mem.heap.valid
      // Nothing that was freed has become valid, i.e., new_ptrs !! s.mem.heap.freed

      next.AddDefinedBehaviorConjunct($"{new_ptr} != 0");
      next.AddDefinedBehaviorConjunct($"{new_ptr} in {new_ptrs}");
      next.AddDefinedBehaviorConjunct($"{new_ptr} in {tree}");
      next.AddDefinedBehaviorConjunct($"{tree}[{new_ptr}].child_type.Armada_ChildTypeRoot?");
      next.AddDefinedBehaviorConjunct($"{tree}[{new_ptr}].child_type.rt.Armada_RootTypeDynamicHeap?");
      next.AddDefinedBehaviorConjunct($"{new_ptrs} !! {h}.valid");
      next.AddDefinedBehaviorConjunct($"{new_ptrs} !! {h}.freed");

      // We model it as undefined behavior if a non-positive number was passed as the count.
      // The reason we don't allow allocation of a 0-size array is as follows.  What we return
      // is a pointer to the 0th element, and there is no 0th element to return if we allocate
      // an array of size 0.

      next.AddUndefinedBehaviorAvoidanceConstraint($"({count}) > 0");

      var s_current = $"{s}.(mem := {s}.mem.(heap := {s}.mem.heap.(valid := {s}.mem.heap.valid + {new_ptrs})))";
      s_current = next.AddVariableDeclaration("s", s_current);

      // new_ptr is a valid pointer in s_current.mem.heap to a SizedArrayType.

      var h_current = $"{s_current}.mem.heap";
      next.AddDefinedBehaviorConjunct(AH.GetInvocationOfValidPointerToDynamicArray(h_current, new_ptr, rhs.AllocatedType, count));

      var descendants = AH.GetInvocationOfDescendantsOfDynamicArray(h_current, new_ptr, rhs.AllocatedType, count);
      next.AddDefinedBehaviorConjunct($"(forall p :: p in new_ptrs <==> p in ({descendants}))");

      // There's a difference in Armada between a pointer to an array and the pointer to its 0th element.
      // (The former is just a proof construct in the case of a calloc.)  So we need to get a pointer to
      // the 0th element to store in the left-hand side.

      var child = $"{tree}[{new_ptr}].children[0]";

      // s_current := lhs.update_state(s_current, child);

      var current_context = new NormalResolutionContext(s_current, next, parse.symbols);
      var newLhs = current_context.ResolveAsLValue(lhs);
      if (!(newLhs is ArmadaLValue)) {
        next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
        return;
      }
      next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

      s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, child)
                                          : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, child, startPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      parse.symbols.AddNextRoutineConstructor(next);

      //////////////////////////////////////////////////////////////////////////////
      // Now, create a next routine for the case where calloc fails.
      //////////////////////////////////////////////////////////////////////////////

      next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.CallocFailure, parse.methodInfo,
                                        this, stmt, startPC, endPC);
      current_context = new NormalResolutionContext(next.s, next, parse.symbols);

      // s_current := lhs.update_state(s_current, new_ptr);

      newLhs = current_context.ResolveAsLValue(lhs);
      if (!(newLhs is ArmadaLValue)) {
        next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
        return;
      }
      next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());
      s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, "0")
                                          : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, "0", startPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      if (other is ArmadaCallocStatement ams) {
        return AH.TypesMatch(((CallocRhs)stmt.Rhss[0]).AllocatedType, ((CallocRhs)((UpdateStmt)ams.Stmt).Rhss[0]).AllocatedType);
      }
      else {
        return false;
      }
    }
  }

  public class ArmadaCompareAndSwapStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaCompareAndSwapStatement(ParseInfo i_parse, UpdateStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      if (stmt.Lhss.Count > 1) {
        AH.PrintError(parse.prog, stmt.Tok, $"Number of left-hand sides for compare-and-swap must be 1");
        return;
      }

      var rhs = (CompareAndSwapRhs)stmt.Rhss[0];
      var target = rhs.Target;
      var oldval = rhs.OldVal;
      var newval = rhs.NewVal;

      if (!AH.TypesMatch(target.Type, oldval.Type)) {
        AH.PrintError(parse.prog, stmt.Tok, $"The target has type {target.Type} but the comparison value is of type {oldval.Type}");
        return;
      }
      if (!AH.TypesMatch(target.Type, newval.Type)) {
        AH.PrintError(parse.prog, stmt.Tok, $"The target has type {target.Type} but the new value is of type {newval.Type}");
        return;
      }

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.CompareAndSwap, parse.methodInfo,
                                            this, stmt, startPC, endPC);

      // Compare-and-swap is a locked routine, so it implies a fence.
      // So, add the constraint |s.threads[tid].storeBuffer| == 0.

      next.AddConjunct($"|({next.t}).storeBuffer| == 0");

      // Add undefined-behavior constraints for evaluating the parameters to compare_and_swap.
      // Use a TSO-bypassing context for all the rvalues since they use the global view of memory.
      // (It is a LOCK'd instruction, after all, so the store buffer is empty.)

      var resolutionContext = new NormalResolutionContext(next, parse.symbols);
      var tsoBypassingContext = new TSOBypassingResolutionContext(next, parse.symbols);
      var targetLValue = resolutionContext.ResolveAsLValue(target);
      next.AddUndefinedBehaviorAvoidanceConstraint(targetLValue.GetUndefinedBehaviorAvoidanceConstraint());
      var targetRValue = tsoBypassingContext.ResolveAsRValue(target);
      next.AddUndefinedBehaviorAvoidanceConstraint(targetRValue.UndefinedBehaviorAvoidance);
      var oldRValue = tsoBypassingContext.ResolveAsRValue(oldval);
      next.AddUndefinedBehaviorAvoidanceConstraint(oldRValue.UndefinedBehaviorAvoidance);
      var newRValue = tsoBypassingContext.ResolveAsRValue(newval);
      next.AddUndefinedBehaviorAvoidanceConstraint(newRValue.UndefinedBehaviorAvoidance);

      // s_current := if target == oldval then <update state setting target to newval> else next.s;

      var targetMatchesOld = next.AddVariableDeclaration("m", $"({targetRValue.Val}) == ({oldRValue.Val})");
      var s_after_value_update = targetLValue.UpdateTotalStateBypassingStoreBuffer(resolutionContext, next, newRValue.Val);
      var s_current = $"if {targetMatchesOld} then {s_after_value_update} else {next.s}";
      s_current = next.AddVariableDeclaration("s", s_current);

      // If there's an LHS, then:
      // s_current := oldval

      if (stmt.Lhss.Count > 0) {
        var lhs = stmt.Lhss[0];
        if (!AH.TypesMatch(target.Type, lhs.Type)) {
          AH.PrintError(parse.prog, stmt.Tok, $"The target has type {target.Type} but the left hand side is of type {lhs.Type}");
          return;
        }
        ResolutionContext updated_context = new NormalResolutionContext(s_current, next, parse.symbols);
        var lhsLValue = updated_context.ResolveAsLValue(lhs);
        if (lhsLValue.IsHeap()) {
          AH.PrintError(parse.prog, stmt.Tok, $"The result of an atomic-exchange instruction may not be stored in a shared heap variable; it must be stored in a local variable.");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(lhsLValue.GetUndefinedBehaviorAvoidanceConstraint());
        s_current = lhsLValue.UpdateTotalStateBypassingStoreBuffer(updated_context, next, targetRValue.Val);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      // s_current := Armada_UpdatePC(s_current, tid, {end PC})

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaCompareAndSwapStatement;
    }
  }

  public class ArmadaAtomicExchangeStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaAtomicExchangeStatement(ParseInfo i_parse, UpdateStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      if (stmt.Lhss.Count > 1) {
        AH.PrintError(parse.prog, stmt.Tok, $"Number of left-hand sides for atomic-exchange must be 1");
        return;
      }

      var rhs = (AtomicExchangeRhs)stmt.Rhss[0];
      var target = rhs.Target;
      var newval = rhs.NewVal;

      if (!AH.TypesMatch(target.Type, newval.Type)) {
        AH.PrintError(parse.prog, stmt.Tok, $"The target has type {target.Type} but the new value is of type {newval.Type}");
        return;
      }

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.AtomicExchange, parse.methodInfo,
                                            this, stmt, startPC, endPC);

      // atomic exchange is a locked routine, so it implies a fence.
      // So, add the constraint |s.threads[tid].storeBuffer| == 0.

      next.AddConjunct($"|({next.t}).storeBuffer| == 0");

      // Add undefined-behavior constraints for evaluating the parameters to atomic_exchange.
      // Use a TSO-bypassing context for all the rvalues since they use the global view of memory.
      // (It is a LOCK'd instruction, after all, so the store buffer is empty.)

      var resolutionContext = new NormalResolutionContext(next, parse.symbols);
      var tsoBypassingContext = new TSOBypassingResolutionContext(next, parse.symbols);
      var targetLValue = resolutionContext.ResolveAsLValue(target);
      next.AddUndefinedBehaviorAvoidanceConstraint(targetLValue.GetUndefinedBehaviorAvoidanceConstraint());
      var targetRValue = tsoBypassingContext.ResolveAsRValue(target);
      next.AddUndefinedBehaviorAvoidanceConstraint(targetRValue.UndefinedBehaviorAvoidance);
      var newRValue = tsoBypassingContext.ResolveAsRValue(newval);
      next.AddUndefinedBehaviorAvoidanceConstraint(newRValue.UndefinedBehaviorAvoidance);

      // s_current := update state setting target to newval;

      var s_current = targetLValue.UpdateTotalStateBypassingStoreBuffer(resolutionContext, next, newRValue.Val);
      s_current = next.AddVariableDeclaration("s", s_current);

      // If there's an LHS, then:
      // s_current := <update state setting lhs to old value of target>

      if (stmt.Lhss.Count > 0) {
        var lhs = stmt.Lhss[0];
        if (!AH.TypesMatch(target.Type, lhs.Type)) {
          AH.PrintError(parse.prog, stmt.Tok, $"The target has type {target.Type} but the left hand side is of type {lhs.Type}");
          return;
        }
        ResolutionContext updated_context = new NormalResolutionContext(s_current, next, parse.symbols);
        var lhsLValue = updated_context.ResolveAsLValue(lhs);
        if (lhsLValue.IsHeap()) {
          AH.PrintError(parse.prog, stmt.Tok,
                        $"The result of an atomic-exchange instruction may not be stored in a shared heap variable; it must be stored in a local variable.");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(lhsLValue.GetUndefinedBehaviorAvoidanceConstraint());
        s_current = lhsLValue.UpdateTotalStateBypassingStoreBuffer(updated_context, next, targetRValue.Val);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      // s_current := Armada_UpdatePC(s_current, tid, {end PC})

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaAtomicExchangeStatement;
    }
  }

  public class ArmadaUpdateStatement : ArmadaStatement
  {
    private UpdateStmt stmt;
    private bool genuineTSO;

    public ArmadaUpdateStatement(ParseInfo i_parse, UpdateStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
      genuineTSO = ! i_stmt.BypassStoreBuffers;
    }

    public override Statement Stmt { get { return stmt; } }

    public bool GenuineTSO { get { return genuineTSO; } }

    public override void GenerateNextRoutines()
    {
      if (stmt.Lhss.Count != stmt.Rhss.Count) {
        AH.PrintError(parse.prog, stmt.Tok, $"Number of left-hand sides for assignment ({stmt.Lhss.Count}) statement doesn't match number of right-hand sides ({stmt.Rhss.Count}).");
        return;
      }

      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Update, parse.methodInfo,
                                            this, stmt, startPC, endPC);

      var s_current = next.s;
      for (int i = 0; i < stmt.Lhss.Count; ++i) {
        var resolutionContext = new NormalResolutionContext(s_current, next, parse.symbols);

        var lhs = stmt.Lhss.ElementAt(i);
        var newLhs = resolutionContext.ResolveAsLValue(lhs);

        if (newLhs.NoTSO()) {
          genuineTSO = false;
        }

        if (newLhs == null) {
          next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        var rhs = stmt.Rhss.ElementAt(i);
        string newRhs;
        if (rhs is HavocRhs) {
          newRhs = next.AddFormal(new NextFormal($"nondet{i}_{startPC}", $"nondet{i}", lhs.Type, parse.symbols));
        }
        else if (rhs is ExprRhs) {
          var erhs = (ExprRhs)rhs;
          var newRhsRValue = resolutionContext.ResolveAsRValue(erhs.Expr);
          next.AddUndefinedBehaviorAvoidanceConstraint(newRhsRValue.UndefinedBehaviorAvoidance);
          newRhs = newRhsRValue.Val;
        }
        else if (rhs is CreateThreadRhs) {
          next.Fail(rhs.Tok, "Create-thread can't be done in parallel with other assignments");
          return;
        }
        else if (rhs is MallocRhs || rhs is CallocRhs) {
          next.Fail(rhs.Tok, "Allocation can't be done in parallel with other assignments");
          return;
        }
        else if (rhs is CompareAndSwapRhs) {
          next.Fail(rhs.Tok, "Compare-and-swap can't be done in parallel with other assignments");
          return;
        }
        else if (rhs is AtomicExchangeRhs) {
          next.Fail(rhs.Tok, "atomic-exchange can't be done in parallel with other assignments");
          return;
        }
        else {
          next.Fail(rhs.Tok, "Right-hand side is not a valid rvalue");
          return;
        }

        // var s_current := lhs.update_state(s_current, rhs);
        s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(resolutionContext, next, newRhs)
                                            : newLhs.UpdateTotalStateWithStoreBufferEntry(resolutionContext, next, newRhs, startPC);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      var nextState = UpdatePC(s_current, next.tid, endPC);
      next.SetNextState(nextState);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      if (other is ArmadaUpdateStatement) {
        var us = (UpdateStmt)other.Stmt;
        if (stmt.Lhss.Count != us.Lhss.Count) {
          return true; // Maybe it's a variable introduction or variable hiding
        }
        for (int i = 0; i < stmt.Rhss.Count; ++i) {
          var rhs = stmt.Rhss.ElementAt(i);
          var otherRhs = us.Rhss.ElementAt(i);
          if (rhs is CreateThreadRhs && !(otherRhs is CreateThreadRhs)) {
            return false;
          }
          if (otherRhs is CreateThreadRhs && !(rhs is CreateThreadRhs)) {
            return false;
          }
          if (rhs is MallocRhs && !(otherRhs is MallocRhs)) {
            return false;
          }
          if (otherRhs is MallocRhs && !(rhs is MallocRhs)) {
            return false;
          }
          if (rhs is CallocRhs && !(otherRhs is CallocRhs)) {
            return false;
          }
          if (otherRhs is CallocRhs && !(rhs is CallocRhs)) {
            return false;
          }
          if (rhs is CompareAndSwapRhs && !(otherRhs is CompareAndSwapRhs)) {
            return false;
          }
          if (otherRhs is CompareAndSwapRhs && !(rhs is CompareAndSwapRhs)) {
            return false;
          }
          if (rhs is AtomicExchangeRhs && !(otherRhs is AtomicExchangeRhs)) {
            return false;
          }
          if (otherRhs is AtomicExchangeRhs && !(rhs is AtomicExchangeRhs)) {
            return false;
          }
        }
        return true;
      }
      else {
        return false;
      }
    }
  }

  public class ArmadaVarDeclStatement : ArmadaStatement
  {
    private VarDeclStmt stmt;

    public ArmadaVarDeclStatement(ParseInfo i_parse, VarDeclStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override ArmadaPC AssignPCs(ArmadaPC i_startPC)
    {
      if (i_startPC.instructionCount > 0) {
        if (stmt.Update != null) {
          AH.PrintError(parse.prog, stmt.Tok, "In Armada, all stack variables for a method are created and initialized atomically with the stack frame getting pushed onto the stack.  So, it's a bad idea to have a variable declaration with an initialization value, like this one, somewhere other than the beginning of the method.  After all, in this case the semantics will not be what seems intuitive from reading the code.");
        }
        else {
          AH.PrintWarning(parse.prog, stmt.Tok, "Note that, in Armada, all stack variables for a method are created and initialized atomically with the stack frame getting pushed onto the stack.  So, it's generally a good idea to have all variable declarations at the beginnings of methods.  Otherwise, the semantics may not be what seems intuitive from reading the code.");
        }
      }
      return endPC = startPC = i_startPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
      if (stmt.Update != null && inExplicitYieldBlock) {
        potentiallyNonyieldingPCs.Add(startPC);
      }
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaVarDeclStatement;
    }
  }

  public class ArmadaReturnStatement : ArmadaStatement
  {
    private ReturnStmt stmt;

    public ArmadaReturnStatement(ParseInfo i_parse, ReturnStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      if (stmt.rhss != null && stmt.rhss.Count > 0) {
        AH.PrintError(parse.prog, stmt.Tok, "Armada doesn't allow arguments in return statements. You should just assign to output variables and then use a return statement with no arguments.");
        return;
      }
      
      // We model a return statement as a goto with the target being the method's end PC.

      var targetPC = parse.methodInfo.ReturnPC;
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Goto, parse.methodInfo,
                                            this, stmt, startPC, targetPC);

      // s' == Armada_UpdatePC(s, tid, targetPC)

      var s_with_new_PC = UpdatePC(next.s, next.tid, targetPC);
      next.SetNextState(s_with_new_PC);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaReturnStatement;
    }
  }

  public class ArmadaAssertStatement : ArmadaStatement
  {
    private AssertStmt stmt;

    public ArmadaAssertStatement(ParseInfo i_parse, AssertStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      // First, create the NextRoutine for the case where the assertion succeeds.
      
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.AssertTrue, parse.methodInfo,
                                            this, stmt, startPC, endPC);
      var resolutionContext = new NormalResolutionContext(next, parse.symbols);

      // s' == Armada_UpdatePC(s, tid, endPC)

      var rvalue = resolutionContext.ResolveAsRValue(stmt.Expr);
      next.AddUndefinedBehaviorAvoidanceConstraint(rvalue.UndefinedBehaviorAvoidance);
      next.AddDefinedBehaviorConjunct(rvalue.Val);

      var s_prime = UpdatePC(next.s, next.tid, endPC);
      next.SetNextState(s_prime);
      parse.symbols.AddNextRoutineConstructor(next);

      // Second, create the NextRoutine for the case where the assertion fails.

      next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.AssertFalse, parse.methodInfo,
                                        this, stmt, startPC, endPC);
      resolutionContext = new NormalResolutionContext(next, parse.symbols);

      rvalue = resolutionContext.ResolveAsRValue(stmt.Expr);
      next.AddUBAvoidanceConstraintAsDefinedBehaviorConjunct(rvalue.UndefinedBehaviorAvoidance);
      next.AddDefinedBehaviorConjunct($"!({rvalue.Val})");

      // s' == s.(stop_reason := Armada_StopReasonAssertionFailure)

      s_prime = $"({next.s}).(stop_reason := Armada_StopReasonAssertionFailure)";
      next.SetNextState(s_prime);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaAssertStatement;
    }
  }

  public class ArmadaAssumeStatement : ArmadaStatement
  {
    private AssumeStmt stmt;

    public ArmadaAssumeStatement(ParseInfo i_parse, AssumeStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override ArmadaPC AssignPCs(ArmadaPC i_startPC)
    {
      return endPC = startPC = i_startPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
    }

    public override void GenerateEnablingConstraints()
    {
      parse.methodInfo.AddEnablingConstraint(parse.prog, startPC, stmt.Expr);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaAssumeStatement;
    }
  }

  public class ArmadaSomehowStatement : ArmadaStatement
  {
    private SomehowStmt stmt;

    public ArmadaSomehowStatement(ParseInfo i_parse, SomehowStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Somehow, parse.methodInfo,
                                            this, stmt, startPC, endPC);
      var method = parse.methodInfo.method;

      var top = $"({next.t}).top";
      var ghosts = $"({next.s}).ghosts";
      var start_read_context = new CustomResolutionContext(next.s, next.s, next.locv, top,
                                                           ghosts, next.tid, method.Name, parse.symbols, next);

      // Add each undefined_unless clause as an undefined-behavior-avoidance constraint, to model that the
      // instruction may have arbitrary behavior if those constraints aren't met at the outset.

      foreach (var undefined_unless_clause in stmt.UndefinedUnless) {
        var uuc = start_read_context.ResolveAsRValue(undefined_unless_clause);
        next.AddUndefinedBehaviorAvoidanceConstraint(uuc.UndefinedBehaviorAvoidance);
        next.AddUndefinedBehaviorAvoidanceConstraint(uuc.Val);
      }

      // Compute each s{i+1} by updating a single modifies element in s{i}.

      var s_current = next.s;
      for (int i = 0; i < stmt.Mod.Expressions.Count; ++i) {
        var lhs = stmt.Mod.Expressions.ElementAt(i);

        var nextFormal = new NextFormal($"newval{i}_{startPC}", $"newval{i}", lhs.Type, parse.symbols);
        var newRhs = next.AddFormal(nextFormal);

        //
        // It's important that we model the external method as
        // updating the state using store-buffer entries if the {:tso}
        // annotation appears on the modifies clause.  If we model it
        // as updating the state directly, then this doesn't permit
        // any behavior in which the external method updates the store
        // buffer and then, after it's returned, a tau causes the
        // modification to be reflected in real state.
        //

        // s_current := lhs.update_state(s_current, newRhs);
        var current_context = new NormalResolutionContext(s_current, next, parse.symbols);
        var newLhs = current_context.ResolveAsLValue(lhs);
        if (!(newLhs is ArmadaLValue)) {
          next.Fail(lhs.tok, "Modifies element is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        s_current = Attributes.Contains(stmt.Mod.Attributes, "tso") ?
          newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, newRhs, startPC) :
          newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, newRhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      // s_current := Armada_UpdatePC(s_current, tid, endPC);

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s' must be equal to the updated s we just computed

      next.SetNextState(s_current);

      // For each ensures clause, add another condition that the clause holds in s' (as viewed by the local thread).

      if (stmt.Ens.Count > 0) {
        var end_read_context = new EnsuresResolutionContext(next.s, s_current, next.tid, method.Name, parse.symbols, next, null);

        foreach (var ens in stmt.Ens) {
          var ens_resolved = end_read_context.ResolveAsRValue(ens);
          next.AddUBAvoidanceConstraintAsDefinedBehaviorConjunct(ens_resolved.UndefinedBehaviorAvoidance);
          next.AddDefinedBehaviorConjunct(ens_resolved.Val);
        }
      }

      // We're done building the next routine, so add it to the list of nexts.

      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaSomehowStatement;
    }
  }

  public class ArmadaFenceStatement : ArmadaStatement
  {
    private FenceStmt stmt;

    public ArmadaFenceStatement(ParseInfo i_parse, FenceStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Fence, parse.methodInfo,
                                            this, stmt, startPC, endPC);

      // |s.threads[tid].storeBuffer| == 0

      next.AddConjunct($"|({next.t}).storeBuffer| == 0");

      // s' == Armada_UpdatePC(s, tid, endPC)

      var s_with_new_PC = UpdatePC(next.s, next.tid, endPC);
      next.SetNextState(s_with_new_PC);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaFenceStatement;
    }
  }

  public class ArmadaGotoStatement : ArmadaStatement
  {
    private GotoStmt stmt;

    public ArmadaGotoStatement(ParseInfo i_parse, GotoStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      var targetPC = parse.symbols.GetPCForMethodAndLabel(parse.methodInfo.method.Name + "_" + stmt.Target);
      if (targetPC == null) {
        AH.PrintError(parse.prog, $"ERROR:  No label found in method {parse.methodInfo.method.Name} with name {stmt.Target}");
      }
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Goto, parse.methodInfo,
                                            this, stmt, startPC, targetPC);

      // s' == Armada_UpdatePC(s, tid, targetPC)

      var s_with_new_PC = UpdatePC(next.s, next.tid, targetPC);
      next.SetNextState(s_with_new_PC);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaGotoStatement;
    }
  }

  public class ArmadaDeallocStatement : ArmadaStatement
  {
    private DeallocStmt stmt;

    public ArmadaDeallocStatement(ParseInfo i_parse, DeallocStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Dealloc, parse.methodInfo,
                                            this, stmt, startPC, endPC);
      var resolutionContext = new NormalResolutionContext(next, parse.symbols);

      if (stmt.Addr.Type == null)
      {
        next.Fail(stmt.Tok, "Attempt to dealloc an address whose type isn't known");
        return;
      }
      Type subtype;
      string err;
      if (!AH.GetDereferenceType(stmt.Addr.Type, out subtype, out err))
      {
        next.Fail(stmt.Tok, err);
        return;
      }

      var addrRValue = resolutionContext.ResolveAsRValue(stmt.Addr);
      next.AddUndefinedBehaviorAvoidanceConstraint(addrRValue.UndefinedBehaviorAvoidance);

      var addr = next.AddVariableDeclaration("addr", addrRValue.Val);

      var s = $"({next.s})";
      var h = $"{s}.mem.heap";
      var tree = $"{h}.tree";

      // Experience undefined behavior if tree-forest properties don't hold
      next.AddUndefinedBehaviorAvoidanceConstraint($"Armada_TreeForestProperties({tree})");

      // Experience undefined behavior if addr isn't valid
      next.AddUndefinedBehaviorAvoidanceConstraint(AH.GetInvocationOfValidPointer(h, addr, subtype));

      //
      // If 'addr' is a pointer to the 0th element of an array, then
      // free its parent pointer instead, i.e., free the pointer to
      // the array.  We can't require the Armada code to pass us that
      // array pointer because there's no way to get that pointer in
      // Armada.  After all, calloc returns a pointer to the 0th element
      // and there's no way to go "up" to the pointer to the array.
      //

      // var addr_to_free := if tree[addr].child_type.Armada_ChildTypeIndex? && tree[addr].child_type.i == 0 then
      //                         tree[addr].parent else addr
      // Experience undefined behavior if we're using the parent and the parent isn't in the tree

      var use_parent = next.AddVariableDeclaration(
        "use_parent",
        $"{tree}[{addr}].child_type.Armada_ChildTypeIndex? && {tree}[{addr}].child_type.i == 0"
      );
      var parent = $"{tree}[{addr}].parent";
      next.AddUndefinedBehaviorAvoidanceConstraint($"{use_parent} ==> {parent} in {tree}");
      var addr_to_free = next.AddVariableDeclaration("addr_to_free", $"if {use_parent} then {parent} else {addr}");

      // Experience undefined behavior if we're freeing something that isn't a root
      next.AddUndefinedBehaviorAvoidanceConstraint($"{tree}[{addr_to_free}].child_type.Armada_ChildTypeRoot?");
      next.AddUndefinedBehaviorAvoidanceConstraint($"{tree}[{addr_to_free}].child_type.rt.Armada_RootTypeDynamicHeap?");

      // var descendants := set d | d in tree && Armada_PointerIsAncestorOfPointer(tree, addr_to_free, d) :: d;
      var descendants = $"Armada_DescendantsOfPointer({tree}, {addr_to_free})";
      descendants = next.AddVariableDeclaration("descendants", descendants);

      // Update valid and freed pointer sets

      var s_current = $"{s}.(mem := {s}.mem.(heap := {h}.(valid := {h}.valid - {descendants}, freed := {h}.freed + {descendants})))";
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaDeallocStatement;
    }
  }

  public class ArmadaJoinStatement : ArmadaStatement
  {
    private JoinStmt stmt;

    public ArmadaJoinStatement(ParseInfo i_parse, JoinStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.Join, parse.methodInfo,
                                            this, stmt, startPC, endPC);
      var resolutionContext = new NormalResolutionContext(next, parse.symbols);

      var s = $"({next.s})";
      var join_tid = resolutionContext.ResolveAsRValue(stmt.WhichThread);
      var join_tid_undefined_behavior_avoidance = join_tid.UndefinedBehaviorAvoidance;
      next.AddUndefinedBehaviorAvoidanceConstraint(join_tid_undefined_behavior_avoidance);

      // It's undefined behavior to join a thread that isn't either running or joinable.
      // For instance, once you join a thread you can't join it again.

      next.AddUndefinedBehaviorAvoidanceConstraint($"({join_tid.Val}) in {s}.threads || ({join_tid.Val}) in {s}.joinable_tids");

      // The step is enabled only when join_tid is in s.joinable_tids.

      next.AddDefinedBehaviorConjunct($"({join_tid.Val}) in {s}.joinable_tids");

      // Remove the joined thread from the set of joinable threads, to model the fact that a join
      // releases the thread's resources and thus makes it illegal to join it again.
      //
      // s_current := s.(joinable_tids := joinable_tids - {join_tid});

      var s_current = next.AddVariableDeclaration("s", $"{s}.(joinable_tids := {s}.joinable_tids - {{ {join_tid.Val} }})");

      // s' == Armada_UpdatePC(s_current, tid, endPC)

      var s_with_new_PC = UpdatePC(s_current, next.tid, endPC);
      next.SetNextState(s_with_new_PC);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaJoinStatement;
    }
  }

  public class ArmadaBreakStatement : ArmadaStatement
  {
    private BreakStmt stmt;
    private ArmadaWhileStatement innermostEnclosingWhile;

    public ArmadaBreakStatement(ParseInfo i_parse, BreakStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
      innermostEnclosingWhile = parse.innermostEnclosingWhile;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.WhileBreak, parse.methodInfo,
                                            this, stmt, startPC, innermostEnclosingWhile.EndPC);
      var s_with_new_PC = UpdatePC(next.s, next.tid, innermostEnclosingWhile.EndPC);
      next.SetNextState(s_with_new_PC);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaBreakStatement;
    }
  }

  public class ArmadaContinueStatement : ArmadaStatement
  {
    private ContinueStmt stmt;
    private ArmadaWhileStatement innermostEnclosingWhile;

    public ArmadaContinueStatement(ParseInfo i_parse, ContinueStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
      innermostEnclosingWhile = parse.innermostEnclosingWhile;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines()
    {
      var next = new NextRoutineConstructor(parse.prog, parse.symbols, NextType.WhileContinue, parse.methodInfo,
                                            this, stmt, startPC, innermostEnclosingWhile.StartPC);
      var s_with_new_PC = UpdatePC(next.s, next.tid, innermostEnclosingWhile.StartPC);
      next.SetNextState(s_with_new_PC);
      parse.symbols.AddNextRoutineConstructor(next);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaContinueStatement;
    }
  }

  public class ArmadaYieldStatement : ArmadaStatement
  {
    private YieldStmt stmt;

    public ArmadaYieldStatement(ParseInfo i_parse, YieldStmt i_stmt) : base(i_parse)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override ArmadaPC AssignPCs(ArmadaPC i_startPC)
    {
      endPC = startPC = i_startPC;
      return endPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
      yieldPCs.Add(startPC);
    }

    public override bool RoughlyMatches(ArmadaStatement other)
    {
      return other is ArmadaYieldStatement;
    }
  }
}
