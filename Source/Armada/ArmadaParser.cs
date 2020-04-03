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
  public class ParseContext
  {
    public Program prog;
    public ArmadaSymbolTable symbols;
    public MethodInfo methodInfo;
    public ArmadaWhileStatement innermostEnclosingWhile;

    public ParseContext(Program i_prog, ArmadaSymbolTable i_symbols, MethodInfo i_methodInfo)
    {
      prog = i_prog;
      symbols = i_symbols;
      methodInfo = i_methodInfo;
      innermostEnclosingWhile = null;
    }

    public ParseContext Clone()
    {
      var other = new ParseContext(prog, symbols, methodInfo);
      other.innermostEnclosingWhile = this.innermostEnclosingWhile;
      return other;
    }
  }

  public abstract class ArmadaStatement
  {
    protected ArmadaPC startPC;
    protected ArmadaPC endPC;
    protected NextRoutine nextRoutine;

    public virtual Statement Stmt { get { return null; } }
    public ArmadaPC StartPC { get { return startPC; } }
    public ArmadaPC EndPC { get { return endPC; } }
    public NextRoutine NxtRoutine { get { return nextRoutine; } }

    public ArmadaStatement(ParseContext context)
    {
      startPC = null;
      endPC = null;
      nextRoutine = null;
    }

    public static ArmadaStatement ParseStatementInternal(ParseContext context, Statement stmt)
    {
      if (stmt == null)
      {
        return null;
      }
      else if (stmt is BlockStmt)
      {
        var s = (BlockStmt)stmt;
        return new ArmadaBlockStatement(context, s);
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
                if (context.symbols.DoesMethodNameExist(suffixName.Name)) {
                  return new ArmadaCallStatement(context, s, suffixName.Name);
                }
              }
            }
          }
          else if (rhs is CreateThreadRhs) {
            return new ArmadaCreateThreadStatement(context, s);
          }
          else if (rhs is MallocRhs) {
            return new ArmadaMallocStatement(context, s);
          }
          else if (rhs is CallocRhs) {
            return new ArmadaCallocStatement(context, s);
          }
        }

        return new ArmadaUpdateStatement(context, s);
      }
      else if (stmt is IfStmt)
      {
        var s = (IfStmt)stmt;
        return new ArmadaIfStatement(context, s);
      }
      else if (stmt is WhileStmt)
      {
        var s = (WhileStmt)stmt;
        context = context.Clone();
        return new ArmadaWhileStatement(context, s);
      }
      else if (stmt is VarDeclStmt)
      {
        var s = (VarDeclStmt)stmt;
        return new ArmadaVarDeclStatement(context, s);
      }
      else if (stmt is ReturnStmt)
      {
        var s = (ReturnStmt)stmt;
        return new ArmadaReturnStatement(context, s);
      }
      else if (stmt is AssertStmt)
      {
        var s = (AssertStmt)stmt;
        return new ArmadaAssertStatement(context, s);
      }
      else if (stmt is AssumeStmt)
      {
        var s = (AssumeStmt)stmt;
        return new ArmadaAssumeStatement(context, s);
      }
      else if (stmt is SomehowStmt)
      {
        var s = (SomehowStmt)stmt;
        return new ArmadaSomehowStatement(context, s);
      }
      else if (stmt is DeallocStmt)
      {
        var s = (DeallocStmt)stmt;
        return new ArmadaDeallocStatement(context, s);
      }
      else if (stmt is JoinStmt)
      {
        var s = (JoinStmt)stmt;
        return new ArmadaJoinStatement(context, s);
      }
      else if (stmt is BreakStmt)
      {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          AH.PrintError(context.prog, stmt.Tok, "Armada doesn't support breaks with statement labels");
        }
        if (s.BreakCount != 1) {
          AH.PrintError(context.prog, stmt.Tok, "Armada doesn't support breaks with counts other than 1");
        }
        if (context.innermostEnclosingWhile == null) {
          AH.PrintError(context.prog, stmt.Tok, "Can't have a break that isn't inside of a while loop");
        }
        return new ArmadaBreakStatement(context, s);
      }
      else if (stmt is ContinueStmt)
      {
        var s = (ContinueStmt)stmt;
        if (context.innermostEnclosingWhile == null) {
          AH.PrintError(context.prog, stmt.Tok, "Can't have a continue that isn't inside of a while loop");
        }
        return new ArmadaContinueStatement(context, s);
      }
      else if (stmt is YieldStmt)
      {
        var s = (YieldStmt)stmt;
        return new ArmadaYieldStatement(context, s);
      }
      else
      {
        AH.PrintWarning(context.prog, stmt.Tok, "Armada doesn't yet support this statement type");
        return null;
      }
    }

    public static ArmadaStatement ParseStatement(ParseContext context, Statement stmt)
    {
      if (stmt == null) {
        return null;
      }
      stmt.Parsed = ParseStatementInternal(context, stmt);
      return stmt.Parsed;
    }

    public virtual IEnumerator<ArmadaStatement> GetEnumerator()
    {
      yield return this;
    }

    public virtual ArmadaPC AssignPCs(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo, ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      endPC = methodInfo.GenerateOnePC();
      return endPC;
    }

    public static void CollectReturnPCs(ArmadaStatement stmt, List<ArmadaPC> returnPCs)
    {
      foreach (var substmt in stmt) {
        if (substmt is ArmadaReturnStatement) {
          returnPCs.Add(substmt.StartPC);
        }
      }
      returnPCs.Add(stmt.endPC);
    }

    public virtual PCNode GeneratePCStructureForStatement(PCNode endNode, PCNode breakTarget, PCNode continueTarget,
                                                          HashSet<ArmadaPC> loopHeads)
    {
      if (nextRoutine != null) {
        return new NormalPCNode(startPC, nextRoutine, endNode);
      }
      else {
        return endNode;
      }
    }

    public Expression UpdatePC(ArmadaSymbolTable symbols, MethodInfo methodInfo, Expression s, Expression tid, ArmadaPC newPC)
    {
      var newPCExpr = AH.MakeNameSegment(newPC.ToString(), "Armada_PC");
      return AH.MakeApply3("Armada_UpdatePC", s, tid, newPCExpr, "Armada_TotalState");
    }

    public virtual void AssociateLabelWithStatement(ArmadaSymbolTable symbols, string lbl)
    {
      symbols.AssociateLabelWithPC(lbl, startPC);
    }

    public void AssociateLabelsWithPCs(ArmadaSymbolTable symbols)
    {
      Statement stmt = Stmt;
      if (stmt != null) {
        for (var lbl = stmt.Labels; lbl != null; lbl = lbl.Next) {
          if (lbl.Data != null && lbl.Data.Name != null) {
            AssociateLabelWithStatement(symbols, lbl.Data.Name);
          }
        }
      }
    }

    public virtual void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
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

    protected void GetStackFrameForCallOrCreateThread(Program prog, ArmadaSymbolTable symbols, NextRoutine next, ResolutionContext context,
                                                      string calleeName, IEnumerable<Expression> args, ref Expression s_current,
                                                      out Expression new_frame, out Expression new_ptrs)
    {
      // First, allocate new pointers to represent the addressable stack variables:
      //
      // s_current := s.(mem := s.mem.(heap := s.mem.heap.(valid := s.mem.heap.valid + new_ptrs)))

      next.AddFormal(new NextFormal($"new_ptrs_{startPC}", "new_ptrs", AH.MakePointerSetType()));
      new_ptrs = AH.MakeNameSegment("new_ptrs", AH.MakePointerSetType());

      var mem = AH.MakeExprDotName(s_current, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
      var valid = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
      var valid_plus_new = AH.MakeAddExpr(valid, new_ptrs);
      var h_updated = AH.MakeDatatypeUpdateExpr(h, "valid", valid_plus_new);
      var mem_updated = AH.MakeDatatypeUpdateExpr(mem, "heap", h_updated);
      s_current = AH.MakeDatatypeUpdateExpr(s_current, "mem", mem_updated);
      s_current = next.AddVariableDeclaration("s", s_current);

      // The new_ptrs don't overlap the previous valid pointers, i.e., new_ptrs !! s.mem.heap.valid

      var valid_new_ptrs_disjoint = AH.MakeDisjointExpr(new_ptrs, valid);
      next.AddConjunct(valid_new_ptrs_disjoint);

      // Nothing that was freed has become valid, i.e., new_ptrs !! s.mem.heap.freed

      var freed = AH.MakeExprDotName(h, "freed", AH.MakePointerSetType());
      var valid_freed_disjoint = AH.MakeDisjointExpr(new_ptrs, freed);
      next.AddConjunct(valid_freed_disjoint);

      var mem_current = AH.MakeExprDotName(s_current, "mem", "Armada_SharedMemory");
      var h_current = AH.MakeExprDotName(mem_current, "heap", "Armada_Heap");

      // Next, compute the parameters to the new-frame
      // constructor. For each input field, get its value from the
      // arguments; for each non-input field, model its initial
      // value as non-deterministic.

      List<Expression> new_frame_elements = new List<Expression>();
      var smst = symbols.GetMethodSymbolTable(calleeName);
      string p_in_new_ptrs = "";
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
            var argVal = context.ResolveAsRValue(arg);
            next.AddUndefinedBehaviorAvoidanceConstraint(argVal.UndefinedBehaviorAvoidance);
            new_frame_elements.Add(argVal.Val);
          }
          continue;
        }

        var varName = v.name;
        var ty = symbols.FlattenType(v.ty);
        if (v is AddressableArmadaVariable) {
          // For addressable variables, we have to not only add a pointer to the new-frame constructor, we also
          // have to make sure the pointed-to values are allocated

          next.AddFormal(new NextFormal($"newframe_{startPC}_{varName}", $"newframe_{varName}", "Armada_Pointer"));
          var new_ptr = AH.MakeNameSegment($"newframe_{varName}", "Armada_Pointer");
          new_frame_elements.Add(new_ptr);

          // new_ptr is among new_ptrs

          var new_ptr_in_new_ptrs = AH.MakeInExpr(new_ptr, new_ptrs);
          next.AddConjunct(new_ptr_in_new_ptrs);

          // new_ptr is in s.mem.heap.tree

          var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
          var new_ptr_in_tree = AH.MakeInExpr(new_ptr, tree);
          next.AddConjunct(new_ptr_in_tree);

          // new_ptr is a stack-based root in s.mem.heap, i.e.,
          //    && s.mem.heap.tree[new_ptr].field_of_parent.Armada_FieldNone?
          //    && s.mem.heap.tree[new_ptr].field_of_parent.rt.Armada_RootTypeStack?

          var node = AH.MakeSeqSelectExpr(tree, new_ptr, "Armada_Node");
          var field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
          var new_ptr_is_root = AH.MakeExprDotName(field_of_parent, "Armada_FieldNone?", new BoolType());
          var root_type = AH.MakeExprDotName(field_of_parent, "rt", "Armada_RootType");
          var root_type_stack = AH.MakeExprDotName(root_type, "Armada_RootTypeStack?", new BoolType());
          next.AddConjunct(new_ptr_is_root);
          next.AddConjunct(root_type_stack);

          /*
          if (v.ty is SizedArrayType) {
          }
          else {
            p_in_new_ptrs += $"|| p in {AH.GetNameOfAllocator(v.ty)}(s2.mem.heap, newframe_{varName})";
          }
          */
          var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
            AH.MakeNameSegment("s2.mem.heap", "Armada_Heap"),
            AH.MakeNameSegment($"newframe_{varName}", "Armada_Pointer"),
            v.ty
          );
          p_in_new_ptrs += $"|| p in ({Printer.ExprToString(allocatedByExpr)})";
          addressesOfAddressables.Add($"newframe_{varName}");
          // new_ptr is a valid pointer in s_current.mem.heap

          var pointer_valid = AH.GetInvocationOfValidPointer(h_current, new_ptr, v.ty);
          next.AddConjunct(pointer_valid);
        }
        else {
          next.AddFormal(new NextFormal($"newframe_{startPC}_{varName}", $"newframe_{varName}", ty));
          var elt = AH.MakeNameSegment($"newframe_{varName}", ty);
          new_frame_elements.Add(elt);
        }
      }
      string str;
      if (p_in_new_ptrs.Length > 0) {
        str = $"forall p :: p in new_ptrs <==> ({p_in_new_ptrs})";
      }
      else {
        str = "new_ptrs == {}";
      }
      next.AddConjunct(AH.ParseExpression(prog, "", str));
      for (int i = 0; i < addressesOfAddressables.Count; i++) {
        for (int j = i + 1; j < addressesOfAddressables.Count; j++) {
          str = addressesOfAddressables[i] + " != " + addressesOfAddressables[j];
          next.AddConjunct(AH.ParseExpression(prog, "", str));
        }
      }

      // new_ptrs == Armada_Allocator_type1(local1) + ...
      // Equivalently, forall x :: x in new_ptrs <==> x in Armada_Allocator_type1(local1)

      // Finally, create the frame.
      // var new_frame := Armada_StackFrame_{calleeName}(input..., output..., normal..., reads...);

      var frame_ctor = AH.MakeNameSegment($"Armada_StackFrame_{calleeName}", (Type)null);
      var frame_type = AH.ReferToType("Armada_StackFrame");
      new_frame = AH.SetExprType(new ApplySuffix(Token.NoToken, frame_ctor, new_frame_elements), frame_type);
      new_frame = next.AddVariableDeclaration("new_frame", new_frame);
    }

    protected void PerformStackFrameInitializations(ArmadaSymbolTable symbols, NextRoutine next, string calleeName,
                                                    Expression tid, ref Expression s_current)
    {
      var smst = symbols.GetMethodSymbolTable(calleeName);
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.InitialValue != null))
      {
        var context = new ResolutionContext(s_current, s_current, tid, calleeName, symbols, next);
        var ty = symbols.FlattenType(v.ty);
        var lhs = v.GetLValue(v.InitialValue.tok, context);
        var rhsRVal = context.ResolveAsRValue(v.InitialValue);
        next.AddUndefinedBehaviorAvoidanceConstraint(rhsRVal.UndefinedBehaviorAvoidance);
        var rhs = rhsRVal.Val;

        bool bypassStoreBuffers = (v is MethodStackFrameAddressableLocalArmadaVariable) &&
                                  ((MethodStackFrameAddressableLocalArmadaVariable)v).TSOBypassingInitialization;

        // var s_current := lhs.update_state(s_current, rhs);
        s_current = bypassStoreBuffers ? lhs.UpdateTotalStateBypassingStoreBuffer(context, next, rhs)
                                       : lhs.UpdateTotalStateWithStoreBufferEntry(context, next, rhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }
    }
  }

  public class ArmadaBlockStatement : ArmadaStatement
  {
    private BlockStmt stmt;
    private List<ArmadaStatement> statements;

    public ArmadaBlockStatement(ParseContext context, BlockStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
      statements = stmt.Body.Select(x => ParseStatement(context, x)).ToList();
    }

    public override Statement Stmt { get { return stmt; } }

    public override IEnumerator<ArmadaStatement> GetEnumerator()
    {
      yield return this;
      foreach (var statement in statements) {
        foreach (var substatement in statement) {
          yield return substatement;
        }
      }
    }

    public override ArmadaPC AssignPCs(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo, ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      var currentPC = startPC;
      foreach (var statement in statements)
      {
        currentPC = statement.AssignPCs(prog, symbols, methodInfo, currentPC);
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

    public override PCNode GeneratePCStructureForStatement(PCNode endNode, PCNode breakTarget, PCNode continueTarget,
                                                           HashSet<ArmadaPC> loopHeads)
    {
      foreach (var substmt in Enumerable.Reverse(statements))
      {
        endNode = substmt.GeneratePCStructureForStatement(endNode, breakTarget, continueTarget, loopHeads);
      }
      return endNode;
    }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      foreach (var statement in statements) {
        statement.GenerateNextRoutines(prog, symbols, methodInfo);
      }
    }
  }

  public class ArmadaIfStatement : ArmadaStatement
  {
    private IfStmt stmt;
    private ArmadaStatement thenClause;
    private ArmadaStatement elseClause;
    private NextRoutine elseNextRoutine;
    private NextRoutine jumpPastElseNextRoutine;

    public ArmadaIfStatement(ParseContext context, IfStmt i_stmt)
      : base(context)
    {
      stmt = i_stmt;
      thenClause = ParseStatement(context, stmt.Thn);
      elseClause = ParseStatement(context, stmt.Els);
      elseNextRoutine = null;
      jumpPastElseNextRoutine = null;
    }

    public override Statement Stmt { get { return stmt; } }

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

    public override ArmadaPC AssignPCs(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo, ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      var thenPC = methodInfo.GenerateOnePC();
      var thenEndPC = thenClause.AssignPCs(prog, symbols, methodInfo, thenPC);
      Debug.Assert(thenEndPC == thenClause.EndPC);

      if (elseClause == null) {
        endPC = thenEndPC;
      }
      else {
        var elsePC = methodInfo.GenerateOnePC();
        endPC = elseClause.AssignPCs(prog, symbols, methodInfo, elsePC);
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

    public override PCNode GeneratePCStructureForStatement(PCNode endNode, PCNode breakTarget, PCNode continueTarget,
                                                           HashSet<ArmadaPC> loopHeads)
    {
      if (elseClause == null)
      {
        var thenStartNode = thenClause.GeneratePCStructureForStatement(endNode, breakTarget, continueTarget, loopHeads);
        return new IfPCNode(startPC, nextRoutine, elseNextRoutine, thenStartNode, endNode);
      }
      else
      {
        var jumpPastElseNode = new NormalPCNode(thenClause.EndPC, jumpPastElseNextRoutine, endNode);
        var thenStartNode = thenClause.GeneratePCStructureForStatement(jumpPastElseNode, breakTarget, continueTarget, loopHeads);
        var elseStartNode = elseClause.GeneratePCStructureForStatement(endNode, breakTarget, continueTarget, loopHeads);
        return new IfPCNode(startPC, nextRoutine, elseNextRoutine, thenStartNode, elseStartNode);
      }
    }

    public override void AssociateLabelWithStatement(ArmadaSymbolTable symbols, string lbl)
    {
      base.AssociateLabelWithStatement(symbols, lbl);
      if (elseClause != null) {
        symbols.AssociateLabelWithPC($"JumpPastElse_{lbl}", thenClause.EndPC);
      }
    }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      //
      // First, we generate the next routine for evaluating the guard at
      // startPC and going to either thenClause.StartPC or (elseClause.StartPC or thenClause.EndPC),
      // or failing because the guard evaluation crashes.
      //

      var elsePC = stmt.Els != null ? elseClause.StartPC : thenClause.EndPC;
      var nextThen = new NextRoutine(prog, symbols, NextType.IfTrue, methodInfo, this, stmt, startPC, thenClause.StartPC);
      var nextElse = new NextRoutine(prog, symbols, NextType.IfFalse, methodInfo, this, stmt, startPC, elsePC);
      this.nextRoutine = nextThen;
      this.elseNextRoutine = nextElse;

      var contextThen = new NormalResolutionContext(nextThen, symbols);
      var contextElse = new NormalResolutionContext(nextElse, symbols);

      if (stmt.Guard != null) { // A null guard means a non-deterministic choice, i.e., *
        var guardRValue = contextThen.ResolveAsRValue(stmt.Guard);
        if (guardRValue.CanCauseUndefinedBehavior) {
          nextThen.AddUndefinedBehaviorAvoidanceConstraint(guardRValue.UndefinedBehaviorAvoidance);
          nextThen.AddConjunct(AH.MakeImpliesExpr(guardRValue.UndefinedBehaviorAvoidance.Expr, guardRValue.Val));
        }
        else {
          nextThen.AddConjunct(guardRValue.Val);
        }

        guardRValue = contextElse.ResolveAsRValue(stmt.Guard);
        if (guardRValue.CanCauseUndefinedBehavior) {
          nextElse.AddUndefinedBehaviorAvoidanceConstraint(guardRValue.UndefinedBehaviorAvoidance);
          nextElse.AddConjunct(AH.MakeImpliesExpr(guardRValue.UndefinedBehaviorAvoidance.Expr, AH.MakeNotExpr(guardRValue.Val)));
        }
        else {
          nextElse.AddConjunct(AH.MakeNotExpr(guardRValue.Val));
        }
      }

      // s' == Armada_UpdatePC(s, tid, {then/else PC})

      var s_then = UpdatePC(symbols, methodInfo, nextThen.s, nextThen.tid, thenClause.StartPC);
      nextThen.SetNextState(s_then);

      var s_else = UpdatePC(symbols, methodInfo, nextElse.s, nextElse.tid, elsePC);
      nextElse.SetNextState(s_else);

      symbols.AddNextRoutine(nextThen);
      symbols.AddNextRoutine(nextElse);

      //
      // Second, we generate the next routines for the then clause.
      //

      thenClause.GenerateNextRoutines(prog, symbols, methodInfo);

      if (elseClause != null) {

        //
        // Third, if there's an else clause, we generate the next
        // routine for jumping from thenClause.EndPC directly and
        // unconditionally to endPC.
        //

        var next = new NextRoutine(prog, symbols, NextType.JumpPastElse, methodInfo, this, stmt, thenClause.EndPC, endPC);
        this.jumpPastElseNextRoutine = next;
        var s_prime = UpdatePC(symbols, methodInfo, next.s, next.tid, endPC);
        next.SetNextState(s_prime);
        symbols.AddNextRoutine(next);

        //
        // Fourth, if there's an else clause, we generate the next routines for that clause
        //

        elseClause.GenerateNextRoutines(prog, symbols, methodInfo);
      }
    }
  }

  public class ArmadaWhileStatement : ArmadaStatement
  {
    private WhileStmt stmt;
    private ArmadaStatement body;
    private NextRoutine guardFalseNextRoutine;
    private NextRoutine jumpBackNextRoutine;

    public ArmadaWhileStatement(ParseContext context, WhileStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
      context = context.Clone();
      context.innermostEnclosingWhile = this;
      body = ParseStatement(context, stmt.Body);
      jumpBackNextRoutine = null;
    }

    public override Statement Stmt { get { return stmt; } }

    public override IEnumerator<ArmadaStatement> GetEnumerator()
    {
      yield return this;
      foreach (var statement in body) {
        yield return statement;
      }
    }

    public override ArmadaPC AssignPCs(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo, ArmadaPC i_startPC)
    {
      startPC = i_startPC;
      var loopHeadPC = methodInfo.GenerateOnePC();
      var loopEndPC = body.AssignPCs(prog, symbols, methodInfo, loopHeadPC);
      endPC = methodInfo.GenerateOnePC();
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

    public override PCNode GeneratePCStructureForStatement(PCNode endNode, PCNode breakTarget, PCNode continueTarget,
                                                           HashSet<ArmadaPC> loopHeads)
    {
      var loopRestartNode = new LoopRestartPCNode(startPC);
      var jumpBackNode = new NormalPCNode(body.EndPC, jumpBackNextRoutine, loopRestartNode);

      //
      // Inside the body of the loop, reaching the end is followed by the jump-back statement, so
      // we pass jumpBackNode as endNode.
      //
      // Inside the body of the loop, executing a break statement jumps to the successor of the
      // while loop, so we pass our endNode as breakTarget.
      //
      // Inside the body of the loop, executing a continue statement restarts the loop, so we pass
      // loopRestartNode as continueTarget.
      //

      var bodyStartNode = body.GeneratePCStructureForStatement(jumpBackNode, endNode, loopRestartNode, loopHeads);
      var whileNode = new WhilePCNode(startPC, nextRoutine, guardFalseNextRoutine, bodyStartNode, endNode);
      loopHeads.Add(startPC);
      return whileNode;
    }

    public override void AssociateLabelWithStatement(ArmadaSymbolTable symbols, string lbl)
    {
      base.AssociateLabelWithStatement(symbols, lbl);
      symbols.AssociateLabelWithPC($"JumpBack_{lbl}", body.EndPC);
    }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      // First, make a next routine for conditionally jumping from the statement beginning to either the loop head or the statement end.

      var nextTrue = new NextRoutine(prog, symbols, NextType.WhileTrue, methodInfo, this, stmt, startPC, body.StartPC);
      this.nextRoutine = nextTrue;
      var nextFalse = new NextRoutine(prog, symbols, NextType.WhileFalse, methodInfo, this, stmt, startPC, endPC);
      this.guardFalseNextRoutine = nextFalse;

      var contextTrue = new NormalResolutionContext(nextTrue, symbols);
      var contextFalse = new NormalResolutionContext(nextFalse, symbols);

      if (stmt.Guard != null) { // A null guard means a non-deterministic choice, i.e., *
        var guardRValue = contextTrue.ResolveAsRValue(stmt.Guard);
        if (guardRValue.CanCauseUndefinedBehavior) {
          nextTrue.AddUndefinedBehaviorAvoidanceConstraint(guardRValue.UndefinedBehaviorAvoidance);
          nextTrue.AddConjunct(AH.MakeImpliesExpr(guardRValue.UndefinedBehaviorAvoidance.Expr, guardRValue.Val));
        }
        else {
          nextTrue.AddConjunct(guardRValue.Val);
        }

        guardRValue = contextFalse.ResolveAsRValue(stmt.Guard);
        if (guardRValue.CanCauseUndefinedBehavior) {
          nextFalse.AddUndefinedBehaviorAvoidanceConstraint(guardRValue.UndefinedBehaviorAvoidance);
          nextFalse.AddConjunct(AH.MakeImpliesExpr(guardRValue.UndefinedBehaviorAvoidance.Expr, AH.MakeNotExpr(guardRValue.Val)));
        }
        else {
          nextFalse.AddConjunct(AH.MakeNotExpr(guardRValue.Val));
        }
      }

      // s' == Armada_UpdatePC(s, tid, {head/end PC})

      var s_true = UpdatePC(symbols, methodInfo, nextTrue.s, nextTrue.tid, body.StartPC);
      nextTrue.SetNextState(s_true);
      var s_false = UpdatePC(symbols, methodInfo, nextFalse.s, nextFalse.tid, endPC);
      nextFalse.SetNextState(s_false);

      symbols.AddNextRoutine(nextTrue);
      symbols.AddNextRoutine(nextFalse);

      // Second, make next routines for the body

      body.GenerateNextRoutines(prog, symbols, methodInfo);

      // Third, make a next routine for unconditionally jumping from the loop end to the statement beginning.

      var next = new NextRoutine(prog, symbols, NextType.WhileEnd, methodInfo, this, stmt, body.EndPC, startPC);
      this.jumpBackNextRoutine = next;
      var s_with_new_PC = UpdatePC(symbols, methodInfo, next.s, next.tid, startPC);
      next.SetNextState(s_with_new_PC);
      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaCallStatement : ArmadaStatement
  {
    private UpdateStmt stmt;
    private string calleeName;
    private NextRoutine returnToNextRoutine;

    public ArmadaCallStatement(ParseContext context, UpdateStmt i_stmt, string i_calleeName) : base(context)
    {
      stmt = i_stmt;
      calleeName = i_calleeName;
      returnToNextRoutine = null;
    }

    public override Statement Stmt { get { return stmt; } }

    public string CalleeName { get {return calleeName; } }

    private void GenerateCallNextRoutine(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      //
      // The first next routine for a call statement is the one for the call itself.
      //

      var next = new NextRoutine(prog, symbols, NextType.Call, methodInfo, this, stmt, startPC, new ArmadaPC(symbols, calleeName, 0));
      this.nextRoutine = next;
      var context = new NormalResolutionContext(next, symbols);
      var ex = (ExprRhs)stmt.Rhss[0];
      var suffix = (ApplySuffix)ex.Expr;

      int numArgsExpected = symbols.GetNumInputVariables(calleeName);
      if (numArgsExpected != suffix.Args.Count) {
        next.Fail(stmt.Tok, $"Incorrect number of arguments to {calleeName} ({suffix.Args.Count} instead of {numArgsExpected})");
        return;
      }
      int numReturnValuesExpected = symbols.GetNumOutputVariables(calleeName);
      if (numReturnValuesExpected != stmt.Lhss.Count) {
        next.Fail(stmt.Tok, $"Incorrect number of return values assigned from {calleeName} ({stmt.Lhss.Count} instead of {numReturnValuesExpected}");
        return;
      }

      // Set up the new stack frame

      Expression s_current = next.s, new_frame, new_ptrs;
      GetStackFrameForCallOrCreateThread(prog, symbols, next, context, calleeName, suffix.Args, ref s_current, out new_frame, out new_ptrs);

      // s_current.(threads := s.threads[tid := Armada_Thread(Armada_PC_{callee}'0, new_frame, new_ptrs,
      //                                                      [Armada_ExtendedFrame(returnPC, t.top)] + t.stack, t.storeBuffer)])

      var old_top = AH.MakeExprDotName(next.t, "top", "Armada_StackFrame");
      var old_new_ptrs = AH.MakeExprDotName(next.t, "new_ptrs", AH.MakePointerSetType());
      var return_pc = AH.MakeNameSegment(endPC.ToString(), "Armada_PC");
      var new_extended_frame = AH.MakeApply3("Armada_ExtendedFrame", return_pc, old_top, old_new_ptrs, "Armada_ExtendedFrame");
      var new_extended_frame_as_list = AH.MakeSeqDisplayExpr(new List<Expression>{ new_extended_frame });
      var old_stack = AH.MakeExprDotName(next.t, "stack", AH.MakeStackType());
      var new_stack = AH.MakeAddExpr(new_extended_frame_as_list, old_stack);
      var old_store_buffer = AH.MakeExprDotName(next.t, "storeBuffer", AH.MakeStoreBufferType());
      var callee_pc = AH.MakeNameSegment(new ArmadaPC(symbols, calleeName, 0).ToString(), "Armada_PC");
      var new_thread = AH.MakeApply5("Armada_Thread", callee_pc, new_frame, new_ptrs, new_stack, old_store_buffer, "Armada_Thread");
      var old_threads = AH.MakeExprDotName(next.s, "threads", AH.MakeThreadsType());
      var new_threads = AH.MakeSeqUpdateExpr(old_threads, next.tid, new_thread);
      s_current = AH.MakeDatatypeUpdateExpr(s_current, "threads", new_threads);
      s_current = next.AddVariableDeclaration("s", s_current);

      PerformStackFrameInitializations(symbols, next, calleeName, next.tid, ref s_current);

      next.SetNextState(s_current);

      symbols.AddNextRoutine(next);
    }

    private void GenerateReturnNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      //
      // The second type of next routine for a call statement is the one for the return from the call,
      // including assignment of returned values.  We have to make one of these for each return PC in
      // the called method.
      //

      var method = methodInfo.method;
      var calleeMethodInfo = symbols.AllMethods.LookupMethod(calleeName);

      foreach (var returnPC in calleeMethodInfo.ReturnPCs) {
        var next = new NextRoutine(prog, symbols, NextType.Return, calleeMethodInfo, this, stmt, returnPC, endPC);
        this.returnToNextRoutine = next;

        // |t.stack| > 0
        var old_stack = AH.MakeExprDotName(next.t, "stack", AH.MakeStackType());
        var old_stack_size = AH.MakeCardinalityExpr(old_stack);
        var old_stack_size_positive = AH.MakeGtExpr(old_stack_size, AH.MakeZero());
        next.AddConjunct(old_stack_size_positive);

        // t.stack[0].return_pc == {end PC}
        var next_extended_frame = AH.MakeSeqSelectExpr(old_stack, AH.MakeZero(), "Armada_ExtendedFrame");
        var return_pc = AH.MakeExprDotName(next_extended_frame, "return_pc", "Armada_PC");
        var end_pc = AH.MakeNameSegment(endPC.ToString(), "Armada_PC");
        var returning_here = AH.MakeEqExpr(return_pc, end_pc);
        next.AddConjunct(returning_here);

        // t.stack[0].frame.Armada_StackFrame_{method.Name}?
        var next_stack_frame = AH.MakeExprDotName(next_extended_frame, "frame", "Armada_StackFrame");
        var next_stack_frame_correct = AH.MakeExprDotName(next_stack_frame, $"Armada_StackFrame_{method.Name}?", new BoolType());
        next.AddConjunct(next_stack_frame_correct);

        // var s_current := s.(threads := s.threads[tid := Armada_Thread({return PC}, next_stack_frame, t.stack[0].new_ptrs,
        //                                                               t.stack[1..], t.storeBuffer)])

        var popped_stack = AH.MakeSeqSliceExpr(old_stack, AH.MakeOne(), null);
        var popped_new_ptrs = AH.MakeExprDotName(next_extended_frame, "new_ptrs", AH.MakePointerSetType());
        var store_buffer = AH.MakeExprDotName(next.t, "storeBuffer", AH.MakeStoreBufferType());
        var updated_thread = AH.MakeApply5("Armada_Thread", end_pc, next_stack_frame, popped_new_ptrs, popped_stack,
                                           store_buffer, "Armada_Thread");
        var threads = AH.MakeExprDotName(next.s, "threads", AH.MakeThreadsType());
        var updated_threads = AH.MakeSeqUpdateExpr(threads, next.tid, updated_thread);
        var s_current = AH.MakeDatatypeUpdateExpr(next.s, "threads", updated_threads);
        s_current = next.AddVariableDeclaration("s", s_current);

        // Now, we need to free the new_ptrs.  In Dafny, if we denote s_current by s, that's:
        //
        // s := s.(mem := s.mem.(heap := s.mem.heap.(valid := s.mem.heap.valid - t.new_ptrs,
        //                                           freed := s.mem.heap.freed + t.new_ptrs))))

        var mem = AH.MakeExprDotName(s_current, "mem", "Armada_SharedMemory");
        var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
        var valid = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
        var freed = AH.MakeExprDotName(h, "freed", AH.MakePointerSetType());
        var new_ptrs = AH.MakeExprDotName(next.t, "new_ptrs", AH.MakePointerSetType());
        var valid_new = AH.MakeSubExpr(valid, new_ptrs);
        var freed_new = AH.MakeAddExpr(freed, new_ptrs);
        var h_new = AH.MakeDatatypeUpdate2Expr(h, "valid", valid_new, "freed", freed_new);
        var mem_new = AH.MakeDatatypeUpdateExpr(mem, "heap", h_new);
        s_current = AH.MakeDatatypeUpdateExpr(s_current, "mem", mem_new);
        s_current = next.AddVariableDeclaration("s", s_current);

        // We need a context to compute the values of returned values, a callee_context.

        var callee_context = new NormalResolutionContext(next, symbols);

        // When computing caller contexts (for use in computing lvalues to use for storing return values), we'll need to
        // know the state of various objects as they appear right after popping the stack frame.  So, compute those now.

        var state_after_pop = s_current;
        var ghosts_after_pop = AH.MakeExprDotName(s_current, "ghosts", AH.MakeGhostsType());
        var threads_after_pop = AH.MakeExprDotName(s_current, "threads", AH.MakeThreadsType());
        var thread_after_pop = AH.MakeSeqSelectExpr(threads_after_pop, next.tid, "Armada_Thread");
        var top_after_pop = AH.MakeExprDotName(thread_after_pop, "top", "Armada_StackFrame");

        int numReturnValuesExpected = symbols.GetNumOutputVariables(calleeName);
        for (int i = 0; i < numReturnValuesExpected; ++i) {
          // We need a context for the caller to use when computing lvalues to use for storing return
          // values into local variables.  The hard part of this is computing the local view of the
          // state.  A shortcut to this is to observe that the local view of the state doesn't change
          // due to a pop, so we can just use next.locv.

          var caller_context = new CustomResolutionContext(s_current, state_after_pop, next.locv, top_after_pop,
                                                           ghosts_after_pop, next.tid, method.Name, symbols, next);

          var av = symbols.GetOutputVariableByIndex(calleeName, i);
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
            newLhs.UpdateTotalStateWithStoreBufferEntry(caller_context, next, rhs.Val);
          s_current = next.AddVariableDeclaration("s", s_current);
        }

        next.SetNextState(s_current);
        symbols.AddNextRoutine(next);
      }
    }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      GenerateCallNextRoutine(prog, symbols, methodInfo);
      GenerateReturnNextRoutines(prog, symbols, methodInfo);
    }
  }

  public class ArmadaCreateThreadStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaCreateThreadStatement(ParseContext context, UpdateStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      if (stmt.Lhss.Count > 1) {
        AH.PrintError(prog, stmt.Tok,
                      $"Number of left-hand sides for create_thread must be 0 or 1, since the only thing returned is a thread handle");
        return;
      }

      var rhs = (CreateThreadRhs)stmt.Rhss[0];
      var calleeName = rhs.MethodName.val;

      if (!symbols.DoesMethodNameExist(calleeName)) {
        AH.PrintError(prog, stmt.Tok, $"Call to create_thread on non-existent method {calleeName}");
        return;
      }

      if (calleeName.Equals("main")) {
        AH.PrintError(prog, stmt.Tok, $"It's illegal to create a thread using main as the routine");
        return;
      }

      symbols.UseMethodAsThreadRoutine(calleeName);

      int numInputs = symbols.GetNumInputVariables(calleeName);
      if (numInputs != rhs.Args.Count) {
        AH.PrintError(prog, stmt.Tok,
                      $"Call to create_thread has {rhs.Args.Count} input variables but {calleeName} takes {numInputs} input parameters");
        return;
      }

      var next = new NextRoutine(prog, symbols, NextType.CreateThread, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;
      var context = new NormalResolutionContext(next, symbols);

      next.AddFormal(new NextFormal($"newtid_{startPC}", "newtid", "Armada_ThreadHandle"));
      var new_tid = AH.MakeNameSegment("newtid", "Armada_ThreadHandle");

      // new_tid !in s.threads

      var threads = AH.MakeExprDotName(next.s, "threads", AH.MakeThreadsType());
      var new_tid_not_in_threads = AH.MakeNotInExpr(new_tid, threads);
      next.AddConjunct(new_tid_not_in_threads);

      // new_tid != 0

      var new_tid_nonzero = AH.MakeNeqExpr(new_tid, AH.MakeZero());
      next.AddConjunct(new_tid_nonzero);

      // Set up the new stack frame

      Expression s_current = next.s, new_frame, new_ptrs;
      GetStackFrameForCallOrCreateThread(prog, symbols, next, context, calleeName, rhs.Args, ref s_current, out new_frame, out new_ptrs);

      // s_current := s_current.(threads := s.threads[new_tid := Armada_Thread(Armada_PC_{calleeName}'0, new_frame,
      //                                                                       new_ptrs, [], [])])

      var new_stack = AH.MakeEmptySeqDisplayExpr("Armada_ExtendedStackFrame");
      var callee_pc = AH.MakeNameSegment(new ArmadaPC(symbols, calleeName, 0).ToString(), "Armada_PC");
      var new_store_buffer = AH.MakeEmptySeqDisplayExpr("Armada_StoreBufferEntry");
      var new_thread = AH.MakeApply5("Armada_Thread", callee_pc, new_frame, new_ptrs, new_stack, new_store_buffer, "Armada_Thread");
      var old_threads = AH.MakeExprDotName(next.s, "threads", AH.MakeThreadsType());
      var new_threads = AH.MakeSeqUpdateExpr(old_threads, new_tid, new_thread);
      s_current = AH.MakeDatatypeUpdateExpr(s_current, "threads", new_threads);
      s_current = next.AddVariableDeclaration("s", s_current);

      PerformStackFrameInitializations(symbols, next, calleeName, new_tid, ref s_current);

      // s_current := Armada_UpdatePC(s_current, next.tid, endPC);

      s_current = UpdatePC(symbols, methodInfo, s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // If there's a return value, set it to new_tid

      if (stmt.Lhss.Count > 0) {
        var current_context = new NormalResolutionContext(s_current, next, symbols);
        var lhs = stmt.Lhss[0];
        var newLhs = current_context.ResolveAsLValue(lhs);
        if (!(newLhs is ArmadaLValue)) {
          next.Fail(lhs.tok, "Where to store the returned thread handle from create_thread is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        // var s_current := lhs.update_state(s_current, new_tid);
        s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, new_tid)
                                            : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, new_tid);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      next.SetNextState(s_current);

      // We're done creating the next routine, so add it to the list

      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaMallocStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaMallocStatement(ParseContext context, UpdateStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      if (stmt.Lhss.Count != 1) {
        AH.PrintError(prog, stmt.Tok, $"Number of left-hand sides for malloc must be 1");
        return;
      }

      var lhs = stmt.Lhss[0];
      if (!(lhs.Type is PointerType)) {
        AH.PrintError(prog, stmt.Tok, $"Result of malloc must be stored in a ptr");
        return;
      }

      var rhs = (MallocRhs)stmt.Rhss[0];
      var lhsPointerType = (PointerType)lhs.Type;
      if (!lhsPointerType.Arg.Equals(rhs.AllocatedType)) {
        AH.PrintError(prog, stmt.Tok, $"Result of malloc must be stored in a ptr<{rhs.AllocatedType}>");
        return;
      }

      var next = new NextRoutine(prog, symbols, NextType.Malloc, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;
      var context = new NormalResolutionContext(next, symbols);

      var mem = AH.MakeExprDotName(next.s, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");

      next.AddFormal(new NextFormal($"new_ptr_{startPC}", "new_ptr", "Armada_Pointer"));
      var new_ptr = AH.MakeNameSegment("new_ptr", "Armada_Pointer");

      next.AddFormal(new NextFormal($"new_ptrs_{startPC}", "new_ptrs", AH.MakePointerSetType()));
      var new_ptrs = AH.MakeNameSegment("new_ptrs", AH.MakePointerSetType());

      // if new_ptr == 0 (malloc fails) then
      //    |new_ptrs| == 0
      // else
      //     new_ptr is among new_ptrs
      //     new_ptrs == Armada_Allocator_{ty}(new_ptr)
      //     new_ptr is in s.mem.heap.tree
      //     new_ptr is a root in s.mem.heap, i.e., s.mem.heap.tree[new_ptr].field_of_parent.Armada_FieldNone?
      //     new_ptr is a dynamic-heap root, i.e., s.mem.heap.tree[new_ptr].field_of_parent.rt.Armada_RootTypeDynamicHeap?
      //     The new_ptrs don't overlap the previous valid pointers, i.e., new_ptrs !! s.mem.heap.valid
      //     Nothing that was freed has become valid, i.e., new_ptrs !! s.mem.heap.freed

      var new_ptr_in_new_ptrs = AH.MakeInExpr(new_ptr, new_ptrs);
      var new_ptr_is_valid_ptr = AH.GetInvocationOfValidPointer(h, new_ptr, rhs.AllocatedType);

      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
      var new_ptr_in_tree = AH.MakeInExpr(new_ptr, tree);

      var node = AH.MakeSeqSelectExpr(tree, new_ptr, "Armada_Node");
      var field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
      var new_ptr_is_root = AH.MakeExprDotName(field_of_parent, "Armada_FieldNone?", new BoolType());
      var root_type = AH.MakeExprDotName(field_of_parent, "rt", "Armada_RootType");
      var root_type_dynamic_heap = AH.MakeExprDotName(root_type, "Armada_RootTypeDynamicHeap?", new BoolType());

      var valid = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
      var valid_new_ptrs_disjoint = AH.MakeDisjointExpr(new_ptrs, valid);

      var freed = AH.MakeExprDotName(h, "freed", AH.MakePointerSetType());
      var valid_freed_disjoint = AH.MakeDisjointExpr(new_ptrs, freed);

      var malloc_fails = AH.MakeEqExpr(new_ptr, AH.MakeZero());
      var new_ptrs_empty = AH.MakeEqExpr(AH.MakeCardinalityExpr(new_ptrs), AH.MakeZero());
      var implications_of_malloc_success =
        new List<Expression>{ new_ptr_in_new_ptrs, new_ptr_in_tree, new_ptr_is_root, root_type_dynamic_heap,
                              valid_new_ptrs_disjoint, valid_freed_disjoint };
      next.AddConjunct(AH.MakeIfExpr(malloc_fails, new_ptrs_empty, AH.CombineExpressionsWithAnd(implications_of_malloc_success)));

      // s_current := s.(mem := s.mem.(heap := s.mem.heap.(valid := s.mem.heap.valid + new_ptrs)))

      var valid_plus_new = AH.MakeAddExpr(valid, new_ptrs);
      var h_updated = AH.MakeDatatypeUpdateExpr(h, "valid", valid_plus_new);
      var mem_updated = AH.MakeDatatypeUpdateExpr(mem, "heap", h_updated);
      var s_current = AH.MakeDatatypeUpdateExpr(next.s, "mem", mem_updated);
      s_current = next.AddVariableDeclaration("s", s_current);

      // if new_ptr != 0, then new_ptr is a valid pointer in s_current.mem.heap

      var mem_current = AH.MakeExprDotName(s_current, "mem", "Armada_SharedMemory");
      var h_current = AH.MakeExprDotName(mem_current, "heap", "Armada_Heap");
      var pointer_valid = AH.GetInvocationOfValidPointer(h_current, new_ptr, rhs.AllocatedType);
      var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
        AH.MakeNameSegment("s2.mem.heap", "Armada_Heap"),
        AH.MakeNameSegment("new_ptr", "Armada_Pointer"),
        rhs.AllocatedType
      );
      var new_ptrs_equals_allocator_result = AH.ParseExpression(prog, "MallocNewPtrsEqualsAllocated", $"(forall x :: x in new_ptrs <==> x in {Printer.ExprToString(allocatedByExpr)})");

      var malloc_succeeds = AH.MakeNeqExpr(new_ptr, AH.MakeZero());
      next.AddConjunct(AH.MakeImpliesExpr(malloc_succeeds, AH.MakeAndExpr(pointer_valid, new_ptrs_equals_allocator_result)));

      // s_current := lhs.update_state(s_current, new_ptr);

      var current_context = new NormalResolutionContext(s_current, next, symbols);
      var newLhs = current_context.ResolveAsLValue(lhs);
      if (!(newLhs is ArmadaLValue)) {
        next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
        return;
      }
      next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

      s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, new_ptr)
                                          : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, new_ptr);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(symbols, methodInfo, s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaCallocStatement : ArmadaStatement
  {
    private UpdateStmt stmt;

    public ArmadaCallocStatement(ParseContext context, UpdateStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      if (stmt.Lhss.Count != 1) {
        AH.PrintError(prog, stmt.Tok, $"Number of left-hand sides for calloc must be 1");
        return;
      }

      var lhs = stmt.Lhss[0];
      if (!(lhs.Type is PointerType)) {
        AH.PrintError(prog, stmt.Tok, $"Result of calloc must be stored in a ptr");
        return;
      }

      var rhs = (CallocRhs)stmt.Rhss[0];
      var lhsPointerType = (PointerType)lhs.Type;
      if (!lhsPointerType.Arg.Equals(rhs.AllocatedType)) {
        AH.PrintError(prog, stmt.Tok, $"Result of calloc must be stored in a ptr<{rhs.AllocatedType}>");
        return;
      }

      var next = new NextRoutine(prog, symbols, NextType.Calloc, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;
      var context = new NormalResolutionContext(next, symbols);

      var countRValue = context.ResolveAsRValue(rhs.Count);
      next.AddUndefinedBehaviorAvoidanceConstraint(countRValue.UndefinedBehaviorAvoidance);
      var count = AH.MakeConversionExpr(countRValue.Val, new IntType());

      var mem = AH.MakeExprDotName(next.s, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");

      next.AddFormal(new NextFormal($"new_ptr_{startPC}", "new_ptr", "Armada_Pointer"));
      var new_ptr = AH.MakeNameSegment("new_ptr", "Armada_Pointer");

      next.AddFormal(new NextFormal($"new_ptrs_{startPC}", "new_ptrs", AH.MakePointerSetType()));
      var new_ptrs = AH.MakeNameSegment("new_ptrs", AH.MakePointerSetType());

      // if new_ptr == 0 (calloc fails) then
      //     |new_ptrs| == 0
      // else
      //     new_ptr is among new_ptrs
      //     new_ptr is in s.mem.heap.tree
      //     new_ptr is a root in s.mem.heap, i.e., s.mem.heap.tree[new_ptr].field_of_parent.Armada_FieldNone?
      //     new_ptr is a dynamic-heap root, i.e., s.mem.heap.tree[new_ptr].field_of_parent.rt.Armada_RootTypeDynamicHeap?
      //     The new_ptrs don't overlap the previous valid pointers, i.e., new_ptrs !! s.mem.heap.valid
      //     Nothing that was freed has become valid, i.e., new_ptrs !! s.mem.heap.freed

      var new_ptr_in_new_ptrs = AH.MakeInExpr(new_ptr, new_ptrs);

      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
      var new_ptr_in_tree = AH.MakeInExpr(new_ptr, tree);

      var node = AH.MakeSeqSelectExpr(tree, new_ptr, "Armada_Node");
      var field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
      var new_ptr_is_root = AH.MakeExprDotName(field_of_parent, "Armada_FieldNone?", new BoolType());
      var root_type = AH.MakeExprDotName(field_of_parent, "rt", "Armada_RootType");
      var root_type_dynamic_heap = AH.MakeExprDotName(root_type, "Armada_RootTypeDynamicHeap?", new BoolType());

      var valid = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
      var valid_new_ptrs_disjoint = AH.MakeDisjointExpr(new_ptrs, valid);

      var freed = AH.MakeExprDotName(h, "freed", AH.MakePointerSetType());
      var valid_freed_disjoint = AH.MakeDisjointExpr(new_ptrs, freed);

      var calloc_fails = AH.MakeEqExpr(new_ptr, AH.MakeZero());
      var new_ptrs_empty = AH.MakeEqExpr(AH.MakeCardinalityExpr(new_ptrs), AH.MakeZero());
      var implications_of_calloc_success =
        new List<Expression>{ new_ptr_in_new_ptrs, new_ptr_in_tree, new_ptr_is_root, root_type_dynamic_heap,
                              valid_new_ptrs_disjoint, valid_freed_disjoint };
      next.AddConjunct(AH.MakeIfExpr(calloc_fails, new_ptrs_empty, AH.CombineExpressionsWithAnd(implications_of_calloc_success)));

      // We model it as undefined behavior if a non-positive number was passed as the count.
      // The reason we don't allow allocation of a 0-size array is as follows.  What we return
      // is a pointer to the 0th element, and there is no 0th element to return if we allocate
      // an array of size 0.

      var count_positive = AH.MakeGtExpr(count, AH.MakeZero());
      next.AddUndefinedBehaviorAvoidanceConstraint(count_positive);

      // s_current := s.(mem := s.mem.(heap := s.mem.heap.(valid := s.mem.heap.valid + new_ptrs)))

      var valid_plus_new = AH.MakeAddExpr(valid, new_ptrs);
      var h_updated = AH.MakeDatatypeUpdateExpr(h, "valid", valid_plus_new);
      var mem_updated = AH.MakeDatatypeUpdateExpr(mem, "heap", h_updated);
      var s_current = AH.MakeDatatypeUpdateExpr(next.s, "mem", mem_updated);
      s_current = next.AddVariableDeclaration("s", s_current);

      // If new_ptr != 0, then new_ptr is a valid pointer in s_current.mem.heap to a SizedArrayType.
      // This is somewhat tricky because this is part of the validity step, which comes before the
      // crash-evaluation step, but it only makes sense if the evaluation of 'count' doesn't crash.

      var mem_current = AH.MakeExprDotName(s_current, "mem", "Armada_SharedMemory");
      var h_current = AH.MakeExprDotName(mem_current, "heap", "Armada_Heap");
      var pointer_valid = AH.GetInvocationOfValidPointer(h_current, new_ptr, new SizedArrayType(rhs.AllocatedType, count));
      var calloc_succeeds = AH.MakeNeqExpr(new_ptr, AH.MakeZero());
      var calloc_succeeds_and_count_doesnt_crash =
        countRValue.CanCauseUndefinedBehavior ? AH.MakeAndExpr(calloc_succeeds, countRValue.UndefinedBehaviorAvoidance.Expr) : calloc_succeeds;

      var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
        AH.MakeNameSegment("s2.mem.heap", "Armada_Heap"),
        AH.MakeNameSegment("new_ptr", "Armada_Pointer"),
        new SizedArrayType(rhs.AllocatedType, count)
      );
      var new_ptrs_equals_allocator_result = AH.ParseExpression(prog, "CallocNewPtrsEqualsAllocated", $"(forall x :: x in new_ptrs <==> x in {Printer.ExprToString(allocatedByExpr)})");
      var pointer_valid_and_new_ptrs_if_nonzero_and_count_doesnt_crash = AH.MakeImpliesExpr(calloc_succeeds_and_count_doesnt_crash, AH.MakeAndExpr(pointer_valid, new_ptrs_equals_allocator_result));
      next.AddConjunct(pointer_valid_and_new_ptrs_if_nonzero_and_count_doesnt_crash);

      // There's a difference in Armada between a pointer to an array and the pointer to its 0th element.
      // (The former is just a proof construct in the case of a calloc.)  So we need to get a pointer to
      // the 0th element to store in the left-hand side.

      var children = AH.MakeExprDotName(node, "children", AH.MakeChildrenType());
      var zero_index = AH.MakeApply1("Armada_FieldArrayIndex", AH.MakeZero(), "Armada_Field");
      var child = AH.MakeSeqSelectExpr(children, zero_index, "Armada_Pointer");
      var result = AH.MakeIfExpr(calloc_succeeds, child, AH.MakeZero());  // if new_ptr != 0 then child else 0

      // s_current := lhs.update_state(s_current, result);

      var current_context = new NormalResolutionContext(s_current, next, symbols);
      var newLhs = current_context.ResolveAsLValue(lhs);
      if (!(newLhs is ArmadaLValue)) {
        next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
        return;
      }
      next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

      s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, result)
                                          : newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, result);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(symbols, methodInfo, s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaUpdateStatement : ArmadaStatement
  {
    private UpdateStmt stmt;
    private bool genuineTSO;

    public ArmadaUpdateStatement(ParseContext context, UpdateStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
      genuineTSO = ! i_stmt.BypassStoreBuffers;
    }

    public override Statement Stmt { get { return stmt; } }

    public bool GenuineTSO { get { return genuineTSO; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      if (stmt.Lhss.Count != stmt.Rhss.Count) {
        AH.PrintError(prog, stmt.Tok, $"Number of left-hand sides for assignment ({stmt.Lhss.Count}) statement doesn't match number of right-hand sides ({stmt.Rhss.Count}).");
        return;
      }

      var next = new NextRoutine(prog, symbols, NextType.Update, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;

      var s_current = next.s;
      for (int i = 0; i < stmt.Lhss.Count; ++i) {
        var context = new NormalResolutionContext(s_current, next, symbols);

        var lhs = stmt.Lhss.ElementAt(i);
        var newLhs = context.ResolveAsLValue(lhs);

        if (newLhs.NoTSO()) {
          genuineTSO = false;
        }

        if (newLhs == null) {
          next.Fail(lhs.tok, "Left-hand side is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        var rhs = stmt.Rhss.ElementAt(i);
        Expression newRhs;
        if (rhs is HavocRhs) {
          next.AddFormal(new NextFormal($"nondet{i}_{startPC}", $"nondet{i}", symbols.FlattenType(lhs.Type)));
          newRhs = AH.MakeNameSegment($"nondet{i}", lhs.Type);
        }
        else if (rhs is ExprRhs) {
          var erhs = (ExprRhs)rhs;
          var newRhsRValue = context.ResolveAsRValue(erhs.Expr);
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
        else {
          next.Fail(rhs.Tok, "Right-hand side is not a valid rvalue");
          return;
        }

        // var s_current := lhs.update_state(s_current, rhs);
        s_current = stmt.BypassStoreBuffers ? newLhs.UpdateTotalStateBypassingStoreBuffer(context, next, newRhs)
                                            : newLhs.UpdateTotalStateWithStoreBufferEntry(context, next, newRhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      var nextState = UpdatePC(symbols, methodInfo, s_current, next.tid, endPC);
      next.SetNextState(nextState);
      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaVarDeclStatement : ArmadaStatement
  {
    private VarDeclStmt stmt;

    public ArmadaVarDeclStatement(ParseContext context, VarDeclStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override ArmadaPC AssignPCs(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo, ArmadaPC i_startPC)
    {
      if (i_startPC.instructionCount > 0) {
        if (stmt.Update != null) {
          AH.PrintError(prog, stmt.Tok, "In Armada, all stack variables for a method are created and initialized atomically with the stack frame getting pushed onto the stack.  So, it's a bad idea to have a variable declaration with an initialization value, like this one, somewhere other than the beginning of the method.  After all, in this case the semantics will not be what seems intuitive from reading the code.");
        }
        else {
          AH.PrintWarning(prog, stmt.Tok, "Note that, in Armada, all stack variables for a method are created and initialized atomically with the stack frame getting pushed onto the stack.  So, it's generally a good idea to have all variable declarations at the beginnings of methods.  Otherwise, the semantics may not be what seems intuitive from reading the code.");
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
  }

  public class ArmadaReturnStatement : ArmadaStatement
  {
    private ReturnStmt stmt;

    public ArmadaReturnStatement(ParseContext context, ReturnStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
    }
  }

  public class ArmadaAssertStatement : ArmadaStatement
  {
    private AssertStmt stmt;

    public ArmadaAssertStatement(ParseContext context, AssertStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      var next = new NextRoutine(prog, symbols, NextType.Assert, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;
      var context = new NormalResolutionContext(next, symbols);

      // s' == if <expression> then Armada_UpdatePC(s, tid, endPC) else s.(stop_reason := Armada_StopReasonAssertionFailure)

      var rvalue = context.ResolveAsRValue(stmt.Expr);
      next.AddUndefinedBehaviorAvoidanceConstraint(rvalue.UndefinedBehaviorAvoidance);

      var s = next.s;
      var s_with_assertion_failure =
        AH.MakeDatatypeUpdateExpr(s, "stop_reason", AH.MakeNameSegment("Armada_StopReasonAssertionFailure", "Armada_StopReason"));
      var s_with_new_PC = UpdatePC(symbols, methodInfo, next.s, next.tid, endPC);
      var s_updated = AH.MakeIfExpr(rvalue.Val, s_with_new_PC, s_with_assertion_failure);

      next.SetNextState(s_updated);
      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaAssumeStatement : ArmadaStatement
  {
    private AssumeStmt stmt;

    public ArmadaAssumeStatement(ParseContext context, AssumeStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override ArmadaPC AssignPCs(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo, ArmadaPC i_startPC)
    {
      return endPC = startPC = i_startPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
    }

    public void AddEnablingConstraint(ArmadaSymbolTable symbols, MethodInfo methodInfo, EnablingConstraintCollector constraintCollector)
    {
      var context = new CustomResolutionContext(constraintCollector.s, constraintCollector.s, constraintCollector.locv,
                                                constraintCollector.top, constraintCollector.ghosts,
                                                constraintCollector.tid, methodInfo.method.Name, symbols, constraintCollector);
      var rvalue = context.ResolveAsRValue(stmt.Expr);
      constraintCollector.AddConjunct(rvalue.UndefinedBehaviorAvoidance);
      constraintCollector.AddConjunct(rvalue.Val);
    }
  }

  public class ArmadaSomehowStatement : ArmadaStatement
  {
    private SomehowStmt stmt;

    public ArmadaSomehowStatement(ParseContext context, SomehowStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      var next = new NextRoutine(prog, symbols, NextType.Somehow, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;
      var method = methodInfo.method;

      var top = AH.MakeExprDotName(next.t, "top", "Armada_StackFrame");
      var ghosts = AH.MakeExprDotName(next.s, "ghosts", "Armada_Ghosts");
      var start_read_context = new CustomResolutionContext(next.s, next.s, next.locv, top,
                                                           ghosts, next.tid, method.Name, symbols, next);

      // Add each requires clause as an undefined-behavior-avoidance constraint, to model that the
      // instruction may have arbitrary behavior if its requirements aren't met at the outset.

      foreach (var requires_clause in stmt.Req) {
        var r = start_read_context.ResolveAsRValue(requires_clause);
        next.AddUndefinedBehaviorAvoidanceConstraint(r.UndefinedBehaviorAvoidance);
        next.AddUndefinedBehaviorAvoidanceConstraint(r.Val);
      }

      // Add each awaits clause as a predicate.

      foreach (var await_clause in stmt.Awaits) {
        if (!(await_clause.Type is BoolType)) {
          next.Fail(await_clause.tok, "Awaits clauses have to be boolean expressions");
          return;
        }
        var await_clause_resolved = start_read_context.ResolveAsRValue(await_clause);
        next.AddConjunct(await_clause_resolved.UndefinedBehaviorAvoidance);
        next.AddConjunct(await_clause_resolved.Val);
      }

      // Compute each s{i+1} by updating a single modifies element in s{i}.

      var s_current = next.s;
      for (int i = 0; i < stmt.Mod.Expressions.Count; ++i) {
        var lhs = stmt.Mod.Expressions.ElementAt(i);

        var nextFormal = new NextFormal($"newval{i}_{startPC}", $"newval{i}", lhs.Type);
        next.AddFormal(nextFormal);
        var newRhs = AH.MakeNameSegment($"newval{i}", lhs.Type);

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
        var current_context = new NormalResolutionContext(s_current, next, symbols);
        var newLhs = current_context.ResolveAsLValue(lhs);
        if (!(newLhs is ArmadaLValue)) {
          next.Fail(lhs.tok, "Modifies element is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        s_current = Attributes.Contains(stmt.Mod.Attributes, "tso") ?
          newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, newRhs) :
          newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, newRhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      // s_current := Armada_UpdatePC(s_current, tid, endPC);

      s_current = UpdatePC(symbols, methodInfo, s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s' must be equal to the updated s we just computed

      next.SetNextState(s_current);

      // For each ensures clause, add another condition that the clause holds in s' (as viewed by the local thread).

      if (stmt.Ens.Count > 0) {
        var locv_prime = AH.MakeApply2("Armada_GetThreadLocalView", s_current, next.tid, "Armada_SharedMemory");
        locv_prime = next.AddVariableDeclaration("locv_prime", locv_prime);

        var threads_prime = AH.MakeExprDotName(s_current, "threads", AH.MakeThreadsType());
        var thread_prime = AH.MakeSeqSelectExpr(threads_prime, next.tid, "Armada_Thread");
        var top_prime = AH.MakeExprDotName(thread_prime, "top", "Armada_StackFrame");
        var ghosts_prime = AH.MakeExprDotName(s_current, "ghosts", "Armada_Ghosts");

        // In an ensures clause of a somehow statement, "old" refers to the state before the somehow.
        var old_mem = AH.MakeExprDotName(next.s, "mem", "Armada_SharedMemory");
        var old_ghosts = AH.MakeExprDotName(next.s, "ghosts", "Armada_Ghosts");
        var end_read_context = new EnsuresResolutionContext(next.s, s_current, next.tid, method.Name, symbols, next, null);

        foreach (var ens in stmt.Ens) {
          var ens_resolved = end_read_context.ResolveAsRValue(ens);
          next.AddConjunct(ens_resolved.UndefinedBehaviorAvoidance);
          next.AddConjunct(ens_resolved.Val);
        }
      }

      // We're done building the next routine, so add it to the list of nexts.

      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaDeallocStatement : ArmadaStatement
  {
    private DeallocStmt stmt;

    public ArmadaDeallocStatement(ParseContext context, DeallocStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      var addr = stmt.Addr;
      var next = new NextRoutine(prog, symbols, NextType.Dealloc, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;
      var context = new NormalResolutionContext(next, symbols);

      if (addr.Type == null)
      {
        next.Fail(stmt.Tok, "Attempt to dealloc an address whose type isn't known");
        return;
      }
      Type subtype;
      string err;
      if (!AH.GetDereferenceType(addr.Type, out subtype, out err))
      {
        next.Fail(stmt.Tok, err);
        return;
      }

      var addrRValue = context.ResolveAsRValue(addr);
      next.AddUndefinedBehaviorAvoidanceConstraint(addrRValue.UndefinedBehaviorAvoidance);

      addr = addrRValue.Val;
      AH.SetExprType(addr, "Armada_Pointer");
      addr = next.AddVariableDeclaration("addr", addr);

      var mem = AH.MakeExprDotName(next.s, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");

      // Experience undefined behavior if tree-forest properties don't hold
      var tree_forest_properties = AH.MakeApply1("Armada_TreeForestProperties", tree, new BoolType());
      next.AddUndefinedBehaviorAvoidanceConstraint(tree_forest_properties);

      // Experience undefined behavior if addr isn't valid
      var addr_valid = AH.GetInvocationOfValidPointer(h, addr, subtype);
      next.AddUndefinedBehaviorAvoidanceConstraint(addr_valid);

      //
      // If 'addr' is a pointer to the 0th element of an array, then
      // free its parent pointer instead, i.e., free the pointer to
      // the array.  We can't require the Armada code to pass us that
      // array pointer because there's no way to get that pointer in
      // Armada.  After all, calloc returns a pointer to the 0th element
      // and there's no way to go "up" to the pointer to the array.
      //

      // var addr_to_free := if tree[addr].field_of_parent.Armada_FieldArrayIndex? && tree[addr].field_of_parent.i == 0 then
      //                         tree[addr].parent else addr
      var node = AH.MakeSeqSelectExpr(tree, addr, "Armada_Node");
      var field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
      var is_array_index = AH.MakeExprDotName(field_of_parent, "Armada_FieldArrayIndex?", new BoolType());
      var index_within_parent = AH.MakeExprDotName(field_of_parent, "i", new IntType());
      var index_is_zero = AH.MakeEqExpr(index_within_parent, AH.MakeZero());
      var is_array_index_zero = AH.MakeAndExpr(is_array_index, index_is_zero);
      var use_parent = next.AddVariableDeclaration("use_parent", is_array_index_zero);
      var parent = AH.MakeExprDotName(node, "parent", "Armada_Pointer");
      var addr_to_free = AH.MakeIfExpr(use_parent, parent, addr);
      addr_to_free = next.AddVariableDeclaration("addr_to_free", addr_to_free);

      // Experience undefined behavior if we're using the parent and the parent isn't in the tree
      var parent_in_tree = AH.MakeInExpr(parent, tree);
      next.AddUndefinedBehaviorAvoidanceConstraint(AH.MakeImpliesExpr(use_parent, parent_in_tree));

      // Experience undefined behavior if we're freeing something that isn't a root
      node = AH.MakeSeqSelectExpr(tree, addr_to_free, "Armada_Node");
      field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
      var addr_is_root = AH.MakeExprDotName(field_of_parent, "Armada_FieldNone?", new BoolType());
      next.AddUndefinedBehaviorAvoidanceConstraint(addr_is_root);
      var root_type = AH.MakeExprDotName(field_of_parent, "rt", "Armada_RootType");
      var root_type_dynamic_heap = AH.MakeExprDotName(root_type, "Armada_RootTypeDynamicHeap?", new BoolType());
      next.AddUndefinedBehaviorAvoidanceConstraint(root_type_dynamic_heap);

      // var descendants := set d | d in tree && Armada_PointerIsAncestorOfPointer(tree, addr_to_free, d) :: d;
      var d = AH.MakeNameSegment("d", "Armada_Pointer");
      var d_in_tree = AH.MakeInExpr(d, tree);
      var is_descendant = AH.MakeApply3("Armada_PointerIsAncestorOfPointer", tree, addr_to_free, d, new BoolType());
      var d_in_tree_and_is_descendant = AH.MakeAndExpr(d_in_tree, is_descendant);
      var descendants = AH.MakeSetComprehension(new List<BoundVar>{ AH.MakeBoundVar("d", "Armada_Pointer") },
                                                d_in_tree_and_is_descendant, d);
      AH.SetExprType(descendants, AH.MakePointerSetType());
      descendants = next.AddVariableDeclaration("descendants", descendants);

      // s_current := s.(mem := s.mem.(heap := s.mem.heap.(
      //              valid := s.mem.heap.valid - descendants,
      //              freed := s.mem.heap..freed + descendants)))

      var valid = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
      var valid_minus_descendants = AH.MakeSubExpr(valid, descendants);
      var freed = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
      var freed_plus_decendants = AH.MakeAddExpr(freed, descendants);
      var h_updated = AH.MakeDatatypeUpdate2Expr(h, "valid", valid_minus_descendants, "freed", freed_plus_decendants);
      var mem_updated = AH.MakeDatatypeUpdateExpr(mem, "heap", h_updated);
      var s_current = AH.MakeDatatypeUpdateExpr(next.s, "mem", mem_updated);
      s_current = next.AddVariableDeclaration("s", s_current);

      // s_current := Armada_UpdatePC(s, tid, {end PC})

      s_current = UpdatePC(symbols, methodInfo, s_current, next.tid, endPC);
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);

      // The next predicate is built, so add it to the list of next predicates.

      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaJoinStatement : ArmadaStatement
  {
    private JoinStmt stmt;

    public ArmadaJoinStatement(ParseContext context, JoinStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      var next = new NextRoutine(prog, symbols, NextType.Join, methodInfo, this, stmt, startPC, endPC);
      this.nextRoutine = next;
      var context = new NormalResolutionContext(next, symbols);

      var join_tid = context.ResolveAsRValue(stmt.WhichThread);
      var join_tid_undefined_behavior_avoidance = join_tid.UndefinedBehaviorAvoidance;
      next.AddUndefinedBehaviorAvoidanceConstraint(join_tid_undefined_behavior_avoidance);

      // join_tid !in s.threads

      var threads = AH.MakeExprDotName(next.s, "threads", AH.MakeThreadsType());
      var join_tid_not_in_threads = AH.MakeNotInExpr(join_tid.Val, threads);
      if (join_tid_undefined_behavior_avoidance.CanCauseUndefinedBehavior) {
        next.AddConjunct(AH.MakeImpliesExpr(join_tid_undefined_behavior_avoidance.Expr, join_tid_not_in_threads));
      }
      else {
        next.AddConjunct(join_tid_not_in_threads);
      }

      // s' == Armada_UpdatePC(s, tid, endPC)

      var s_with_new_PC = UpdatePC(symbols, methodInfo, next.s, next.tid, endPC);
      next.SetNextState(s_with_new_PC);
      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaBreakStatement : ArmadaStatement
  {
    private BreakStmt stmt;
    private ArmadaWhileStatement innermostEnclosingWhile;

    public ArmadaBreakStatement(ParseContext context, BreakStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
      innermostEnclosingWhile = context.innermostEnclosingWhile;
    }

    public override Statement Stmt { get { return stmt; } }

    public override PCNode GeneratePCStructureForStatement(PCNode endNode, PCNode breakTarget, PCNode continueTarget,
                                                           HashSet<ArmadaPC> loopHeads)
    {
      return new NormalPCNode(startPC, nextRoutine, breakTarget);
    }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      var next = new NextRoutine(prog, symbols, NextType.WhileBreak, methodInfo, this, stmt, startPC, innermostEnclosingWhile.EndPC);
      this.nextRoutine = next;
      var s_with_new_PC = UpdatePC(symbols, methodInfo, next.s, next.tid, innermostEnclosingWhile.EndPC);
      next.SetNextState(s_with_new_PC);
      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaContinueStatement : ArmadaStatement
  {
    private ContinueStmt stmt;
    private ArmadaWhileStatement innermostEnclosingWhile;

    public ArmadaContinueStatement(ParseContext context, ContinueStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
      innermostEnclosingWhile = context.innermostEnclosingWhile;
    }

    public override Statement Stmt { get { return stmt; } }

    public override PCNode GeneratePCStructureForStatement(PCNode endNode, PCNode breakTarget, PCNode continueTarget,
                                                           HashSet<ArmadaPC> loopHeads)
    {
      return new NormalPCNode(startPC, nextRoutine, continueTarget);
    }

    public override void GenerateNextRoutines(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      var next = new NextRoutine(prog, symbols, NextType.WhileContinue, methodInfo, this, stmt, startPC, innermostEnclosingWhile.StartPC);
      this.nextRoutine = next;
      var s_with_new_PC = UpdatePC(symbols, methodInfo, next.s, next.tid, innermostEnclosingWhile.StartPC);
      next.SetNextState(s_with_new_PC);
      symbols.AddNextRoutine(next);
    }
  }

  public class ArmadaYieldStatement : ArmadaStatement
  {
    private YieldStmt stmt;

    public ArmadaYieldStatement(ParseContext context, YieldStmt i_stmt) : base(context)
    {
      stmt = i_stmt;
    }

    public override Statement Stmt { get { return stmt; } }

    public override ArmadaPC AssignPCs(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo, ArmadaPC i_startPC)
    {
      endPC = startPC = i_startPC;
      return endPC;
    }

    public override void ComputeNonyieldAndYieldPCs(bool inExplicitYieldBlock, HashSet<ArmadaPC> potentiallyNonyieldingPCs,
                                                    HashSet<ArmadaPC> yieldPCs)
    {
      yieldPCs.Add(startPC);
    }
  }
}
