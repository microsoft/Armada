using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using static Microsoft.Armada.Predicate;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  public class EnclosingWhile {
    private List<BreakStmt> breakStatements;
    private List<ContinueStmt> continueStatements;

    public EnclosingWhile()
    {
      breakStatements = new List<BreakStmt>();
      continueStatements = new List<ContinueStmt>();
    }

    public List<BreakStmt> BreakStatements { get { return breakStatements; } }
    public List<ContinueStmt> ContinueStatements { get { return continueStatements; } }
  }

  ////////////////////////////////////////////////////////////////////////////
  /// STATE MACHINE TRANSLATOR
  ////////////////////////////////////////////////////////////////////////////

  public class StateMachineTranslator : IRewriter {

    public Program prog;

    public StateMachineTranslator(Program i_prog)
      : base(i_prog.reporter) {
      Contract.Requires(i_prog.reporter != null);
      prog = i_prog;
    }

    public Expression ParseExpression(string filename, string s) {
      var e = new Errors(new ErrorReporterWrapper(prog.reporter, s));
      return Parser.ParseExpression(s, filename, filename, null, prog.DefaultModule, prog.BuiltIns, e);
    }

    public static string LocalName(string name) {
      return name + "Local";
    }

    public bool CheckForCyclicStructDefinition(ArmadaStruct outer, ArmadaStruct inner, ArmadaStructs structs) {
      foreach (var fieldName in inner.FieldNames) {
        var t = inner.GetFieldType(fieldName);
        if (t is UserDefinedType) {
          var u = (UserDefinedType)t;
          if (u.Name == outer.Name) {
            AH.PrintError(prog, $"Class {outer.Name} has a cyclic dependency on itself, specifically in field {fieldName} of component {inner.Name}");
            return false;
          }
          else if (structs.DoesStructExist(u.Name)) {
            CheckForCyclicStructDefinition(outer, structs.GetStruct(u.Name), structs);
          }
        }
      }
      return true;
    }

    public bool CheckForCyclicStructDefinitions(ArmadaStructs structs) {
      foreach (var structName in structs.StructNames) {
        var s = structs.GetStruct(structName);
        if (!CheckForCyclicStructDefinition(s, s, structs)) {
          return false;
        }
      }
      return true;
    }

    public string GetObjectTypeAsString(ModuleDefinition m, Type t, ArmadaStructs structs)
    {
      t = t.NormalizeExpand(true);
      if (t is UserDefinedType) {
        var ut = (UserDefinedType)t;
        if (structs.DoesStructExist(ut.Name)) {
          return $"Armada_ObjectType_struct(Armada_StructType_{ut.Name})";
        }
        return $"Armada_ObjectType_primitive(Armada_PrimitiveType_{ut.Name})";
      }
      else if (t is SizedArrayType) {
        var ssa = (SizedArrayType)t;
        var subtype = GetObjectTypeAsString(m, ssa.Range, structs);
        var ssaSize = (LiteralExpr)ssa.Size;
        return $"Armada_ObjectType_array({subtype}, {ssaSize.Value})";
      }
      else if (t is PointerType) {
        var ty = AH.GetConcretePointerTypeName();
        return $"Armada_ObjectType_primitive(Armada_PrimitiveType_{ty})";
      }

      return null;
    }

    public void GenerateStructDatatypes(ModuleDefinition m, ArmadaStructs structs, List<TopLevelDecl> newTopLevelDecls,
                                        List<string> structTypes, List<string> structFieldTypes)
    {
      foreach (var structName in structs.StructNames) {
        var s = structs.GetStruct(structName);
        List<Formal> structFields = new List<Formal>();
        foreach (var fieldName in s.FieldNames) {
          var fieldType = s.GetFieldType(fieldName);
          var formal = AH.MakeFormal(fieldName, structs.FlattenType(fieldType));
          structFields.Add(formal);
          structFieldTypes.Add("Armada_FieldType_" + structName + "'" + fieldName);
        }
        var dtName = "Armada_Struct_" + structName;
        var dtDecl = AH.MakeDatatypeDecl(m, dtName, new List<DatatypeCtor> { AH.MakeDatatypeCtor(dtName, structFields) });
        newTopLevelDecls.Add(dtDecl);

        var structType = "Armada_StructType_" + structName;
        structTypes.Add(structType);
      }
    }

    public void RemoveAllMethods(ModuleDefinition m)
    {
      foreach (var d in m.TopLevelDecls) {
        if (d is ClassDecl) {
          var c = (ClassDecl)d;
          var membersToRemove = new List<MemberDecl>();
          foreach (MemberDecl member in c.Members) {
            if (member is Method) {
              if (!c.IsDefaultClass) {
                AH.PrintError(prog, $"Non-default classes aren't permitted to have methods, but class {c.Name} has method {member.Name}");
              }
              membersToRemove.Add(member);
            }
          }
          foreach (var memberToRemove in membersToRemove){
            c.Members.Remove(memberToRemove);
          }
        }
      }
    }

    public void GetMethods(ArmadaSymbolTable symbols, ClassDecl c)
    {
      foreach (MemberDecl member in c.Members) {
        if (member is Method) {
          var method = (Method)member;
          symbols.AllMethods.AddMethod(symbols, method);
        }
      }
    }

    public DatatypeCtor CreateMethodStackFrame(string methodName, ArmadaSymbolTable symbols)
    {
      var smst = symbols.GetMethodSymbolTable(methodName);
      var stackFormals = new List<Formal>();
      foreach (var v in smst.AllVariablesInOrder) {
        stackFormals.Add(AH.MakeFormal($"{methodName}'{v.FieldName}", v.GetFlattenedType(symbols)));
      }

      return AH.MakeDatatypeCtor($"Armada_StackFrame_{methodName}", stackFormals);
    }

    public void ParseMethodWithBody(Program prog, MethodInfo methodInfo, ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      var method = methodInfo.method;

      if (method.Awaits.Count > 0) {
        AH.PrintError(prog, method.tok, "Awaits clauses can't appear except in body-less methods");
        return;
      }

      methodInfo.ParseMethodBody(symbols);
    }

    public void CreateNextRoutinesForMethodWithNoBodyPart1(ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                           List<MemberDecl> newDefaultClassDecls, ArmadaPC startPC, ArmadaPC midPC)
    {
      //
      // The first next routine to generate is...
      //   start->middle:   find that the awaits clauses are satisfied, then havoc the write set, then
      //                    read each element in the read set into Armada_Extern local variables
      //

      var method = methodInfo.method;
      var next = new NextRoutine(prog, symbols, NextType.ExternStart, methodInfo, null, null, startPC, midPC);
      method.externStartNextRoutine = next;
      var read_context = new NormalResolutionContext(next, symbols);
      List<FrameExpression> modifies = method.Mod.Expressions ?? new List<FrameExpression>();
      List<Expression> reads = method.Reads.Expressions ?? new List<Expression>();

      // Add each awaits clause as a predicate.

      foreach (var await_clause in method.Awaits) {
        if (!(await_clause.Type is BoolType)) {
          next.Fail(await_clause.tok, "Awaits clauses have to be boolean expressions");
          return;
        }
        var await_clause_resolved = read_context.ResolveAsRValue(await_clause);
        next.AddConjunct(await_clause_resolved.UndefinedBehaviorAvoidance);
        next.AddConjunct(await_clause_resolved.Val);
      }

      // Add each requires clause as an undefined-behavior constraint, to model that the
      // method's behavior is undefined if its requirements aren't met at the outset.

      foreach (var requires_clause in method.Req) {
        var r = read_context.ResolveAsRValue(requires_clause.E);
        next.AddUndefinedBehaviorAvoidanceConstraint(r.UndefinedBehaviorAvoidance);
        next.AddUndefinedBehaviorAvoidanceConstraint(r.Val);
      }

      // Compute each s{i+1} by updating a single modifies element in s{i}.

      var s_current = next.s;
      for (int i = 0; i < modifies.Count; ++i) {
        var lhs = modifies.ElementAt(i).E;

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

        s_current = Attributes.Contains(method.Mod.Attributes, "tso") ?
          newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, newRhs) :
          newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, newRhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      if (reads.Count > 0) {
        // s_current := Armada_UpdateTSFrame(s_current, tid, s_current.threads[tid].top.(Armada_Extern0 := ..., Armada_Extern1 := ...})

        var locv_current = AH.MakeApply2("Armada_GetThreadLocalView", s_current, next.tid, "Armada_SharedMemory");
        locv_current = next.AddVariableDeclaration("locv", locv_current);
        var ghosts_current = AH.MakeExprDotName(s_current, "ghosts", "Armada_Ghosts");
        // The top stack frame hasn't changed since the beginning, since nothing we modify is on the stack
        var top = read_context.GetRValueTopStackFrame();
        var top_correct_type = AH.MakeExprDotName(top, $"Armada_StackFrame_{method.Name}?", new BoolType());
        next.AddUndefinedBehaviorAvoidanceConstraint(top_correct_type);
        var current_context = new CustomResolutionContext(s_current, s_current, locv_current, top, ghosts_current,
                                                          next.tid, method.Name, symbols, next);
        var updates = new List<Tuple<IToken, string, Expression>>();

        for (int i = 0; i < reads.Count; ++i) {
          var read_expr = reads.ElementAt(i);
          var read_val = current_context.ResolveAsRValue(read_expr);
          next.AddUndefinedBehaviorAvoidanceConstraint(read_val.UndefinedBehaviorAvoidance);
          updates.Add(Tuple.Create(read_expr.tok, $"{method.Name}'Armada_Extern{i}", read_val.Val));
        }

        var top_post_snapshot = AH.SetExprType(new DatatypeUpdateExpr(Token.NoToken, top, updates), "Armada_StackFrame");
        s_current = AH.MakeApply3("Armada_UpdateTSFrame", s_current, next.tid, top_post_snapshot, "Armada_TotalState");
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      // s_current := Armada_UpdatePC(s_current, tid, midPC);

      var newPC = AH.MakeNameSegment(midPC.ToString(), "Armada_PC");
      s_current = AH.MakeApply3("Armada_UpdatePC", s_current, next.tid, newPC, "Armada_TotalState");
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);
      symbols.AddNextRoutine(next);
    }

    public void CreateNextRoutinesForMethodWithNoBodyPart2(ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                           List<MemberDecl> newDefaultClassDecls, ArmadaPC midPC)
    {
      //
      // The second next routine to generate is...
      //   middle->middle:  crash if anything in the read set doesn't match the Armada_Extern variables,
      //                    then havoc the write set, then read each element in the read set into
      //                    Armada_Extern local variables

      var method = methodInfo.method;
      var next = new NextRoutine(prog, symbols, NextType.ExternContinue, methodInfo, null, null, midPC, midPC);
      method.externContinueNextRoutine = next;
      var read_context = new NormalResolutionContext(next, symbols);
      List<FrameExpression> modifies = method.Mod.Expressions ?? new List<FrameExpression>();
      List<Expression> reads = method.Reads.Expressions ?? new List<Expression>();

      // Crash if, for any element in the read set, the current value of that element doesn't
      // match the corresponding element of the latest snapshot.

      var top = AH.MakeExprDotName(next.t, "top", "Armada_StackFrame");
      var top_correct_type = AH.MakeExprDotName(top, $"Armada_StackFrame_{method.Name}?", new BoolType());
      next.AddUndefinedBehaviorAvoidanceConstraint(top_correct_type);

      for (int i = 0; i < reads.Count; ++i) {
        var read_expr = reads.ElementAt(i);
        var current_val = read_context.ResolveAsRValue(read_expr);
        next.AddUndefinedBehaviorAvoidanceConstraint(current_val.UndefinedBehaviorAvoidance);
        var snapshot_val = AH.MakeExprDotName(top, $"{method.Name}'Armada_Extern{i}", read_expr.Type);
        var read_expr_unchanged = AH.MakeEqExpr(current_val.Val, snapshot_val);
        next.AddUndefinedBehaviorAvoidanceConstraint(read_expr_unchanged);
      }

      // Compute each s{i+1} by updating a single modifies element in s{i}.

      var s_current = next.s;
      for (int i = 0; i < modifies.Count; ++i) {
        var lhs = modifies.ElementAt(i).E;

        var nextFormal = new NextFormal($"newval{i}_{midPC}", $"newval{i}", lhs.Type);
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

        s_current = Attributes.Contains(method.Mod.Attributes, "tso") ?
          newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, newRhs) :
          newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, newRhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      if (reads.Count > 0) {
        // s_current := Armada_UpdateTSFrame(s_current, tid, s_current.threads[tid].top.(Armada_Extern0 := ..., Armada_Extern1 := ...})

        var locv_current = AH.MakeApply2("Armada_GetThreadLocalView", s_current, next.tid, "Armada_SharedMemory");
        locv_current = next.AddVariableDeclaration("locv", locv_current);
        var ghosts_current = AH.MakeExprDotName(s_current, "ghosts", "Armada_Ghosts");
        var threads_current = AH.MakeExprDotName(s_current, "threads", AH.MakeThreadsType());
        var thread_current = AH.MakeSeqSelectExpr(threads_current, next.tid, "Armada_Thread");
        var top_current = AH.MakeExprDotName(thread_current, "top", "Armada_StackFrame");
        var current_context = new CustomResolutionContext(s_current, s_current, locv_current, top_current, ghosts_current,
                                                          next.tid, method.Name, symbols, next);
        var updates = new List<Tuple<IToken, string, Expression>>();

        for (int i = 0; i < reads.Count; ++i) {
          var read_expr = reads.ElementAt(i);
          var read_val = current_context.ResolveAsRValue(read_expr);
          next.AddUndefinedBehaviorAvoidanceConstraint(read_val.UndefinedBehaviorAvoidance);
          updates.Add(Tuple.Create(read_expr.tok, $"{method.Name}'Armada_Extern{i}", read_val.Val));
        }

        var top_post_snapshot = AH.SetExprType(new DatatypeUpdateExpr(Token.NoToken, top_current, updates), "Armada_StackFrame");
        s_current = AH.MakeApply3("Armada_UpdateTSFrame", s_current, next.tid, top_post_snapshot, "Armada_TotalState");
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      next.SetNextState(s_current);
      symbols.AddNextRoutine(next);
    }

    public void CreateNextRoutinesForMethodWithNoBodyPart3(ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                           List<MemberDecl> newDefaultClassDecls, ArmadaPC midPC, ArmadaPC endPC)
    {
      //
      // The third next routine to generate is...
      //   middle->end:     find that the post-condition is satisfied and append log elements
      //

      var method = methodInfo.method;
      var next = new NextRoutine(prog, symbols, NextType.ExternEnd, methodInfo, null, null, midPC, endPC);
      method.externEndNextRoutine = next;
      var read_context = new BodylessMethodPostconditionResolutionContext(next, symbols);

      foreach (var ensure_raw in method.Ens) {
        var ensure_resolved = read_context.ResolveAsRValue(ensure_raw.E);
        next.AddConjunct(ensure_resolved.UndefinedBehaviorAvoidance);
        next.AddConjunct(ensure_resolved.Val);
      }

      var s_current = next.s;

      // s_current := Armada_UpdatePC(s_current, tid, endPC);

      var newPC = AH.MakeNameSegment(endPC.ToString(), "Armada_PC");
      s_current = AH.MakeApply3("Armada_UpdatePC", s_current, next.tid, newPC, "Armada_TotalState");
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);
      symbols.AddNextRoutine(next);
    }

    public void ParseMethodWithNoBody(Program prog, MethodInfo methodInfo, ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      var method = methodInfo.method;
      if (!Attributes.Contains(method.Attributes, "extern")) {
        AH.PrintError(prog, method.tok, "Armada doesn't support body-less methods, except external ones marked with {:extern}.");
        return;
      }

      //
      // There are three PCs, at the start, middle, and end of the method.
      // There are three transitions:
      //
      //   start->middle:   find that the awaits clauses are satisfied, then havoc the write set, then
      //                    read each element in the read set into Armada_Extern local variables
      //   middle->middle:  crash if anything in the read set doesn't match the Armada_Extern variables,
      //                    then havoc the write set, then read each element in the read set into
      //                    Armada_Extern local variables
      //   middle->end:     find that the post-condition is satisfied and append log elements
      //

      // Create the three PC values

      var startPC = methodInfo.GenerateOnePC();
      var midPC = methodInfo.GenerateOnePC();
      var endPC = methodInfo.GenerateOnePC();
      symbols.AssociateLabelWithPC("Start", startPC);
      symbols.AssociateLabelWithPC("Middle", midPC);
      symbols.AssociateLabelWithPC("End", endPC);

      // Create the can-return-from predicate.

      methodInfo.AddReturnPC(endPC);
    }

    public void CreateNextRoutinesForMethodWithNoBody(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                      List<MemberDecl> newDefaultClassDecls)
    {
      var methodName = methodInfo.method.Name;
      var startPC = new ArmadaPC(symbols, methodName, 0);
      var midPC = new ArmadaPC(symbols, methodName, 1);
      var endPC = new ArmadaPC(symbols, methodName, 2);

      // Generate the next routines for the three transitions.

      CreateNextRoutinesForMethodWithNoBodyPart1(symbols, methodInfo, newDefaultClassDecls, startPC, midPC);
      CreateNextRoutinesForMethodWithNoBodyPart2(symbols, methodInfo, newDefaultClassDecls, midPC);
      CreateNextRoutinesForMethodWithNoBodyPart3(symbols, methodInfo, newDefaultClassDecls, midPC, endPC);
    }

    public void CreateNextTerminateThread(ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      foreach (var returnPC in methodInfo.ReturnPCs) {
        var next = new NextRoutine(prog, symbols, NextType.Terminate, methodInfo, null, null, returnPC, null);
        methodInfo.method.terminateNextRoutine = next;

        // |t.stack| == 0

        var stack = AH.MakeExprDotName(next.t, "stack", AH.MakeStackType());
        var stack_size = AH.MakeCardinalityExpr(stack);
        var stack_empty = AH.MakeEqExpr(stack_size, AH.MakeZero());
        next.AddConjunct(stack_empty);

        // The thread's store buffer contents should be flushed before termination, i.e.,
        // |t.storeBuffers| == 0

        var store_buffer = AH.MakeExprDotName(next.t, "storeBuffer", AH.MakeStoreBufferType());
        var store_buffer_size = AH.MakeCardinalityExpr(store_buffer);
        var store_buffer_empty = AH.MakeEqExpr(store_buffer_size, AH.MakeZero());
        next.AddConjunct(store_buffer_empty);

        // s_current := s.(threads := (map other | other in s.threads && other != tid :: s.threads[other]))

        var other = AH.MakeNameSegment("other", "Armada_ThreadHandle");
        var threads = AH.MakeExprDotName(next.s, "threads", AH.MakeThreadsType());
        var other_in_threads = AH.MakeInExpr(other, threads);
        var other_neq_tid = AH.MakeNeqExpr(other, next.tid);
        var other_in_threads_and_neq_tid = AH.MakeAndExpr(other_in_threads, other_neq_tid);
        var other_thread = AH.MakeSeqSelectExpr(threads, other, "Armada_Thread");
        var bvars = new List<BoundVar> { AH.MakeBoundVar("other", "Armada_ThreadHandle") };
        var new_threads = AH.MakeMapComprehension(bvars, other_in_threads_and_neq_tid, other_thread);
        var s_current = AH.MakeDatatypeUpdateExpr(next.s, "threads", new_threads);
        s_current = next.AddVariableDeclaration("s", s_current);

        // Now, we need to free the new_ptrs.  In Dafny, if we denote s_current by s, that's:
        //
        // s := s.(mem := s.mem.(heap := s.mem.heap :=
        //         s.mem.heap.(valid := s.mem.heap.valid - t.new_ptrs,
        //                     freed := s.mem.heap.freed + t.new_ptrs))))

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

        // Finally, we need to set the stop_reason to Armada_StopReasonTerminated if the terminated
        // thread was the main thread.
        if (methodInfo.method.Name.Equals("main")) {
          s_current =
            AH.MakeDatatypeUpdateExpr(s_current, "stop_reason", AH.MakeNameSegment("Armada_StopReasonTerminated", "Armada_StopReason"));
          s_current = next.AddVariableDeclaration("s", s_current);
        }

        next.SetNextState(s_current);
        symbols.AddNextRoutine(next);
      }
    }

    public void ProcessMethods(ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls, List<TopLevelDecl> newTopLevelDecls)
    {
      bool mainFound = false;

      var c = symbols.DefaultClass;

      // First, parse all the methods.  This way, we'll know all the return PCs when
      // we later generate next routines.

      foreach (var methodName in symbols.AllMethods.AllMethodNames) {
        var methodInfo = symbols.AllMethods.LookupMethod(methodName);
        var method = methodInfo.method;
        if (method.Name == "main") {
          mainFound = true;
        }
        if (method.Body is null) {
          ParseMethodWithNoBody(prog, methodInfo, symbols, newDefaultClassDecls);
        }
        else {
          ParseMethodWithBody(prog, methodInfo, symbols, newDefaultClassDecls);
        }
        if (Attributes.Contains(method.Attributes, "atomic")) {
          methodInfo.UseAtomicCallsAndReturns();
        }
      }

      if (!mainFound) {
        AH.PrintError(prog, $"No main routine found");
      }

      // Next, generate next routines for all the methods.

      foreach (var methodName in symbols.AllMethods.AllMethodNames) {
        var methodInfo = symbols.AllMethods.LookupMethod(methodName);
        var method = methodInfo.method;
        if (method.Body is null) {
          CreateNextRoutinesForMethodWithNoBody(prog, symbols, methodInfo, newDefaultClassDecls);
        }
        else {
          methodInfo.ParsedBody.GenerateNextRoutines(prog, symbols, methodInfo);
        }
      }

      foreach (var methodName in symbols.GetThreadRoutines()) {
        var methodInfo = symbols.AllMethods.LookupMethod(methodName);
        CreateNextTerminateThread(symbols, methodInfo);
      }
    }

    public void CreateApplyTauUnaddressableFunction(ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      var globals = AH.MakeNameSegment("globals", "Armada_Globals");
      var v = AH.MakeNameSegment("v", "Armada_GlobalStaticVar");
      var fields = AH.MakeNameSegment("fields", AH.MakeSeqType("Armada_Field"));
      var value = AH.MakeNameSegment("value", "Armada_PrimitiveValue");

      var cases = new List<MatchCaseExpr>();

      foreach (var varName in symbols.Globals.VariableNames) {
        var gv = symbols.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          var cur_value = AH.MakeExprDotName(globals, varName, gv.ty);
          var updated_value = AH.GetInvocationOfPerformFieldUpdate(cur_value, fields, value);
          var updated_globals = AH.MakeDatatypeUpdateExpr(globals, varName, updated_value);
          cases.Add(AH.MakeMatchCaseExpr($"Armada_GlobalStaticVar_{varName}", updated_globals));
        }
      }

      cases.Add(AH.MakeMatchCaseExpr("Armada_GlobalStaticVarNone", globals));
      var body = AH.MakeMatchExpr(v, cases, "Armada_Globals");
      var fn = AH.MakeFunction("Armada_ApplyTauUnaddressable",
                               new List<Formal> {
                                 AH.MakeFormal("globals", "Armada_Globals"),
                                 AH.MakeFormal("v", "Armada_GlobalStaticVar"),
                                 AH.MakeFormal("fields", AH.MakeSeqType("Armada_Field")),
                                 AH.MakeFormal("value", "Armada_PrimitiveValue")
                               },
                               body);
      newDefaultClassDecls.Add(fn);
    }

    public Expression GetUpdatedHeapAfterTau(Expression h, Expression p, Expression value)
    {
      // if && p in h.valid
      //    && p in h.tree
      //    && p in h.values
      //    && h.tree[p].ty.Armada_ObjectType_primitive?
      //    && Armada_PrimitiveValueMatchesType(value, h.tree[p].ty.pty)
      // then
      //   h.(values := Armada_UpdateHeapValues(h.values, p, value)))
      // else
      //   h

      var conditions = new List<Expression>();
      var valid_set = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
      var valid = AH.MakeInExpr(p, valid_set);
      conditions.Add(valid);

      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
      var in_tree = AH.MakeInExpr(p, tree);
      conditions.Add(in_tree);

      var node = AH.MakeSeqSelectExpr(tree, p, "Armada_Node");
      var ty = AH.MakeExprDotName(node, "ty", "Armada_ObjectType");
      var is_primitive = AH.MakeExprDotName(ty, "Armada_ObjectType_primitive?", new BoolType());
      conditions.Add(is_primitive);

      var pty = AH.MakeExprDotName(ty, "pty", "Armada_PrimitiveType");
      var matches_type = AH.MakeApply2("Armada_PrimitiveValueMatchesType", value, pty, new BoolType());
      conditions.Add(matches_type);

      var values = AH.MakeExprDotName(h, "values", AH.MakeValuesType());
      var values_updated = AH.MakeApply3("Armada_UpdateHeapValues", values, p, value, AH.MakeValuesType());
      var h_updated = AH.MakeDatatypeUpdateExpr(h, "values", values_updated);

      var body = AH.MakeIfExpr(AH.CombineExpressionsWithAnd(conditions), h_updated, h);
      return body;
    }

    public void CreateApplyTauAddressableFunction(ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      var h = AH.MakeNameSegment("h", "Armada_Heap");
      var p = AH.MakeNameSegment("p", "Armada_Pointer");
      var value = AH.MakeNameSegment("value", "Armada_PrimitiveValue");
      var h_updated = GetUpdatedHeapAfterTau(h, p, value);
      var h_prime = AH.MakeNameSegment("h'", "Armada_Heap");
      var ens = AH.MakeApply2("Armada_HeapMetadataUnchangedByTau", h, h_prime, new BoolType());
      var fn = AH.MakeFunctionWithEns("Armada_ApplyTauAddressable",
                                      new List<Formal> {
                                        AH.MakeFormal("h", "Armada_Heap"),
                                        AH.MakeFormal("p", "Armada_Pointer"),
                                        AH.MakeFormal("value", "Armada_PrimitiveValue")
                                      },
                                      AH.MakeFormal("h'", "Armada_Heap"),
                                      ens,
                                      h_updated);
      newDefaultClassDecls.Add(fn);
    }

    public void CreateHeapMetadataUnchangedByTau(ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      var old_heap = AH.MakeNameSegment("h", "Armada_Heap");
      var new_heap = AH.MakeNameSegment("h'", "Armada_Heap");
      var preds = new List<Expression>();

      var old_valid = AH.MakeExprDotName(old_heap, "valid", AH.MakePointerSetType());
      var new_valid = AH.MakeExprDotName(new_heap, "valid", AH.MakePointerSetType());
      var valids_match = AH.MakeEqExpr(new_valid, old_valid);
      preds.Add(valids_match);

      var old_tree = AH.MakeExprDotName(old_heap, "tree", "Armada_Tree");
      var new_tree = AH.MakeExprDotName(new_heap, "tree", "Armada_Tree");
      var trees_match = AH.MakeEqExpr(new_tree, old_tree);
      preds.Add(trees_match);

      var old_freed = AH.MakeExprDotName(old_heap, "freed", "Armada_Freed");
      var new_freed = AH.MakeExprDotName(new_heap, "freed", "Armada_Freed");
      var freeds_match = AH.MakeEqExpr(new_freed, old_freed);
      preds.Add(freeds_match);

      var formals = new List<Formal> { AH.MakeFormal("h", "Armada_Heap"), AH.MakeFormal("h'", "Armada_Heap") };
      var body = AH.CombineExpressionsWithAnd(preds);
      var pred = AH.MakePredicate("Armada_HeapMetadataUnchangedByTau", formals, body);
      newDefaultClassDecls.Add(pred);
    }

    public void CreateTauNext(ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      CreateHeapMetadataUnchangedByTau(symbols, newDefaultClassDecls);
      CreateApplyTauUnaddressableFunction(symbols, newDefaultClassDecls);
      CreateApplyTauAddressableFunction(symbols, newDefaultClassDecls);

      var fnDef = @"
  function Armada_ApplyStoreBufferEntry(mem: Armada_SharedMemory, entry: Armada_StoreBufferEntry) : (mem':Armada_SharedMemory)
    ensures Armada_HeapMetadataUnchangedByTau(mem.heap, mem'.heap)
  {
    match entry.loc
        case Armada_StoreBufferLocation_Unaddressable(v, fields) => mem.(globals := Armada_ApplyTauUnaddressable(mem.globals, v, fields, entry.value))
        case Armada_StoreBufferLocation_Addressable(p) => mem.(heap := Armada_ApplyTauAddressable(mem.heap, p, entry.value))
  }
";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_ApplyStoreBufferEntry", fnDef));

      fnDef = @"
  function Armada_ApplyStoreBuffer(mem: Armada_SharedMemory, storeBuffer: seq<Armada_StoreBufferEntry>) : (mem':Armada_SharedMemory)
    ensures Armada_HeapMetadataUnchangedByTau(mem.heap, mem'.heap)
    decreases |storeBuffer|
  {
    if |storeBuffer| == 0 then
      mem
    else
      Armada_ApplyStoreBuffer(Armada_ApplyStoreBufferEntry(mem, storeBuffer[0]), storeBuffer[1..])
  }
";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_ApplyStoreBuffer", fnDef));

      fnDef = $@"
  function Armada_GetThreadLocalView(s: Armada_TotalState, tid: Armada_ThreadHandle) : (mem':Armada_SharedMemory)
    requires tid in s.threads
    ensures  Armada_HeapMetadataUnchangedByTau(s.mem.heap, mem'.heap)
  {{
    Armada_ApplyStoreBuffer(s.mem, s.threads[tid].storeBuffer)
  }}
";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_GetThreadLocalView", fnDef));

      var next = new NextRoutine(prog, symbols, NextType.Tau, null, null, null, null, null);
      symbols.TauNextRoutine = next;

      // Add conjunct |t.storeBuffer| > 0:

      var store_buffer = AH.MakeExprDotName(next.t, "storeBuffer", AH.MakeStoreBufferType());
      var store_buffer_size = AH.MakeCardinalityExpr(store_buffer);
      var store_buffer_nonempty = AH.MakeGtExpr(store_buffer_size, AH.MakeZero());
      next.AddConjunct(store_buffer_nonempty);

      //
      // Get an expression for what s.threads will be like after the first entry in the store buffer is popped:
      //    var updated_threads := s.threads[next.tid := next.t.(storeBuffer := t.storeBuffer[1..])]
      //

      var store_buffer_popped = AH.MakeSeqSliceExpr(store_buffer, AH.MakeOne(), null);
      var updated_thread = AH.MakeDatatypeUpdateExpr(next.t, "storeBuffer", store_buffer_popped);
      var threads = AH.MakeExprDotName(next.s, "threads", AH.MakeThreadsType());
      var updated_threads = AH.MakeSeqUpdateExpr(threads, next.tid, updated_thread);

      //
      // Get an expression for the correct final state:
      //    var mem' := Armada_ApplyStoreBufferEntry(s.mem, store_buffer_entry);
      //    s_updated := s.(threads := updated_threads, mem := mem');
      //

      var mem = AH.MakeExprDotName(next.s, "mem", "Armada_SharedMemory");
      var store_buffer_entry = AH.MakeSeqSelectExpr(store_buffer, AH.MakeZero(), "Armada_StoreBufferEntry");
      var mem_prime = AH.MakeApply2("Armada_ApplyStoreBufferEntry", mem, store_buffer_entry, "Armada_SharedMemory");
      var s_updated = AH.MakeDatatypeUpdate2Expr(next.s,
                                                 "threads", updated_threads,
                                                 "mem", mem_prime);

      next.SetNextState(s_updated);
      symbols.AddNextRoutine(next);
    }

    public void GenerateEnablingConditions(ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      foreach (var methodName in symbols.AllMethods.AllMethodNames) {
        var methodInfo = symbols.AllMethods.LookupMethod(methodName);
        var pcs = new List<ArmadaPC>();
        methodInfo.AppendAllPCs(pcs);
        foreach (var pc in pcs) {
          var collector = methodInfo.GetEnablingConstraintCollector(pc);
          if (collector == null || collector.Empty) {
            continue;
          }
          var body = collector.Extract();
          var formals = new List<Formal>{ AH.MakeFormal("s", "Armada_TotalState"), AH.MakeFormal("tid", "Armada_ThreadHandle") };

          var threads = AH.MakeExprDotName(collector.s, "threads", AH.MakeThreadsType());
          var tid_in_threads = AH.MakeInExpr(collector.tid, threads);
          var conditionsPred = AH.MakePredicateWithReq($"Armada_EnablingConditions_{pc}", formals, tid_in_threads, body);
          newDefaultClassDecls.Add(conditionsPred);
        }
      }
    }

    public void GenerateTreeStructProperties(ModuleDefinition m, ArmadaStructs structs, List<MemberDecl> newDefaultClassDecls)
    {
      string overallFnBody = "";
      foreach (var structName in structs.StructNames) {
        var s = structs.GetStruct(structName);
        overallFnBody += $"&& Armada_TreeStructProperties_{structName}(tree)";
        string fieldsInChildren = "";
        string childrenValid = "";
        string fieldsCorrectType = "";
        string fieldsOfType = "";
        bool emptyStruct = true;
        foreach (var fieldName in s.FieldNames) {
          var fieldType = s.GetFieldType(fieldName);
          emptyStruct = false;
          string objectType = GetObjectTypeAsString(m, fieldType, structs);
          if (objectType == null) {
            AH.PrintError(prog, $"Fields of struct can't have type {fieldType}, so you can't use that type for field {fieldName} of struct {structName}");
            continue;
          }
          fieldsInChildren += $"&& Armada_FieldStruct(Armada_FieldType_{structName}'{fieldName}()) in children";
          childrenValid += $"&& children[Armada_FieldStruct(Armada_FieldType_{structName}'{fieldName}())] in tree";
          fieldsCorrectType += $"&& tree[children[Armada_FieldStruct(Armada_FieldType_{structName}'{fieldName}())]].ty == {objectType}";
          fieldsOfType += $"|| f.f.Armada_FieldType_{structName}'{fieldName}?";
        }

        string fnDef;
        if (emptyStruct) {
          fnDef =   $"predicate Armada_TreeStructProperties_{structName}(tree:map<Armada_Pointer, Armada_Node>)"
                  + "{"
                  + $"forall p {{:trigger Armada_TriggerPointer(p)}} :: Armada_TriggerPointer(p) && p in tree && tree[p].ty.Armada_ObjectType_struct? && tree[p].ty.s.Armada_StructType_{structName}? ==> tree[p].children == map []"
                  + "}";
        }
        else {
          fnDef =   $"predicate Armada_TreeStructProperties_{structName}(tree:map<Armada_Pointer, Armada_Node>)"
                  + "{"
                  + $"&& (forall p {{:trigger Armada_TriggerPointer(p)}} :: Armada_TriggerPointer(p) && p in tree && tree[p].ty.Armada_ObjectType_struct? && tree[p].ty.s.Armada_StructType_{structName}? ==> var children := tree[p].children;"
                  + fieldsInChildren
                  + childrenValid
                  + fieldsCorrectType
                  + $") && (forall p, f {{:trigger Armada_TriggerPointer(p), Armada_TriggerField(f)}} :: Armada_TriggerPointer(p) && Armada_TriggerField(f) && p in tree && tree[p].ty.Armada_ObjectType_struct? && tree[p].ty.s.Armada_StructType_{structName}? && f in tree[p].children ==> f.Armada_FieldStruct? && ("
                  + fieldsOfType
                  + ")) }";
        }
        newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "TreeStructPropertiesSpecific", fnDef));
      }

      string overallFnDef;
      if (overallFnBody.Length == 0) {
        overallFnDef = "predicate Armada_TreeStructProperties(tree:map<Armada_Pointer, Armada_Node>) { true }";
      }
      else {
        overallFnDef = "predicate Armada_TreeStructProperties(tree:map<Armada_Pointer, Armada_Node>) {" + overallFnBody + "}";
      }
      newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "TreeStructProperties", overallFnDef));
    }

    public void GenerateAddressableStaticVariablesPredicates(ModuleDefinition m, ArmadaSymbolTable symbols,
                                                             List<MemberDecl> newDefaultClassDecls)
    {
      var s = AH.MakeNameSegment("s", "Armada_TotalState");
      var new_ptrs = AH.MakeNameSegment("new_ptrs", AH.MakePointerSetType());

      // Every addressable global variable is a root of the heap
      var addrs = AH.MakeExprDotName(s, "addrs", "Armada_Addrs");
      var h = AH.MakeNameSegment("h", "Armada_Heap");
      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");

      var root_preds = new List<Expression>();
      var validity_preds = new List<Expression>();

      var previouslySeenAddressableVariableAddrs = new List<Expression>();
      foreach (var varName in symbols.Globals.VariableNames) {
        var v = symbols.Globals.Lookup(varName);
        if (v is AddressableArmadaVariable) {
          var addr = AH.MakeExprDotName(addrs, varName, "Armada_Pointer");
          foreach (var otherAddr in previouslySeenAddressableVariableAddrs) {
            root_preds.Add(AH.MakeNeqExpr(addr, otherAddr));
          }
          previouslySeenAddressableVariableAddrs.Add(addr);
          var pointer_valid = AH.GetInvocationOfValidPointer(h, addr, v.ty);
          if (pointer_valid is null) {
            AH.PrintError(prog, "Invalid type for static variable {varName}");
          }
          else {
            validity_preds.Add(pointer_valid);
          }
          var addr_in_tree = AH.MakeInExpr(addr, tree);
          root_preds.Add(addr_in_tree);
          var node = AH.MakeSeqSelectExpr(tree, addr, "Armada_Node");
          var field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
          var field_none = AH.MakeExprDotName(field_of_parent, "Armada_FieldNone?", new BoolType());
          root_preds.Add(field_none);
          var root_type = AH.MakeExprDotName(field_of_parent, "rt", "Armada_RootType");
          var is_static_heap = AH.MakeExprDotName(root_type, "Armada_RootTypeStaticHeap?", new BoolType());
          root_preds.Add(is_static_heap);
        }
      }

      var mem = AH.MakeExprDotName(s, "mem", "Armada_SharedMemory");
      h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
      var body = AH.CombineExpressionsWithAnd(root_preds);
      var formals = new List<Formal>() { AH.MakeFormal("s", "Armada_TotalState") };
      body = AH.MakeLet1Expr("h", h, body);
      var fn = AH.MakePredicate("Armada_AddressableStaticVariablesAreDistinctRoots", formals, body);
      newDefaultClassDecls.Add(fn);

      body = AH.CombineExpressionsWithAnd(validity_preds);
      var valid = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
      var valid_without_new_ptrs = AH.MakeSubExpr(valid, new_ptrs);
      var h_without_new_ptrs = AH.MakeDatatypeUpdateExpr(h, "valid", valid_without_new_ptrs);
      body = AH.MakeLet1Expr("h", h_without_new_ptrs, body);
      formals = new List<Formal>() { AH.MakeFormal("s", "Armada_TotalState"), AH.MakeFormal("new_ptrs", AH.MakePointerSetType()) };
      fn = AH.MakePredicate("Armada_AddressableStaticVariablesAreValid", formals, body);
      newDefaultClassDecls.Add(fn);
    }

    public void GenerateInitPredicate(ModuleDefinition m, ArmadaSymbolTable symbols,
                                      List<TopLevelDecl> newTopLevelDecls, List<MemberDecl> newDefaultClassDecls)
    {
      var config_formals = new List<Formal> { AH.MakeFormal("tid_init", "Armada_ThreadHandle"),
                                              AH.MakeFormal("new_ptrs", AH.MakePointerSetType()) };
      var config_ctor = AH.MakeDatatypeCtor("Armada_Config", config_formals);
      var config_decl = AH.MakeDatatypeDecl(m, "Armada_Config", new List<DatatypeCtor> { config_ctor });
      newTopLevelDecls.Add(config_decl);

      var s = AH.MakeNameSegment("s", "Armada_TotalState");
      var config = AH.MakeNameSegment("config", "Armada_Config");
      var tid = AH.MakeExprDotName(config, "tid_init", "Armada_ThreadHandle");
      var new_ptrs = AH.MakeExprDotName(config, "new_ptrs", AH.MakePointerSetType());

      var builder = new PredicateBuilder(prog);

      // s.stop_reason.Armada_NotStopped?
      var stop_reason = AH.MakeExprDotName(s, "stop_reason", "Armada_StopReason");
      var not_stopped = AH.MakeExprDotName(stop_reason, "Armada_NotStopped?", new BoolType());
      builder.AddConjunct(not_stopped);

      // util_collections_maps_i.MapHasUniqueKey(s.threads, config.tid_init)
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var only_one_thread = AH.MakeApply2("util_collections_maps_i.MapHasUniqueKey", threads, tid, new BoolType());
      builder.AddConjunct(only_one_thread);

      // tid_init != 0
      var tid_nonzero = AH.MakeNeqExpr(tid, AH.MakeZero());
      builder.AddConjunct(tid_nonzero);

      // var t := s.threads[config.tid_init];
      var t = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
      t = builder.AddVariableDeclaration("t", t);

      // t.pc == Armada_PC_main'0
      var current_pc = AH.MakeExprDotName(t, "pc", "Armada_PC");
      var main_pc_0 = AH.MakeNameSegment(new ArmadaPC(symbols, "main", 0).ToString(), "Armada_PC");
      var pc_correct = AH.MakeEqExpr(current_pc, main_pc_0);
      builder.AddConjunct(pc_correct);

      // t.top.Armada_StackFrame_main?
      var top = AH.MakeExprDotName(t, "top", "Armada_StackFrame");
      var method_running = AH.MakeExprDotName(top, "Armada_StackFrame_main?", new BoolType());
      builder.AddConjunct(method_running);

      // t.new_ptrs == new_ptrs;
      var t_new_ptrs = AH.MakeExprDotName(t, "new_ptrs", AH.MakePointerSetType());
      var t_new_ptrs_is_new_ptrs = AH.MakeEqExpr(t_new_ptrs, new_ptrs);
      builder.AddConjunct(t_new_ptrs_is_new_ptrs);

      // |t.stack| = 0
      var stack = AH.MakeExprDotName(t, "stack", AH.MakeStackType());
      var stack_size = AH.MakeCardinalityExpr(stack);
      var stack_size_zero = AH.MakeEqExpr(stack_size, AH.MakeZero());
      builder.AddConjunct(stack_size_zero);

      // |t.storeBuffer| == 0
      var store_buffer = AH.MakeExprDotName(t, "storeBuffer", AH.MakeStoreBufferType());
      var store_buffer_size = AH.MakeCardinalityExpr(store_buffer);
      var store_buffer_empty = AH.MakeEqExpr(store_buffer_size, AH.MakeZero());
      builder.AddConjunct(store_buffer_empty);

      // For each addressable stack variable in the main stack frame, it's valid and among new_ptrs

      var mem = AH.MakeExprDotName(s, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
      var smst = symbols.GetMethodSymbolTable("main");
      string p_in_new_ptrs = "";
      List<string> addressesOfAddressables = new List<string>();
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.varType == ArmadaVarType.Local && v is AddressableArmadaVariable))
      {
        var varName = v.name;
        var new_ptr = AH.MakeExprDotName(top, $"main'AddrOf'{varName}", "Armada_Pointer");

        // new_ptr is among new_ptrs

        var new_ptr_in_new_ptrs = AH.MakeInExpr(new_ptr, new_ptrs);
        builder.AddConjunct(new_ptr_in_new_ptrs);

        // new_ptr is in s.mem.heap.tree

        var new_ptr_in_tree = AH.MakeInExpr(new_ptr, tree);
        builder.AddConjunct(new_ptr_in_tree);

        // new_ptr is a stack-based root in s.mem.heap, i.e.,
        //    && s.mem.heap.tree[new_ptr].field_of_parent.Armada_FieldNone?
        //    && s.mem.heap.tree[new_ptr].field_of_parent.rt.Armada_RootTypeStack?

        var node = AH.MakeSeqSelectExpr(tree, new_ptr, "Armada_Node");
        var field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
        var new_ptr_is_root = AH.MakeExprDotName(field_of_parent, "Armada_FieldNone?", new BoolType());
        var root_type = AH.MakeExprDotName(field_of_parent, "rt", "Armada_RootType");
        var root_type_stack = AH.MakeExprDotName(root_type, "Armada_RootTypeStack?", new BoolType());
        builder.AddConjunct(new_ptr_is_root);
        builder.AddConjunct(root_type_stack);
        
        // new_ptr is a valid pointer in s.mem.heap
        
        var pointer_valid = AH.GetInvocationOfValidPointer(h, new_ptr, v.ty);
        builder.AddConjunct(pointer_valid);
        
        var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
          AH.MakeNameSegment("s.mem.heap", "Armada_Heap"),
          AH.MakeNameSegment($"t.top.main'AddrOf'{varName}", "Armada_Pointer"),
          v.ty
        );
        p_in_new_ptrs += $"|| p in {Printer.ExprToString(allocatedByExpr)}";
        addressesOfAddressables.Add($"t.top.main'AddrOf'{varName}");
      }
      string str;
      if (p_in_new_ptrs.Length > 0) {
        str = $"forall p :: p in config.new_ptrs <==> ({p_in_new_ptrs})";
      }
      else {
        str = "config.new_ptrs == {}";
      }
      builder.AddConjunct(AH.ParseExpression(prog, "", str));
      builder.AddConjunct(AH.ParseExpression(prog, "", str));
      for (int i = 0; i < addressesOfAddressables.Count; i++) {
        for (int j = i + 1; j < addressesOfAddressables.Count; j++) {
          str = addressesOfAddressables[i] + " != " + addressesOfAddressables[j];
          builder.AddConjunct(AH.ParseExpression(prog, "", str));
        }
      }

      // Initialize stack variables in main
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.InitialValue != null))
      {
        var varName = v.name;
        var ty = symbols.FlattenType(v.ty);
        var resContext = new ResolutionContext(s, s, tid, "main", symbols, null);
        Expression var_value = AH.MakeExprDotName(top, $"main'{varName}", "Armada_Pointer");
        if (v is AddressableArmadaVariable) {
          var_value = AH.MakeExprDotName(top, $"main'AddrOf'{varName}", "Armada_Pointer");
          var_value = AH.GetInvocationOfDereferencePointer(h, var_value, ty);
        }
        var rhsRVal = resContext.ResolveAsRValue(v.InitialValue);
        var rhs = rhsRVal.Val;
        var var_init_predicate = AH.MakeEqExpr(var_value, rhs);
        builder.AddConjunct(var_init_predicate);
      }

      // The global static variables are valid, even if new_ptrs are excluded from the list of valid pointers.

      var static_vars_valid = AH.MakeApply2("Armada_AddressableStaticVariablesAreValid", s, new_ptrs, new BoolType());
      builder.AddConjunct(static_vars_valid);

      // The global static variables are roots.

      var static_vars_are_roots = AH.MakeApply1("Armada_AddressableStaticVariablesAreDistinctRoots", s, new BoolType());
      builder.AddConjunct(static_vars_are_roots);

      // Armada_HeapInvariant(s.mem.heap)
      var heap_invariant = AH.MakeApply1("Armada_HeapInvariant", h, new BoolType());
      builder.AddConjunct(heap_invariant);

      // Any global variable is initialized appropriately: if it's an
      // unaddressable array, it has the right length, and if it has
      // an initializer then it has that value.

      var failureReporter = new SimpleFailureReporter(prog);
      var context = new GlobalInvariantResolutionContext(s, symbols, failureReporter, "");
      foreach (var globalVariableName in symbols.Globals.VariableNames) {
        var globalVar = symbols.Globals.Lookup(globalVariableName);
        if (globalVar is GlobalUnaddressableArmadaVariable && globalVar.ty is SizedArrayType) {
          var gv_expr = globalVar.GetRValue(Token.NoToken, context);
          var sz = ((SizedArrayType)globalVar.ty).Size;
          var gv_cardinality = AH.MakeCardinalityExpr(gv_expr.Val);
          var gv_has_correct_size = AH.MakeEqExpr(gv_cardinality, sz);
          builder.AddConjunct(gv_has_correct_size);
        }
        if (globalVar.initialValue != null) {
          var gv_expr = globalVar.GetRValue(Token.NoToken, context);
          var val_expr = context.ResolveAsRValue(globalVar.initialValue);
          //
          // We don't crash if these rvalues aren't valid, since we can't crash at init time.
          // Instead, we just generate Dafny that won't satisfy validity checks if that's an issue.
          //
          var gv_initialized_correctly = AH.MakeEqExpr(gv_expr.Val, val_expr.Val);
          builder.AddConjunct(gv_initialized_correctly);
        }
      }

      var init_body = builder.Extract();
      var init_formals = new List<Formal>() { AH.MakeFormal("s", "Armada_TotalState"), AH.MakeFormal("config", "Armada_Config") };
      var init = AH.MakePredicate("Armada_InitConfig", init_formals, init_body);
      newDefaultClassDecls.Add(init);

      str = @"
        predicate Armada_Init(s:Armada_TotalState)
        {
          exists config :: Armada_InitConfig(s, config)
        }
      ";
      newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "Armada_Init", str));
    }

    public void GenerateIsNonyieldingPCPredicate(ModuleDefinition m, ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls)
    {
      var nonyieldingPCs = new List<ArmadaPC>();
      symbols.AllMethods.AppendAllNonyieldingPCs(nonyieldingPCs);

      string str = "predicate Armada_IsNonyieldingPC(pc:Armada_PC) {\n  false\n";
      foreach (var pc in nonyieldingPCs) {
        str += $"  || pc.{pc}?\n";
      }
      str += "}\n";
      newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "IsNonyieldingPC", str));
    }

    public void GenerateNextBodies(ModuleDefinition m, ArmadaSymbolTable symbols,
                                   List<TopLevelDecl> newTopLevelDecls, List<MemberDecl> newDefaultClassDecls)
    {
      var entryCtors = new List<DatatypeCtor>();
      var overallNextCases = new List<MatchCaseExpr>();
      var validStepCases = new List<MatchCaseExpr>();
      var crashAvoidanceCases = new List<MatchCaseExpr>();
      var getNextStateCases = new List<MatchCaseExpr>();
      foreach (var nextRoutine in symbols.NextRoutines) {
        nextRoutine.Extract(m, symbols, newDefaultClassDecls, entryCtors, overallNextCases, validStepCases, crashAvoidanceCases,
                            getNextStateCases);
      }

      if (overallNextCases.Count() == 0) {
        return;
      }

      var entryDecl = AH.MakeDatatypeDecl(m, "Armada_TraceEntry", entryCtors);
      newTopLevelDecls.Add(entryDecl);

      var s = AH.MakeNameSegment("s", "Armada_TotalState");
      var s_prime = AH.MakeNameSegment("s'", "Armada_TotalState");
      var entry = AH.MakeNameSegment("entry", "Armada_TotalEntry");
      var formal_s = AH.MakeFormal("s", "Armada_TotalState");
      var formal_s_prime = AH.MakeFormal("s'", "Armada_TotalState");
      var formal_entry = AH.MakeFormal("entry", "Armada_TraceEntry");

      // predicate Armada_NextOneStep(s:Armada_TotalState, s':Armada_TotalState, entry:Armada_TraceEntry)
      // {
      //     match entry ...
      // }

      var overallNextFormals = new List<Formal> { formal_s, formal_s_prime, formal_entry };
      var overallNextBody = AH.MakeMatchExpr(entry, overallNextCases, new BoolType());
      var overallNext = AH.MakePredicate("Armada_NextOneStep", overallNextFormals, overallNextBody);
      newDefaultClassDecls.Add(overallNext);

      // predicate Armada_ValidStep(s:Armada_TotalState, entry:Armada_TraceEntry)
      // {
      //     match entry ...
      // }

      var validStepFormals = new List<Formal> { formal_s, formal_entry };
      var validStepBody = AH.MakeMatchExpr(entry, validStepCases, new BoolType());
      var validStep = AH.MakePredicate("Armada_ValidStep", validStepFormals, validStepBody);
      newDefaultClassDecls.Add(validStep);

      // predicate Armada_UndefinedBehaviorAvoidance(s:Armada_TotalState, entry:Armada_TraceEntry)
      //     requires Armada_ValidStep(s, entry)
      // {
      //     match entry ...
      // }

      var crashAvoidanceFormals = new List<Formal> { formal_s, formal_entry };
      var crashAvoidanceBody = AH.MakeMatchExpr(entry, crashAvoidanceCases, new BoolType());
      var validStatePred = AH.MakeApply2("Armada_ValidStep", s, entry, new BoolType());
      var crashAvoidance = AH.MakePredicateWithReq("Armada_UndefinedBehaviorAvoidance", crashAvoidanceFormals, validStatePred, crashAvoidanceBody);
      newDefaultClassDecls.Add(crashAvoidance);

      // function Armada_GetNextState(s:Armada_TotalState, entry:Armada_TraceEntry) : Armada_TotalState
      //     requires Armada_ValidStep(s, entry) && Armada_UndefinedBehaviorAvoidance(s, entry)
      // {
      //     match entry ...
      // }

      var getNextStateFormals = new List<Formal> { formal_s, formal_entry };
      var getNextStateBody = AH.MakeMatchExpr(entry, getNextStateCases, "Armada_TotalState");
      var crashAvoidancePred = AH.MakeApply2("Armada_UndefinedBehaviorAvoidance", s, entry, new BoolType());
      var getNextStateReq = AH.MakeAndExpr(validStatePred, crashAvoidancePred);
      var getNextState = AH.MakeFunctionWithReq("Armada_GetNextState", getNextStateFormals, getNextStateReq, getNextStateBody);
      newDefaultClassDecls.Add(getNextState);

      string str;

      str = @"
        function Armada_GetNextStateAlways(s: Armada_TotalState, entry: Armada_TraceEntry): Armada_TotalState
        {
          if Armada_ValidStep(s, entry) && Armada_UndefinedBehaviorAvoidance(s, entry) then
            Armada_GetNextState(s, entry)
          else
            s.(stop_reason := Armada_StopReasonUndefinedBehavior)
        }
      ";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_GetNextStateAlways", str));

      str = @"
        predicate Armada_NextOneStepAlt(s:Armada_TotalState, s':Armada_TotalState, entry:Armada_TraceEntry)
        {
           && Armada_ValidStep(s, entry)
           && s' == Armada_GetNextStateAlways(s, entry)
        }
      ";
      newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "Armada_NextOneStepAlt", str));

      str = @"
        function Armada_GetSpecFunctions() : Armada_SpecFunctions<Armada_TotalState, Armada_TraceEntry, Armada_PC>
        {
          Armada_SpecFunctions(Armada_Init,
                               Armada_ValidStep,
                               Armada_GetNextStateAlways,
                               (step:Armada_TraceEntry) => step.tid,
                               (step:Armada_TraceEntry) => step.Armada_TraceEntry_Tau?,
                               (s:Armada_TotalState) => s.stop_reason.Armada_NotStopped?,
                               (s:Armada_TotalState, tid:Armada_ThreadHandle) =>
                                 if tid in s.threads then util_option_s.Some(s.threads[tid].pc) else util_option_s.None,
                               Armada_IsNonyieldingPC)
        }
      ";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_GetSpecFunctions", str));

      str = @"
        predicate Armada_Next(s: Armada_TotalState, s': Armada_TotalState, entry: Armada_Multistep<Armada_TraceEntry>)
        {
          Armada_NextMultistep(Armada_GetSpecFunctions(), s, s', entry.steps, entry.tid, entry.tau)
        }
      ";
      newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "Armada_Next", str));

      // function Armada_Spec() : GeneralRefinementModule.Spec<Armada_TotalState> {
      //     GeneralRefinementModule.Spec(iset s | Armada_Init(s),
      //                                  iset s, s', entry | Armada_Next(s, s', entry) :: GeneralRefinementModule.StatePair(s, s'))
      // }

      var bv_s = AH.MakeBoundVar("s", "Armada_TotalState");
      var bv_s_prime = AH.MakeBoundVar("s'", "Armada_TotalState");
      var bv_entry = AH.MakeBoundVar("entry", "Armada_Multistep<Armada_TraceEntry>");
      var init_set = AH.MakeIsetComprehension(new List<BoundVar> { bv_s },
                                              AH.MakeApply1("Armada_Init", s, new BoolType()),
                                              s);
      var next_set = AH.MakeIsetComprehension(new List<BoundVar> { bv_s, bv_s_prime, bv_entry },
                                              AH.MakeApply3("Armada_Next", s, s_prime, entry, new BoolType()),
                                              AH.MakeApply2("GeneralRefinementModule.StatePair", s, s_prime, "StatePair"));
      var spec_body = AH.MakeApply2("GeneralRefinementModule.Spec", init_set, next_set,
                                    AH.MakeGenericTypeSpecific("GeneralRefinementModule.Spec", "Armada_TotalState"));
      var spec_function = AH.MakeFunction("Armada_Spec", new List<Formal>(), spec_body);
      newDefaultClassDecls.Add(spec_function);
    }

    public void GenerateStructAllocatedByFunctions(ModuleDefinition m, ArmadaStructs structs,
                                                    List<MemberDecl> newDefaultClassDecls, List<TopLevelDecl> newTopLevelDecls)
    {
      foreach (var structName in structs.StructNames) {
        var builder = new PredicateBuilder(prog);
        var s = structs.GetStruct(structName);
        List<string> allocatorCalls = new List<string>();
        allocatorCalls.Add("{p}");
        foreach (var fieldName in s.FieldNames) {
          var ty = s.GetFieldType(fieldName);
          var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
            AH.MakeNameSegment("h", "Armada_Heap"),
            AH.MakeNameSegment($"h.tree[p].children[Armada_FieldStruct(Armada_FieldType_{structName}'{fieldName})]", "Armada_Pointer"),
            ty
          );
          allocatorCalls.Add(Printer.ExprToString(allocatedByExpr));
        }
        string body = String.Join(" + ", allocatorCalls);

        string str = $@"
        function Armada_AllocatedByStruct_{structName}(h: Armada_Heap, p: Armada_Pointer): set<Armada_Pointer>
          requires Armada_ValidPointerToStruct_{structName}(h, p)
        {{
          {body}
        }}
        ";
        newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, $"Armada_AllocatedByStructArray_{structName}", str));

        str = $@"
          function Armada_RecAllocatedByStructArray_{structName}(h: Armada_Heap, p: Armada_Pointer, j: int): set<Armada_Pointer>
            requires Armada_ValidPointerToStructArray_{structName}(h, p)
            requires 0 <= j <= h.tree[p].ty.sz
            decreases h.tree[p].ty.sz - j
          {{
            if j == h.tree[p].ty.sz then
            {{}}
            else
            Armada_AllocatedByStruct_{structName}(h, h.tree[p].children[Armada_FieldArrayIndex(j)]) + Armada_RecAllocatedByStructArray_{structName}(h, p, j + 1)
          }}
        ";
        newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, $"Armada_RecAllocatedByStructArray_{structName}", str));

        str = $@"
          function {{:opaque}} Armada_AllocatedByStructArray_{structName}(h: Armada_Heap, p: Armada_Pointer): set<Armada_Pointer>
            requires Armada_ValidPointerToStructArray_{structName}(h, p)
          {{
            {{p}} + Armada_RecAllocatedByStructArray_{structName}(h, p, 0)
          }}
        ";
        newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, $"Armada_AllocatedByStructARray_{structName}", str));
      }
    }

    public void GenerateStructDatatypesAndFunctions(ModuleDefinition m, ArmadaStructs structs,
                                                    List<MemberDecl> newDefaultClassDecls, List<TopLevelDecl> newTopLevelDecls)
    {
      GenerateStructAllocatedByFunctions(m, structs, newDefaultClassDecls, newTopLevelDecls);
      var structTypes = new List<string> { "Armada_StructTypeNone" };
      var structFieldTypes = new List<string> { "Armada_FieldTypeNone" };
      GenerateStructDatatypes(m, structs, newTopLevelDecls, structTypes, structFieldTypes);

      var dtDecl = AH.MakeDatatypeDecl(m, "Armada_FieldType",
                                       structFieldTypes.Select(s => AH.MakeDatatypeCtor(s, new List<Formal>())).ToList());
      newTopLevelDecls.Add(dtDecl);
      dtDecl = AH.MakeDatatypeDecl(m, "Armada_StructType",
                                   structTypes.Select(s => AH.MakeDatatypeCtor(s, new List<Formal>())).ToList());
      newTopLevelDecls.Add(dtDecl);

      var synDecl = AH.MakeTypeSynonymDecl(m, "Armada_ObjectType",
                                           new UserDefinedType(Token.NoToken, "Armada_ObjectTypeGeneric",
                                                               new List<Type> { AH.ReferToType("Armada_StructType") }));
      newTopLevelDecls.Add(synDecl);

      synDecl = AH.MakeTypeSynonymDecl(m, "Armada_Field",
                                       new UserDefinedType(Token.NoToken, "Armada_FieldGeneric",
                                                           new List<Type> { AH.ReferToType("Armada_FieldType") }));
      newTopLevelDecls.Add(synDecl);

      synDecl = AH.MakeTypeSynonymDecl(m, "Armada_Node",
                                       new UserDefinedType(Token.NoToken, "Armada_NodeGeneric",
                                                           new List<Type> { AH.ReferToType("Armada_StructType"),
                                                                            AH.ReferToType("Armada_FieldType") }));
      newTopLevelDecls.Add(synDecl);

      synDecl = AH.MakeTypeSynonymDecl(m, "Armada_Heap",
                                       new UserDefinedType(Token.NoToken, "Armada_HeapGeneric",
                                                           new List<Type> { AH.ReferToType("Armada_StructType"),
                                                                            AH.ReferToType("Armada_FieldType") }));
      newTopLevelDecls.Add(synDecl);

      synDecl = AH.MakeTypeSynonymDecl(m, "Armada_Tree",
                                       AH.MakeMapType("Armada_Pointer",
                                                      new UserDefinedType(Token.NoToken, "Armada_NodeGeneric",
                                                                          new List<Type> {
                                                                            AH.ReferToType("Armada_StructType"),
                                                                            AH.ReferToType("Armada_FieldType")
                                                                          })));
      newTopLevelDecls.Add(synDecl);

      var fnDef = @"
    predicate Armada_TreeProperties(tree:Armada_Tree)
    {
        && Armada_TreeForestProperties(tree)
        && Armada_TreeStructProperties(tree)
        && Armada_TreeArrayProperties(tree)
        && Armada_TreePrimitiveProperties(tree)
    }
          ";
      newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "Armada_TreeProperties", fnDef));

      fnDef = @"
    predicate Armada_HeapInvariant(h:Armada_Heap)
    {
        // There's no overlap between valid and freed pointers
        && h.valid * h.freed == {}

        // The special pointer value 0 is always freed, so it's never valid
        && 0 in h.freed

        // This seems redundant, given the above two, but Dafny has a hard time deducing this without it being in the invariant
        && !(0 in h.valid)

        && Armada_TreeProperties(h.tree)

        // Every pointer has the same validity as its parent. So, every tree in the forest has the
        // same validity for all its pointers.
        && (forall p {:trigger Armada_TriggerPointer(p)} ::
                Armada_TriggerPointer(p) && p in h.tree
                && Armada_TriggerPointer(h.tree[p].parent) && Armada_TriggerField(h.tree[p].field_of_parent)
                  ==> (p in h.valid <==> h.tree[p].parent in h.valid))

        // If a pointer is to a primitive object type, then its corresponding value matches that
        // type.
        && (forall p {:trigger Armada_TriggerPointer(p)} ::
                Armada_TriggerPointer(p) && p in h.tree && h.tree[p].ty.Armada_ObjectType_primitive?
                ==> p in h.values && Armada_PrimitiveValueMatchesType(h.values[p], h.tree[p].ty.pty))
    }
          ";
      newDefaultClassDecls.Add((Predicate)AH.ParseTopLevelDecl(prog, "HeapInvariant", fnDef));

      foreach (var structName in structs.StructNames) {
        var s = structs.GetStruct(structName);

        var h = AH.MakeNameSegment("h", "Armada_Heap");
        var p = AH.MakeNameSegment("p", "Armada_Pointer");

        var preds = new List<Expression>();

        var trigger_pointer = AH.MakeApply1("Armada_TriggerPointer", p, new BoolType());
        preds.Add(trigger_pointer);

        var valid_set = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
        var valid = AH.MakeInExpr(p, valid_set);
        preds.Add(valid);

        var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
        var p_in_tree = AH.MakeInExpr(p, tree);
        preds.Add(p_in_tree);

        var node = AH.MakeSeqSelectExpr(tree, p, "Armada_Node");
        var node_ty = AH.MakeExprDotName(node, "ty", "Armada_ObjectType");
        var struct_type = AH.MakeNameSegment($"Armada_StructType_{structName}", "Armada_StructType");
        var obj_type = AH.MakeApply1("Armada_ObjectType_struct", struct_type, "Armada_ObjectType");
        var correct_obj_type = AH.MakeEqExpr(node_ty, obj_type);
        preds.Add(correct_obj_type);

        var children = AH.MakeExprDotName(node, "children", AH.MakeChildrenType());
        foreach (var fieldName in s.FieldNames) {
          var fieldType = s.GetFieldType(fieldName);
          var struct_field_type = AH.MakeNameSegment($"Armada_FieldType_{structName}'{fieldName}", "Armada_FieldType");
          var field_type = AH.MakeApply1("Armada_FieldStruct", struct_field_type, "Armada_FieldStruct");
          var trigger_field = AH.MakeApply1("Armada_TriggerField", field_type, new BoolType());
          preds.Add(trigger_field);
          var field_among_children = AH.MakeInExpr(field_type, children);
          preds.Add(field_among_children);
          var child = AH.MakeSeqSelectExpr(children, field_type, "Armada_Pointer");
          var subpred = AH.GetInvocationOfValidPointer(h, child, fieldType);
          if (subpred == null) {
            AH.PrintError(prog, $"Type {fieldType} isn't a valid type to have a pointer to");
          }
          else {
            preds.Add(subpred);
          }
        }
        var body = AH.CombineExpressionsWithAnd(preds);
        var pred = AH.MakePredicate($"Armada_ValidPointerToStruct_{structName}",
                                    new List<Formal> {
                                      AH.MakeFormal("h", "Armada_Heap"),
                                      AH.MakeFormal("p", "Armada_Pointer")
                                    },
                                    body);
        newDefaultClassDecls.Add(pred);

        fnDef = $@"
            predicate Armada_ValidPointerToStructArray_{structName}(h:Armada_Heap, p:Armada_Pointer)
            {{
              && Armada_TriggerPointer(p)
              && p in h.valid
              && p in h.tree
              && var ty := h.tree[p].ty;
              && ty.Armada_ObjectType_array?
              && ty.subtype.Armada_ObjectType_struct?
              && ty.subtype.s.Armada_StructType_{structName}?
              && ty.sz >= 0
              && (forall i :: 0 <= i < ty.sz ==> var idx := Armada_FieldArrayIndex(i);
                                      && Armada_TriggerField(idx)
                                      && idx in h.tree[p].children
                                      && Armada_ValidPointerToStruct_{structName}(h, h.tree[p].children[idx]))
            }}
        ";
        newDefaultClassDecls.Add((Predicate) AH.ParseTopLevelDecl(prog, $"Armada_ValidPointerToStructArray_{structName}", fnDef));

        fnDef = $@"
            predicate Armada_ValidPointerToStructSizedArray_{structName}(h:Armada_Heap, p:Armada_Pointer, sz:int)
            {{
              && Armada_TriggerPointer(p)
              && Armada_ValidPointerToStructArray_{structName}(h, p)
              && h.tree[p].ty.sz == sz >= 0
            }}
        ";
        newDefaultClassDecls.Add((Predicate) AH.ParseTopLevelDecl(prog, $"Armada_ValidPointerToStructArray_{structName}", fnDef));

        var constructor_params = new List<Expression>();
        foreach (var fieldName in s.FieldNames) {
          var fieldType = s.GetFieldType(fieldName);
          var struct_field_type = AH.MakeNameSegment($"Armada_FieldType_{structName}'{fieldName}", "Armada_FieldType");
          var field_type = AH.MakeApply1("Armada_FieldStruct", struct_field_type, "Armada_FieldStruct");
          var child = AH.MakeSeqSelectExpr(children, field_type, "Armada_Pointer");
          var dereferenced_child = AH.GetInvocationOfDereferencePointer(h, child, fieldType);
          if (dereferenced_child == null) {
            AH.PrintError(prog, $"Type {fieldType} is an invalid type to have in a struct");
          }
          else {
            constructor_params.Add(dereferenced_child);
          }
        }
        var constructed_value = AH.SetExprType(new ApplySuffix(Token.NoToken,
                                                               AH.MakeNameSegment($"Armada_Struct_{structName}", (Type)null),
                                                               constructor_params),
                                               AH.ReferToType($"Armada_Struct_{structName}"));

        var req = AH.MakeApply2($"Armada_ValidPointerToStruct_{structName}", h, p, new BoolType());
        var fn = AH.MakeFunctionWithReq($"Armada_DereferencePointerToStruct_{structName}",
                                        new List<Formal> {
                                          AH.MakeFormal("h", "Armada_Heap"),
                                          AH.MakeFormal("p", "Armada_Pointer")
                                        },
                                        req,
                                        constructed_value);
        newDefaultClassDecls.Add(fn);

        fnDef = $@"
            function Armada_DereferencePointerToStructArray_{structName}(h:Armada_Heap, p:Armada_Pointer) : seq<Armada_Struct_{structName}>
              requires Armada_ValidPointerToStructArray_{structName}(h, p)
            {{
                util_collections_seqs_i.ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToStruct_{structName}(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
            }}
        ";
        newDefaultClassDecls.Add((Function) AH.ParseTopLevelDecl(prog, $"Armada_DereferencePointerToStructArray_{structName}", fnDef));

        var value = AH.MakeNameSegment("value", $"Armada_Struct_{structName}");
        var h_cur = h;
        foreach (var fieldName in s.FieldNames) {
          var fieldType = s.GetFieldType(fieldName);
          var struct_field_type = AH.MakeNameSegment($"Armada_FieldType_{structName}'{fieldName}", "Armada_FieldType");
          var field_type = AH.MakeApply1("Armada_FieldStruct", struct_field_type, "Armada_FieldStruct");
          var subvalue = AH.MakeExprDotName(value, fieldName, fieldType);
          h_cur = AH.GetInvocationOfUpdateChild(h_cur, p, field_type, subvalue, fieldType);
          if (h_cur == null) {
            AH.PrintError(prog, $"Can't have child of type {fieldType} in structure");
            break;
          }
        }
        if (h_cur != null) {
          fn = AH.MakeFunction($"Armada_UpdatePointerToStruct_{structName}",
                               new List<Formal> {
                                 AH.MakeFormal("h", "Armada_Heap"),
                                 AH.MakeFormal("p", "Armada_Pointer"),
                                 AH.MakeFormal("value", $"Armada_Struct_{structName}")
                               },
                               h_cur);
          newDefaultClassDecls.Add(fn);
        }

        fnDef = $@"
            function Armada_UpdateChildToStruct_{structName}(h:Armada_Heap, p:Armada_Pointer, field:Armada_Field, value:Armada_Struct_{structName}) : Armada_Heap
            {{
              if p in h.tree && field in h.tree[p].children then Armada_UpdatePointerToStruct_{structName}(h, h.tree[p].children[field], value) else h
            }}
        ";
        newDefaultClassDecls.Add((Function) AH.ParseTopLevelDecl(prog, $"Armada_UpdateChildToStruct_{structName}", fnDef));

        fnDef = $@"
            function Armada_UpdatePointerToStructArray_{structName}(h:Armada_Heap, p:Armada_Pointer, a:seq<Armada_Struct_{structName}>) : Armada_Heap
              decreases |a|
            {{
              if |a| == 0 then
                  h
              else
                  var new_heap := Armada_UpdateChildToStruct_{structName}(h, p, Armada_FieldArrayIndex(|a|-1), a[|a|-1]);
                  Armada_UpdatePointerToStructArray_{structName}(new_heap, p, a[..|a|-1])
            }}
        ";
        newDefaultClassDecls.Add((Function) AH.ParseTopLevelDecl(prog, $"Armada_UpdatePointerToStructArray_{structName}", fnDef));

        fnDef = $@"
            function Armada_UpdateChildToStructArray_{structName}(h:Armada_Heap, p:Armada_Pointer, field:Armada_Field, a:seq<Armada_Struct_{structName}>) : Armada_Heap
            {{
              if p in h.tree && field in h.tree[p].children then Armada_UpdatePointerToStructArray_{structName}(h, h.tree[p].children[field], a) else h
            }}
        ";
        newDefaultClassDecls.Add((Function) AH.ParseTopLevelDecl(prog, $"Armada_UpdateChildToStructArray_{structName}", fnDef));

        var v = AH.MakeNameSegment("v", $"Armada_Struct_{structName}");
        value = AH.MakeNameSegment("value", "Armada_PrimitiveValue");
        var fields = AH.MakeNameSegment("fields", AH.MakeSeqType("Armada_Field"));
        body = v;

        var fields_size = AH.MakeCardinalityExpr(fields);
        var fields_size_gt_0 = AH.MakeGtExpr(fields_size, AH.MakeZero());
        var field0 = AH.MakeSeqSelectExpr(fields, AH.MakeZero(), "Armada_Field");
        var fields1dotdot = AH.MakeSeqSliceExpr(fields, AH.MakeOne(), null);
        Expression cs, v_field, v_field_updated, v_updated;

        foreach (var fieldName in s.FieldNames) {
          var fieldType = s.GetFieldType(fieldName);
          var field0_is_struct = AH.MakeExprDotName(field0, "Armada_FieldStruct?", new BoolType());
          var field0_f = AH.MakeExprDotName(field0, "f", "Armada_FieldType");
          var field0_is_correct_field = AH.MakeExprDotName(field0_f, $"Armada_FieldType_{structName}'{fieldName}?", new BoolType());
          cs = AH.CombineExpressionsWithAnd(new List<Expression>{fields_size_gt_0, field0_is_struct, field0_is_correct_field});
          v_field = AH.MakeExprDotName(v, fieldName, fieldType);
          v_field_updated = AH.GetInvocationOfPerformFieldUpdate(v_field, fields1dotdot, value);
          v_updated = AH.MakeDatatypeUpdateExpr(v, fieldName, v_field_updated);
          body = AH.MakeIfExpr(cs, v_updated, body);
        }
        fn = AH.MakeFunction($"Armada_PerformFieldUpdateForStruct_{structName}",
                             new List<Formal> {
                               AH.MakeFormal("v", $"Armada_Struct_{structName}"),
                               AH.MakeFormal("fields", AH.MakeSeqType("Armada_Field")),
                               AH.MakeFormal("value", "Armada_PrimitiveValue")
                             },
                             body);
        newDefaultClassDecls.Add(fn);

        v = AH.MakeNameSegment("v", AH.MakeSeqType($"Armada_Struct_{structName}"));
        body = AH.MakeNameSegment("v", AH.MakeSeqType($"Armada_Struct_{structName}"));
        var field0_is_array_index = AH.MakeExprDotName(field0, "Armada_FieldArrayIndex?", new BoolType());
        var field0_index = AH.MakeExprDotName(field0, "i", new IntType());
        var field0_ge_0 = AH.MakeGeExpr(field0_index, AH.MakeZero());
        v_field = AH.MakeSeqSelectExpr(v, field0_index, $"Armada_Struct_{structName}");
        var field0_not_too_high = AH.MakeLtExpr(field0_index, AH.MakeCardinalityExpr(v));
        cs = AH.CombineExpressionsWithAnd(new List<Expression>{fields_size_gt_0, field0_is_array_index, field0_ge_0, field0_not_too_high});
        v_field_updated = AH.MakeApply3($"Armada_PerformFieldUpdateForStruct_{structName}", v_field, fields1dotdot, value,
                                        AH.MakeSeqType($"Armada_Struct_{structName}"));
        v_updated = AH.MakeSeqUpdateExpr(v, field0_index, v_field_updated);
        body = AH.MakeIfExpr(cs, v_updated, body);
        fn = AH.MakeFunction($"Armada_PerformFieldUpdateForStructArray_{structName}",
                             new List<Formal> {
                               AH.MakeFormal("v", AH.MakeSeqType($"Armada_Struct_{structName}")),
                               AH.MakeFormal("fields", AH.MakeSeqType("Armada_Field")),
                               AH.MakeFormal("value", "Armada_PrimitiveValue")
                             },
                             body);
        newDefaultClassDecls.Add(fn);
      }

      GenerateTreeStructProperties(m, structs, newDefaultClassDecls);
    }

    public void GenerateTotalState(ModuleDefinition m, ArmadaSymbolTable symbols,
                                   List<MemberDecl> newDefaultClassDecls, List<TopLevelDecl> newTopLevelDecls)
    {
      var listOfPCs = new List<ArmadaPC>{ };
      symbols.AllMethods.AppendAllPCs(listOfPCs);
      var pcDatatypeCtors = listOfPCs.Select(x => AH.MakeDatatypeCtor(x.ToString(), new List<Formal>())).ToList();
      var pc = AH.MakeDatatypeDecl(m, "Armada_PC", pcDatatypeCtors);
      newTopLevelDecls.Add(pc);

      var listOfStackFrames = new List<DatatypeCtor>();
      foreach (var methodName in symbols.MethodNames) {
        listOfStackFrames.Add(CreateMethodStackFrame(methodName, symbols));
      }
      var stack = AH.MakeDatatypeDecl(m, "Armada_StackFrame", listOfStackFrames);
      newTopLevelDecls.Add(stack);

      List<Formal> globalFields = new List<Formal>();
      List<Formal> addrFields = new List<Formal>();
      List<Formal> ghostFields = new List<Formal>();
      List<DatatypeCtor> staticGlobalVars = new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_GlobalStaticVarNone", new List<Formal>()) };
      foreach (var varName in symbols.Globals.VariableNames) {
        var v = symbols.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable) {
          globalFields.Add(AH.MakeFormal(varName, symbols.FlattenType(v.ty)));
          staticGlobalVars.Add(AH.MakeDatatypeCtor($"Armada_GlobalStaticVar_{varName}", new List<Formal>()));
        }
        else if (v is GlobalAddressableArmadaVariable) {
          addrFields.Add(AH.MakeFormal(varName, AH.ReferToType("Armada_Pointer")));
        }
        else if (v is GlobalGhostArmadaVariable) {
          ghostFields.Add(AH.MakeFormal(varName, symbols.FlattenType(v.ty)));
        }
        else {
          AH.PrintError(prog, "Internal error:  variable of unexpected type");
        }
      }

      var dtDecl = AH.MakeDatatypeDecl(m, "Armada_Globals", new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_Globals", globalFields) });
      newTopLevelDecls.Add(dtDecl);

      dtDecl = AH.MakeDatatypeDecl(m, "Armada_GlobalStaticVar", staticGlobalVars);
      newTopLevelDecls.Add(dtDecl);

      dtDecl = AH.MakeDatatypeDecl(m, "Armada_Ghosts", new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_Ghosts", ghostFields) });
      newTopLevelDecls.Add(dtDecl);

      dtDecl = AH.MakeDatatypeDecl(m, "Armada_Addrs", new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_Addrs", addrFields) });
      newTopLevelDecls.Add(dtDecl);

      dtDecl = AH.MakeDatatypeDecl(m, "Armada_StoreBufferLocation", new List<DatatypeCtor> {
          AH.MakeDatatypeCtor("Armada_StoreBufferLocation_Unaddressable",
                              new List<Formal> { AH.MakeFormal("v", "Armada_GlobalStaticVar"),
                                                 AH.MakeFormal("fields", new SeqType(AH.ReferToType("Armada_Field"))) }),
          AH.MakeDatatypeCtor("Armada_StoreBufferLocation_Addressable",
                              new List<Formal> { AH.MakeFormal("p", "Armada_Pointer") })
        });
      newTopLevelDecls.Add(dtDecl);

      dtDecl = AH.MakeDatatypeDecl(m, "Armada_StoreBufferEntry", new List<DatatypeCtor> {
          AH.MakeDatatypeCtor("Armada_StoreBufferEntry",
                              new List<Formal> { AH.MakeFormal("loc", "Armada_StoreBufferLocation"),
                                                 AH.MakeFormal("value", "Armada_PrimitiveValue") })
        });
      newTopLevelDecls.Add(dtDecl);

      var memFormals = new List<Formal>();
      memFormals.Add(AH.MakeFormal("heap", "Armada_Heap"));
      memFormals.Add(AH.MakeFormal("globals", "Armada_Globals"));
      dtDecl = AH.MakeDatatypeDecl(m, "Armada_SharedMemory", new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_SharedMemory", memFormals) });
      newTopLevelDecls.Add(dtDecl);

      var extendedFrameFormals = new List<Formal>();
      extendedFrameFormals.Add(AH.MakeFormal("return_pc", "Armada_PC"));
      extendedFrameFormals.Add(AH.MakeFormal("frame", "Armada_StackFrame"));
      extendedFrameFormals.Add(AH.MakeFormal("new_ptrs", AH.MakePointerSetType()));
      dtDecl = AH.MakeDatatypeDecl(m, "Armada_ExtendedFrame", new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_ExtendedFrame", extendedFrameFormals) });
      newTopLevelDecls.Add(dtDecl);

      var threadFormals = new List<Formal>();
      threadFormals.Add(AH.MakeFormal("pc", "Armada_PC"));
      threadFormals.Add(AH.MakeFormal("top", "Armada_StackFrame"));
      threadFormals.Add(AH.MakeFormal("new_ptrs", AH.MakePointerSetType()));
      threadFormals.Add(AH.MakeFormal("stack", AH.MakeStackType()));
      threadFormals.Add(AH.MakeFormal("storeBuffer", AH.MakeStoreBufferType()));
      dtDecl = AH.MakeDatatypeDecl(m, "Armada_Thread", new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_Thread", threadFormals) });
      newTopLevelDecls.Add(dtDecl);

      var totalFormals = new List<Formal>();
      totalFormals.Add(AH.MakeFormal("stop_reason", "Armada_StopReason"));
      totalFormals.Add(AH.MakeFormal("threads", AH.MakeThreadsType()));
      totalFormals.Add(AH.MakeFormal("mem", "Armada_SharedMemory"));
      totalFormals.Add(AH.MakeFormal("ghosts", "Armada_Ghosts"));
      totalFormals.Add(AH.MakeFormal("addrs", "Armada_Addrs"));

      dtDecl = AH.MakeDatatypeDecl(m, "Armada_TotalState", new List<DatatypeCtor> { AH.MakeDatatypeCtor("Armada_TotalState", totalFormals) });
      newTopLevelDecls.Add(dtDecl);

      GenerateAddressableStaticVariablesPredicates(m, symbols, newDefaultClassDecls);

      GenerateInitPredicate(m, symbols, newTopLevelDecls, newDefaultClassDecls);

      GenerateIsNonyieldingPCPredicate(m, symbols, newDefaultClassDecls);

      GenerateNextBodies(m, symbols, newTopLevelDecls, newDefaultClassDecls);

      string str = @"
          function Armada_UpdatePC(s:Armada_TotalState, tid:Armada_ThreadHandle, pc:Armada_PC) : Armada_TotalState
            requires tid in s.threads
          {
            s.(threads := s.threads[tid := s.threads[tid].(pc := pc)])
          }
      ";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_UpdatePC", str));

      str = @"
          function Armada_UpdateTSFrame(s:Armada_TotalState, tid:Armada_ThreadHandle, frame:Armada_StackFrame) : Armada_TotalState
            requires tid in s.threads
          {
            s.(threads := s.threads[tid := s.threads[tid].(top := frame)])
          }
      ";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_UpdateTSFrame", str));

      str = @"
          function Armada_StoreBufferAppend(buf:seq<Armada_StoreBufferEntry>, entry:Armada_StoreBufferEntry) : seq<Armada_StoreBufferEntry>
          {
            buf + [entry]
          }
      ";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_AppendToThreadStoreBuffer", str));

      str = @"
          function Armada_AppendToThreadStoreBuffer(s:Armada_TotalState, tid:Armada_ThreadHandle, entry:Armada_StoreBufferEntry)
            : Armada_TotalState
            requires tid in s.threads
          {
            s.(threads := s.threads[tid := s.threads[tid].(storeBuffer := Armada_StoreBufferAppend(s.threads[tid].storeBuffer, entry))])
          }
      ";
      newDefaultClassDecls.Add((Function)AH.ParseTopLevelDecl(prog, "Armada_AppendToThreadStoreBuffer", str));
    }

    public void TranslateGlobalInvariants(ModuleDefinition m, ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls,
                                          List<TopLevelDecl> newTopLevelDecls)
    {
      var s = AH.MakeNameSegment("s", "Armada_TotalState");
      foreach (var globalInvariant in symbols.GlobalInvariants.Values) {
        var gid = globalInvariant.Decl;
        var failureReporter = new SimpleFailureReporter(prog);
        var context = new GlobalInvariantResolutionContext(s, symbols, failureReporter, null);
        var bodyRValue = context.ResolveAsRValue(gid.Body);
        if (!failureReporter.Valid)
        {
          continue;
        }

        var stop_reason = AH.MakeExprDotName(s, "stop_reason", "Armada_StopReason");
        var not_stopped = AH.MakeExprDotName(stop_reason, "Armada_NotStopped?", new BoolType());
        Expression antecedent = not_stopped;
        if (bodyRValue.CanCauseUndefinedBehavior) {
          antecedent = AH.MakeAndExpr(antecedent, bodyRValue.UndefinedBehaviorAvoidance.Expr);
        }
        var body = AH.MakeImpliesExpr(antecedent, bodyRValue.Val);

        var predName = $"Armada_GlobalInv_{gid.Name}";
        var formals = new List<Formal> { AH.MakeFormal("s", "Armada_TotalState") };
        var pred = AH.MakePredicate(predName, formals, body);
        newDefaultClassDecls.Add(pred);

        globalInvariant.TranslatedName = predName;
      }
    }

    public void TranslateYieldPredicates(ModuleDefinition m, ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls,
                                         List<TopLevelDecl> newTopLevelDecls)
    {
      var s = AH.MakeNameSegment("s", "Armada_TotalState");
      var s_prime = AH.MakeNameSegment("s'", "Armada_TotalState");

      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var threads_prime = AH.MakeExprDotName(s_prime, "threads", AH.MakeThreadsType());
      var tid_in_threads = AH.MakeInExpr(tid, threads);
      var tid_in_threads_prime = AH.MakeInExpr(tid, threads_prime);
      var req = AH.MakeAndExpr(tid_in_threads, tid_in_threads_prime);

      foreach (var yieldPredicate in symbols.YieldPredicates.Values) {
        var yd = yieldPredicate.Decl;
        var failureReporter = new SimpleFailureReporter(prog);
        var context = new YieldPredicateResolutionContext(s, s_prime, tid, symbols, failureReporter, null);
        var rvalue = context.ResolveAsRValue(yd.Body);
        if (!failureReporter.Valid)
        {
          continue;
        }
        var body = rvalue.CanCauseUndefinedBehavior ? AH.MakeImpliesExpr(rvalue.UndefinedBehaviorAvoidance.Expr, rvalue.Val) : rvalue.Val;

        var predName = $"Armada_YieldPredicate_{yd.Name}";
        var formals = new List<Formal> { AH.MakeFormal("s", "Armada_TotalState"),
                                         AH.MakeFormal("s'", "Armada_TotalState"),
                                         AH.MakeFormal("tid", "Armada_ThreadHandle") };
        var pred = AH.MakePredicateWithReq(predName, formals, req, body);
        newDefaultClassDecls.Add(pred);

        yieldPredicate.TranslatedName = predName;
      }
    }

    public void RemoveProofElements(ModuleDefinition m)
    {
      var declsToRemove = new List<TopLevelDecl>();
      foreach (var d in m.TopLevelDecls)
      {
        if (d is ArmadaProofDecl) {
          declsToRemove.Add(d);
        }
      }
      foreach (TopLevelDecl d in declsToRemove) {
        m.TopLevelDecls.Remove(d);
      }
    }

    private void CreateStructsTranslation(ModuleDefinition m)
    {
      // Put struct and default class into symbols

      var structs = new ArmadaStructs(m.Name);
      var classes = new Dictionary<string, ClassDecl>();
      ClassDecl defaultClass = null;
      foreach (var d in m.TopLevelDecls) {
        if (d is ClassDecl) {
          var c = (ClassDecl)d;
          if (!c.IsDefaultClass) {
            structs.AddClass(prog, c);
          }
          else {
            structs.SetDefaultClass(c);
            defaultClass = c;
          }
        }
        else if (d is RefinementConstraintDecl) {
          structs.AddRefinementConstraint(((RefinementConstraintDecl)d).Body);
        }
      }
      if (!CheckForCyclicStructDefinitions(structs)) {
        return;
      }

      // Create m.ArmadaTranslation to hold state-machine translation.

      var newTopLevelDecls = new List<TopLevelDecl>();
      var newDefaultClassDecls = new List<MemberDecl>();

      CopyMathematicalDefaultClassMembers(defaultClass, newDefaultClassDecls);
      CopyMathematicalTopLevelDecls(m, newTopLevelDecls);
      m.ArmadaStructs = structs;
      m.ArmadaTranslation = new ModuleDefinition(Token.NoToken, m.Name, new List<IToken>(), false, false, false, null, m.Module /* parent */, null, false);
      m.ArmadaIncludes = new List<string>();
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/ArmadaCommonDefinitions.dfy");
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");

      // Start using m.ArmadaTranslation as our new module definition.

      m = m.ArmadaTranslation;

      // Generate the struct-related datatypes and all their attendant definitions

      GenerateStructDatatypesAndFunctions(m, structs, newDefaultClassDecls, newTopLevelDecls);

      // Add headers to the new module.

      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("ArmadaCommonDefinitions", m, true));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_maps_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_seqs_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_option_s", m, false));

      // Add all the definitions we've created to the module.

      m.TopLevelDecls.Add(new DefaultClassDecl(m, newDefaultClassDecls));
      m.TopLevelDecls.AddRange(newTopLevelDecls);
    }

    private void CreateStateMachineTranslation(ModuleDefinition m)
    {
      // Put default class info into symbols

      var symbols = new ArmadaSymbolTable(prog, m.ArmadaStructs);
      var classes = new Dictionary<string, ClassDecl>();
      var membersToRemove = new List<TopLevelDecl>();
      symbols.AddClass(m.ArmadaStructs.DefaultClass, true /* from structs module */);
      foreach (var d in m.TopLevelDecls) {
        if (d is ClassDecl) {
          var c = (ClassDecl)d;
          if (c.IsDefaultClass) {
            symbols.AddClass(c, false /* not from structs module */);
          }
        }
      }
      foreach (var memberToRemove in membersToRemove) {
        m.TopLevelDecls.Remove(memberToRemove);
      }
      if (symbols.DefaultClass == null) {
        AH.PrintError(prog, "No default class found");
        return;
      }

      // Create m.ArmadaTranslation to hold state-machine translation.

      var newTopLevelDecls = new List<TopLevelDecl>();
      var newDefaultClassDecls = new List<MemberDecl>();

      CopyMathematicalDefaultClassMembers(symbols.DefaultClass, newDefaultClassDecls);
      CopyMathematicalTopLevelDecls(m, newTopLevelDecls);
      m.ArmadaSymbols = symbols;
      m.ArmadaTranslation = new ModuleDefinition(Token.NoToken, m.Name, new List<IToken>(), false, false, false, null, m.Module /* parent */, null, false);
      m.ArmadaIncludes = new List<string>();
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/ArmadaCommonDefinitions.dfy");
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/spec/refinement.s.dfy");
      if (symbols.StructsModuleName != null) {
        m.ArmadaIncludes.Add($"{symbols.StructsModuleName}.dfy");
      }

      // Copy the default class members into symbols.DefaultClass, then remove all the methods from m,
      // then start using m.ArmadaTranslation as our new module definition.

      symbols.DefaultClass = new DefaultClassDecl(m.ArmadaTranslation, new List<MemberDecl>(symbols.DefaultClass.Members));
      GetMethods(symbols, symbols.DefaultClass);
      GetMethods(symbols, m.ArmadaStructs.DefaultClass);
      RemoveAllMethods(m);
      m = m.ArmadaTranslation;

      // Create definitions for methods' next routines

      ProcessMethods(symbols, newDefaultClassDecls, newTopLevelDecls);
      CreateTauNext(symbols, newDefaultClassDecls);
      GenerateEnablingConditions(symbols, newDefaultClassDecls);

      // Generate the total state datatype and all its attendant definitions

      GenerateTotalState(m, symbols, newDefaultClassDecls, newTopLevelDecls);

      // Translate global invariants and yield predicates

      TranslateGlobalInvariants(m, symbols, newDefaultClassDecls, newTopLevelDecls);
      TranslateYieldPredicates(m, symbols, newDefaultClassDecls, newTopLevelDecls);

      // Add headers to the new module.

      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("ArmadaCommonDefinitions", m, true));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_maps_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_seqs_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_option_s", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("GeneralRefinementModule", m, false));
      if (symbols.StructsModuleName != null) {
        m.TopLevelDecls.Add(AH.MakeAliasModuleDecl(symbols.StructsModuleName, m, true));
      }

      // Add all the definitions we've created to the module.

      m.TopLevelDecls.Add(new DefaultClassDecl(m, newDefaultClassDecls));
      m.TopLevelDecls.AddRange(newTopLevelDecls);
    }

    private bool CheckTypeReferenceCompilationCompatible(ArmadaSymbolTable symbols, Type type) {
      if (type is SizedArrayType) {
        return CheckTypeReferenceCompilationCompatible(symbols, ((SizedArrayType)type).Arg);
      }
      else if (type is PointerType) {
        return CheckTypeReferenceCompilationCompatible(symbols, ((PointerType)type).Arg);
      }
      if (type is UserDefinedType) {
        var primitiveTypes = new List<string>{"int", "uint8", "uint16", "uint32", "uint64", "int8", "int16", "int32", "int64", "bool"};
        if (primitiveTypes.Contains(type.ToString())) {
          return true;
        }
        else {
          if (symbols.LookupStruct(type.ToString()) != null) {
            return true;
          }
          else {
            AH.PrintWarning(prog, $"Type {type} is not a compilation-compatible type");
            return false;
          }
        }
      }
      else {
        AH.PrintWarning(prog, $"Type {type} is not a compilation-compatible type");
        return false;
      }
    }

    private bool CheckStructCompilationCompatible(ArmadaSymbolTable symbols, ArmadaStruct structType) {
      bool compatible = true;

      foreach (var fieldName in structType.FieldNames) {
        var fieldType = structType.LookupFieldType(fieldName);
        compatible = CheckTypeReferenceCompilationCompatible(symbols, fieldType) && compatible;
      }
      return true;
    }

    private bool CheckExprCompilationCompatible(ArmadaSymbolTable symbols, string methodName, Expression expr, ref int memoryAccess) {
      // shallow check only
      // [integer, boolean, variable, uop, binop, address of, dereference, field read, subscript of array,
      //  null , functional call ]
      var compatible = true;
      foreach (var subExpr in expr.SubExpressions) {
        compatible = CheckExprCompilationCompatible(symbols, methodName, subExpr, ref memoryAccess) && compatible;
      }
      switch (expr) {
        case NegationExpression _:
        case IdentifierExpr _:
        case ParensExpression _:
          break;
        case NameSegment name:
          var varName = name.Name;
          if (symbols.Lookup(methodName, varName) is AddressableArmadaVariable) {
            // Either access to addressable local variable, or any global variable
            // is counted as access to shared memory
          }
          break;
        case LiteralExpr literal:
          if (! (literal.Value == null || literal.Value is BigInteger || literal.Value is BaseTypes.BigDec ||
                 literal.Value is bool)) {
            AH.PrintWarning(prog, expr.tok, $"Literal {literal.Value} is not compilation-compatible");
            compatible = false;
          }
          break;
        case UnaryOpExpr unary:
          if (! (unary.Op == UnaryOpExpr.Opcode.AddressOf || unary.Op == UnaryOpExpr.Opcode.Not ||
                 unary.Op == UnaryOpExpr.Opcode.Dereference)) {
            AH.PrintWarning(prog, expr.tok, $"Unary Operator {unary.Op} is not compilation-compatible");
            compatible = false;
          }
          if (unary.Op == UnaryOpExpr.Opcode.Dereference) {
            ++ memoryAccess;
          }
          break;
        case BinaryExpr binary:
          var allowedList = new List<BinaryExpr.ResolvedOpcode>{
            BinaryExpr.ResolvedOpcode.And, BinaryExpr.ResolvedOpcode.Or,
            BinaryExpr.ResolvedOpcode.EqCommon, BinaryExpr.ResolvedOpcode.NeqCommon,
            BinaryExpr.ResolvedOpcode.Lt, BinaryExpr.ResolvedOpcode.Le,
            BinaryExpr.ResolvedOpcode.Gt, BinaryExpr.ResolvedOpcode.Ge,
            BinaryExpr.ResolvedOpcode.Add, BinaryExpr.ResolvedOpcode.Sub,
            BinaryExpr.ResolvedOpcode.Mul, BinaryExpr.ResolvedOpcode.Div,
            BinaryExpr.ResolvedOpcode.Mod};
          if (! allowedList.Contains(binary.ResolvedOp)) {
            AH.PrintWarning(prog, expr.tok, $"Binary Operator {binary.ResolvedOp} is not compilation-compatible");
            compatible = false;
          }
          break;
        case ApplySuffix AS:
          /* I don't know why this is not filled with resolution results... */
          compatible = CheckExprCompilationCompatible(symbols, methodName, AS.Lhs, ref memoryAccess) && compatible;
          foreach (var subExpr in AS.Args) {
            compatible = CheckExprCompilationCompatible(symbols, methodName, subExpr, ref memoryAccess) && compatible;
          }
          break;
        case SuffixExpr _:
          break;
        case SeqSelectExpr sel:
          if (! sel.SelectOne || ! CheckTypeReferenceCompilationCompatible(symbols, sel.Seq.Type)) {
            AH.PrintWarning(prog, expr.tok, $"This sort of subscript access is not compilation-compatible");
            compatible = false;
          }
          break;
        case MemberSelectExpr sel:
          if (! (sel.Obj is StaticReceiverExpr) && ! CheckTypeReferenceCompilationCompatible(symbols, sel.Obj.Type)) {
            AH.PrintWarning(prog, expr.tok, $"This sort of suffix access is not compilation-compatible");
            compatible = false;
          }
          break;
        default:
          AH.PrintWarning(prog, expr.tok, $"Expression {expr} is not compilation-compatible");
          compatible = false;
          break;
      }

      return compatible;
    }

    private bool CheckListAtomic(IEnumerable<String> inputVariableNames, IEnumerable<Expression> exprs) {
      if (exprs == null) {
        return true;
      }
      else {
        return exprs.All(expr => CheckExprAtomic(inputVariableNames, expr));
      }
    }

    private bool CheckExprAtomic(IEnumerable<String> inputVariableNames, Expression expr) {
      Func<Expression, bool> checkExpr = (e => CheckExprAtomic(inputVariableNames, e));
      Func<IEnumerable<Expression>, bool> checkList = (exprs => CheckListAtomic(inputVariableNames, exprs));
      if (expr == null) {
        return true;
      }

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return checkExpr(e.E);
      }

      if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        return checkList(e.Operands) && checkList(e.PrefixLimits);
      }

      if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        return checkExpr(e.E);
      }

      if (expr is LiteralExpr) {
        return true;
      }

      if (expr is ThisExpr) {
        return false;
      }

      if (expr is MeExpr) {
        // FIXME
        return true;
      }

      if (expr is StoreBufferEmptyExpr) {
        // FIXME
        return true;
      }

      if (expr is IdentifierExpr) {
        return false;
      }

      if (expr is SetDisplayExpr) {
        var e = (SetDisplayExpr)expr;
        return checkList(e.Elements);
      }

      if (expr is MultiSetDisplayExpr) {
        var e = (MultiSetDisplayExpr)expr;
        return checkList(e.Elements);
      }

      if (expr is SeqDisplayExpr) {
        var e = (SeqDisplayExpr)expr;
        return checkList(e.Elements);
      }

      if (expr is MapDisplayExpr) {
        var e = (MapDisplayExpr)expr;
        foreach (var pair in e.Elements) {
          if (! checkExpr(pair.A) || !checkExpr(pair.B)) {
            return false;
          }
        }
        return true;
      }

      if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        return checkList(e.Arguments);
      }

      if (expr is NameSegment) {
        var e = (NameSegment)expr;
        if (inputVariableNames.Contains(e.Name)) {
          return true;
        }
        else {
          return false;
        }
      }

      if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        return checkExpr(e.Lhs);
      }

      if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        return checkExpr(e.Lhs) && checkList(e.Args);
      }

      if (expr is RevealExpr) {
        // FIXME
        return true;
      }

      if (expr is MemberSelectExpr) {
        // FIXME
        return false;
      }

      if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        return checkExpr(e.Seq) && checkExpr(e.E0) && checkExpr(e.E1);
      }

      if (expr is MultiSelectExpr) {
        // FIXME
        return false;
      }

      if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        return checkExpr(e.Seq) && checkExpr(e.Index) && checkExpr(e.Value);
      }

      if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        return checkExpr(e.Root) && checkList(e.Updates.Select(update => update.Item3));
      }

      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        return checkExpr(e.Receiver) && checkList(e.Args);
      }

      if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        // assume functions could not have problem
        return checkList(e.Args);
      }

      if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return checkExpr(e.E);
      }

      if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return checkExpr(e.E);
      }

      if (expr is UnchangedExpr) {
        return false;
      }

      if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        return checkExpr(e.E);
      }

      if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        return checkExpr(e.E);
      }

      if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        return checkExpr(e.E0) && checkExpr(e.E1);
      }

      if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        return checkExpr(e.E0) && checkExpr(e.E1) && checkExpr(e.E2);
      }

      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return checkList(e.RHSs) && checkExpr(e.Body);
      }

      if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        return checkExpr(e.Body) && checkExpr(e.Contract);
      }

      if (expr is ForallExpr) {
        var e = (ForallExpr)expr;
        return checkExpr(e.Range) && checkExpr(e.Term);
      }

      if (expr is ExistsExpr) {
        var e = (ExistsExpr)expr;
        return checkExpr(e.Range) && checkExpr(e.Term);
      }

      if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        return checkExpr(e.Range) && checkExpr(e.Term);
      }

      if (expr is MapComprehension) {
        var e = (SetComprehension)expr;
        return checkExpr(e.Range) && checkExpr(e.Term);
      }

      if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        return checkExpr(e.Range) && checkExpr(e.Body);
      }

      if (expr is WildcardExpr) {
        return false;
      }

      if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return checkExpr(e.E);
      }

      if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return checkExpr(e.Test) && checkExpr(e.Thn) && checkExpr(e.Els);
      }

      if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return checkExpr(e.Source) && checkList(e.Cases.Select(c => c.Body));
      }

      return false;
    }

    protected bool CheckAtomicInitialization(ArmadaSymbolTable symbols, String method, Expression expr) {
      var methodSymbolTable = symbols.GetMethodSymbolTable(method);

      // we should allow use of global ghost variables and functions as well

      var globalVariables = symbols.Globals.VariableNames;
      var globalGhostVariables = globalVariables.Where(name => symbols.Globals.Lookup(name) is GlobalGhostArmadaVariable);

      return CheckExprAtomic(methodSymbolTable.InputVariableNames.Concat(globalGhostVariables).Concat(symbols.AllFunctions), expr);
    }

    private bool CheckMethodCompilationCompatible(ArmadaSymbolTable symbols, string methodName, MethodInfo methodInfo, ArmadaSingleMethodSymbolTable methodSymbols) {
      bool compatible = true;

      // checking return arguments
      if (methodInfo.method.Outs.Count > 1) {
        AH.PrintWarning(prog, methodInfo.method.tok, $"Method {methodInfo.method.Name} have more than one return values");
        compatible = false;
      }

      // check unsupported types
      // all types to check: [Ins, Outs, {variables in body}]
      IEnumerable<Type> allTypes = methodSymbols.AllVariables.Select(v => v.ty);

      compatible = allTypes.All(type => CheckTypeReferenceCompilationCompatible(symbols, type)) && compatible;

      if (Attributes.Contains(methodInfo.method.Attributes, "extern")) {
        return compatible;
      }

      // check unsupported statements
      // [somehow, TSO-bypassing, atomic, yield, assert, assume]
      int memoryAccess;
      bool initStage = true;
      foreach (var stmt in methodInfo.ParsedBody) {
        foreach (var expr in stmt.Stmt.SubExpressions) {
          memoryAccess = 0;
          compatible = CheckExprCompilationCompatible(symbols, methodName, expr, ref memoryAccess) && compatible;

          if (memoryAccess > 1) {
            AH.PrintWarning(prog, expr.tok, "More than one memory access in the expression");
            compatible = false;
          }
        }
        switch (stmt.Stmt) {
          case SomehowStmt somehow:
            AH.PrintWarning(prog, somehow.Tok, "Somehow statement is not compilation-compatible");
            compatible = false;
            break;

          case UpdateStmt update:
            memoryAccess = 0;
            foreach (var expr in update.Lhss.Concat(update.Rhss.SelectMany(rhs => rhs.SubExpressions))) {
              compatible = CheckExprCompilationCompatible(symbols, methodName, expr, ref memoryAccess) && compatible;
            }
            if (memoryAccess > 1) {
              AH.PrintWarning(prog, update.Tok, "More than one memory access in the expression");
              compatible = false;
            }
            if (update.BypassStoreBuffers) {
              AH.PrintWarning(prog, update.Tok, "TSO-bypassing update is not compilation-compatible");
              compatible = false;
            }
            break;
          case VarDeclStmt varDecl:
            memoryAccess = 0;
            foreach (var local in varDecl.Locals) {
              if (symbols.Lookup(methodName, local.Name) is AddressableArmadaVariable) {
                ++ memoryAccess;
              }
            }
            if (varDecl.Update is UpdateStmt initialUpdate) {
              foreach (var expr in initialUpdate.Rhss.SelectMany(rhs => rhs.SubExpressions)) {
                compatible = CheckExprCompilationCompatible(symbols, methodName, expr, ref memoryAccess) && compatible;

                if (! CheckAtomicInitialization(symbols, methodName, expr)) {
                  AH.PrintWarning(prog, expr.tok, "The initialization expression is not atomic");
                  compatible = false;
                }
              }
              if (memoryAccess > 1) {
                AH.PrintWarning(prog, varDecl.Tok, "More than one memory access in the expression");
                compatible = false;
              }
            }
            else if (varDecl.Update != null) {
              AH.PrintWarning(prog, varDecl.Tok, "non-update initialization is not compilation-compatible");
              compatible = false;
            }
            if (varDecl.BypassStoreBuffers) {
              AH.PrintWarning(prog, varDecl.Tok, "TSO-bypassing initialization is not compilation-compatible");
              compatible = false;
            }
            if (! initStage) {
              AH.PrintWarning(prog, varDecl.Tok, "Declaration of variables at non-entry locations is not supported");
              compatible = false;
            }
            break;
          case ExplicitYieldBlockStmt atomic:
            AH.PrintWarning(prog, atomic.Tok, "Explicit-yield block is not compilation-compatible");
            compatible = false;
            break;
          case YieldStmt yieldStmt:
            AH.PrintWarning(prog, yieldStmt.Tok, "Yield statement is not compilation-compatible");
            compatible = false;
            break;
          case AssertStmt assert:
            AH.PrintWarning(prog, assert.Tok, "Assert statement is not compilation-compatible");
            compatible = false;
            break;
          case AssumeStmt assume:
            AH.PrintWarning(prog, assume.Tok, "Assume statement is not compilation-compatible");
            compatible = false;
            break;
        }
        initStage = initStage && (stmt.Stmt is VarDeclStmt || stmt.Stmt is BlockStmt);
      }

      return compatible;
    }

    private bool CheckCompilationCompatible(ArmadaSymbolTable symbols) {
      bool compatible = true;

      // check all structs
      foreach (var structName in symbols.StructNames) {
        CheckStructCompilationCompatible(symbols, symbols.LookupStruct(structName));
      }

      // check each method
      foreach (var methodName in symbols.AllMethods.AllMethodNames) {
        var methodInfo = symbols.AllMethods.LookupMethod(methodName);
        var methodSymbols = symbols.GetMethodSymbolTable(methodName);
        compatible = compatible && CheckMethodCompilationCompatible(symbols, methodName, methodInfo, methodSymbols);
      }

      return compatible;
    }

    internal override void PreResolve(ModuleDefinition m) {
      if (m.ModuleType == ArmadaModuleType.ArmadaProof) {
        RemoveProofElements(m);
      }
    }

    internal override void PostResolve(ModuleDefinition m) {
      if (m.ModuleType == ArmadaModuleType.ArmadaStructs) {

        CreateStructsTranslation(m);
        // TODO(xueyuanz): We should only add the structs that is used by the concrete layer later.
        prog.CompileModules.Add(m);
      }
      else if (m.ModuleType == ArmadaModuleType.ArmadaLevel) {
        CreateStateMachineTranslation(m);
        // take use of existing parsing information
        if (Attributes.Contains(m.Attributes, "concrete")) {

          if (! CheckCompilationCompatible(m.ArmadaSymbols)) {
            AH.PrintError(prog, $"Level {m.Name} is attributed {{:concrete}} but fails the check");
            return;
          }
          prog.CompileModules.Add(m);
        }
      }
    }

    private void CopyMathematicalDefaultClassMembers(ClassDecl defaultClass, List<MemberDecl> newDefaultClassDecls)
    {
      foreach (var m in defaultClass.Members) {
        if (m is Function || m is Lemma && ! m.Name.StartsWith("reveal_")) { // fix for duplicate export of opaque functions
          newDefaultClassDecls.Add(m);
        }
      }
    }

    private void CopyMathematicalTopLevelDecls(ModuleDefinition m, List<TopLevelDecl> newTopLevelDecls)
    {
      foreach (var d in m.TopLevelDecls) {
        if (d is DatatypeDecl || d is NewtypeDecl || d is TypeSynonymDecl) {
          newTopLevelDecls.Add(d);
        }
      }
    }
  }
}
