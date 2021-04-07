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

    public bool CheckForConcreteStructDefinition(ArmadaStruct s, ArmadaStructs structs)
    {
      foreach (var fieldName in s.FieldNames) {
        var t = s.GetFieldType(fieldName);
        if (!AH.IsValidHeapType(t, structs)) {
          AH.PrintError(prog, $"Struct {s.Name} has a field {fieldName} of type {t}, which is neither a primitive type nor a struct type.");
          return false;
        }
      }
      return true;
    }

    public bool CheckForConcreteStructDefinitions(ArmadaStructs structs)
    {
      foreach (var structName in structs.StructNames) {
        var s = structs.GetStruct(structName);
        if (!CheckForConcreteStructDefinition(s, structs)) {
          return false;
        }
      }
      return true;
    }

    public bool CheckForCyclicStructDefinition(ArmadaStruct outer, ArmadaStruct inner, ArmadaStructs structs) {
      foreach (var fieldName in inner.FieldNames) {
        var t = inner.GetFieldType(fieldName);
        if (t is UserDefinedType u) {
          if (u.Name == outer.Name) {
            AH.PrintError(prog, $"Struct {outer.Name} has a cyclic dependency on itself, specifically in field {fieldName} of component {inner.Name}");
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

    public void CreateMethodStackFrame(string methodName, ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      var smst = symbols.GetMethodSymbolTable(methodName);
      var varFormals = smst.AllVariablesInOrder.Select(v => $"{v.FieldName}: {v.GetFlattenedType(symbols).ToString()}");
      declCollector.AddItem($@"
        datatype Armada_StackVars_{methodName} = Armada_StackVars_{methodName}({AH.CombineStringsWithCommas(varFormals)})
      ");
    }

    public void ParseMethodWithBody(Program prog, MethodInfo methodInfo, ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      var method = methodInfo.method;

      if (method.Awaits.Count > 0) {
        AH.PrintError(prog, method.tok, "Awaits clauses can't appear except in body-less methods");
        return;
      }

      methodInfo.ParseMethodBody(symbols);
    }

    public void CreateNextRoutinesForMethodWithNoBodyPart1(ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                           DeclCollector declCollector, ArmadaPC startPC, ArmadaPC midPC)
    {
      //
      // The first next routine to generate is...
      //   start->middle:   find that the awaits clauses are satisfied, then havoc the write set, then
      //                    read each element in the read set into Armada_Extern local variables
      //

      var method = methodInfo.method;
      var next = new NextRoutineConstructor(prog, symbols, NextType.ExternStart, methodInfo, null, null, startPC, midPC);
      method.externStartNextRoutineConstructor = next;
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
        next.AddUBAvoidanceConstraintAsDefinedBehaviorConjunct(await_clause_resolved.UndefinedBehaviorAvoidance);
        next.AddDefinedBehaviorConjunct(await_clause_resolved.Val);
      }

      // Add each undefined_unless clause as an undefined-behavior constraint, to model that the
      // method's behavior is undefined if its undefined_unless constraints aren't met at the outset.

      foreach (var undefined_unless_clause in method.UndefinedUnless) {
        var uuc = read_context.ResolveAsRValue(undefined_unless_clause);
        next.AddUndefinedBehaviorAvoidanceConstraint(uuc.UndefinedBehaviorAvoidance);
        next.AddUndefinedBehaviorAvoidanceConstraint(uuc.Val);
      }

      // Compute each s{i+1} by updating a single modifies element in s{i}.

      var s_current = next.s;
      for (int i = 0; i < modifies.Count; ++i) {
        var lhs = modifies.ElementAt(i).E;

        var nextFormal = new NextFormal($"newval{i}_{startPC}", $"newval{i}", lhs.Type, symbols);
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
        var current_context = new NormalResolutionContext(s_current, next, symbols);
        var newLhs = current_context.ResolveAsLValue(lhs);
        if (!(newLhs is ArmadaLValue)) {
          next.Fail(lhs.tok, "Modifies element is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        s_current = Attributes.Contains(method.Mod.Attributes, "tso") ?
          newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, newRhs, startPC) :
          newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, newRhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      if (reads.Count > 0) {
        // s_current := Armada_UpdateTSFrame(
        //    s_current, tid,
        //    Armada_StackFrame_{method.Name}(s_current.threads[tid].top.{method.Name}.(Armada_Extern0 := ..., Armada_Extern1 := ...))
        // );

        var locv_current = next.AddVariableDeclaration("locv", $"Armada_GetThreadLocalView({s_current}, {next.tid})");
        // The top stack frame hasn't changed since the beginning, since nothing we modify is on the stack
        var top = read_context.GetRValueTopStackFrame();
        next.AddUndefinedBehaviorAvoidanceConstraint($"({top}).Armada_StackFrame_{method.Name}?");
        var current_context = new CustomResolutionContext(s_current, s_current, locv_current, top, $"{s_current}.ghosts",
                                                          next.tid, method.Name, symbols, next);

        var updates = new List<string>();
        for (int i = 0; i < reads.Count; ++i) {
          var read_expr = reads.ElementAt(i);
          var read_val = current_context.ResolveAsRValue(read_expr);
          next.AddUndefinedBehaviorAvoidanceConstraint(read_val.UndefinedBehaviorAvoidance);
          updates.Add($"Armada_Extern{i} := {read_val.Val}");
        }

        var top_vars = $"({top}).{method.Name}";
        if (updates.Any()) {
          top_vars += ".(" + String.Join(", ", updates) + ")";
        }
        s_current = $"Armada_UpdateTSFrame({s_current}, {next.tid}, Armada_StackFrame_{method.Name}({top_vars}))";
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      // s_current := Armada_UpdatePC(s_current, tid, midPC);

      s_current = $"Armada_UpdatePC({s_current}, {next.tid}, {midPC})";
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);
      symbols.AddNextRoutineConstructor(next);
    }

    public void CreateNextRoutinesForMethodWithNoBodyPart2(ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                           DeclCollector declCollector, ArmadaPC midPC)
    {
      //
      // The second next routine to generate is...
      //   middle->middle:  crash if anything in the read set doesn't match the Armada_Extern variables,
      //                    then havoc the write set, then read each element in the read set into
      //                    Armada_Extern local variables

      var method = methodInfo.method;
      var next = new NextRoutineConstructor(prog, symbols, NextType.ExternContinue, methodInfo, null, null, midPC, midPC);
      method.externContinueNextRoutineConstructor = next;
      var read_context = new NormalResolutionContext(next, symbols);
      List<FrameExpression> modifies = method.Mod.Expressions ?? new List<FrameExpression>();
      List<Expression> reads = method.Reads.Expressions ?? new List<Expression>();

      // Crash if, for any element in the read set, the current value of that element doesn't
      // match the corresponding element of the latest snapshot.

      next.AddUndefinedBehaviorAvoidanceConstraint($"({next.t}).top.Armada_StackFrame_{method.Name}?");

      for (int i = 0; i < reads.Count; ++i) {
        var read_expr = reads.ElementAt(i);
        var current_val = read_context.ResolveAsRValue(read_expr);
        next.AddUndefinedBehaviorAvoidanceConstraint(current_val.UndefinedBehaviorAvoidance);
        next.AddUndefinedBehaviorAvoidanceConstraint($"({current_val.Val}) == ({next.t}).top.{method.Name}.Armada_Extern{i}");
      }

      // Compute each s{i+1} by updating a single modifies element in s{i}.

      var s_current = next.s;
      for (int i = 0; i < modifies.Count; ++i) {
        var lhs = modifies.ElementAt(i).E;

        var nextFormal = new NextFormal($"newval{i}_{midPC}", $"newval{i}", lhs.Type, symbols);
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
        var current_context = new NormalResolutionContext(s_current, next, symbols);
        var newLhs = current_context.ResolveAsLValue(lhs);
        if (!(newLhs is ArmadaLValue)) {
          next.Fail(lhs.tok, "Modifies element is not a valid lvalue");
          return;
        }
        next.AddUndefinedBehaviorAvoidanceConstraint(newLhs.GetUndefinedBehaviorAvoidanceConstraint());

        s_current = Attributes.Contains(method.Mod.Attributes, "tso") ?
          newLhs.UpdateTotalStateWithStoreBufferEntry(current_context, next, newRhs, midPC) :
          newLhs.UpdateTotalStateBypassingStoreBuffer(current_context, next, newRhs);
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      if (reads.Count > 0) {
        // s_current := Armada_UpdateTSFrame(
        //    s_current, tid,
        //    Armada_StackFrame_{method.Name}(s_current.threads[tid].top.{method.Name}.(Armada_Extern0 := ..., Armada_Extern1 := ...))
        // );

        var locv_current = next.AddVariableDeclaration("locv", $"Armada_GetThreadLocalView({s_current}, {next.tid})");
        var ghosts_current = $"{s_current}.ghosts";
        var top_current = $"{s_current}.threads[{next.tid}].top";
        var current_context = new CustomResolutionContext(s_current, s_current, locv_current, top_current, ghosts_current,
                                                          next.tid, method.Name, symbols, next);

        var updates = new List<string>();
        for (int i = 0; i < reads.Count; ++i) {
          var read_expr = reads.ElementAt(i);
          var read_val = current_context.ResolveAsRValue(read_expr);
          next.AddUndefinedBehaviorAvoidanceConstraint(read_val.UndefinedBehaviorAvoidance);
          updates.Add($"Armada_Extern{i} := {read_val.Val}");
        }

        var top_vars = $"({next.t}).top.{method.Name}";
        if (updates.Any()) {
          top_vars += ".(" + String.Join(", ", updates) + ")";
        }
        s_current = $"Armada_UpdateTSFrame({s_current}, {next.tid}, Armada_StackFrame_{method.Name}({top_vars}))";
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      next.SetNextState(s_current);
      symbols.AddNextRoutineConstructor(next);
    }

    public void CreateNextRoutinesForMethodWithNoBodyPart3(ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                           DeclCollector declCollector, ArmadaPC midPC, ArmadaPC endPC)
    {
      //
      // The third next routine to generate is...
      //   middle->end:     find that the post-condition is satisfied and append log elements
      //

      var method = methodInfo.method;
      var next = new NextRoutineConstructor(prog, symbols, NextType.ExternEnd, methodInfo, null, null, midPC, endPC);
      method.externEndNextRoutineConstructor = next;
      var read_context = new BodylessMethodPostconditionResolutionContext(next, symbols);

      foreach (var ensure_raw in method.Ens) {
        var ensure_resolved = read_context.ResolveAsRValue(ensure_raw.E);
        next.AddUBAvoidanceConstraintAsDefinedBehaviorConjunct(ensure_resolved.UndefinedBehaviorAvoidance);
        next.AddDefinedBehaviorConjunct(ensure_resolved.Val);
      }

      var s_current = next.s;

      // s_current := Armada_UpdatePC(s_current, tid, endPC);

      s_current = $"Armada_UpdatePC({s_current}, {next.tid}, {endPC})";
      s_current = next.AddVariableDeclaration("s", s_current);

      next.SetNextState(s_current);
      symbols.AddNextRoutineConstructor(next);
    }

    public void ParseMethodWithNoBody(Program prog, MethodInfo methodInfo, ArmadaSymbolTable symbols, DeclCollector declCollector)
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

      // Set the return PC.

      methodInfo.SetReturnPC(endPC);
    }

    public void CreateNextRoutinesForMethodWithNoBody(Program prog, ArmadaSymbolTable symbols, MethodInfo methodInfo,
                                                      DeclCollector declCollector)
    {
      var methodName = methodInfo.method.Name;
      var startPC = new ArmadaPC(symbols, methodName, 0);
      var midPC = new ArmadaPC(symbols, methodName, 1);
      var endPC = new ArmadaPC(symbols, methodName, 2);

      // Generate the next routines for the three transitions.

      CreateNextRoutinesForMethodWithNoBodyPart1(symbols, methodInfo, declCollector, startPC, midPC);
      CreateNextRoutinesForMethodWithNoBodyPart2(symbols, methodInfo, declCollector, midPC);
      CreateNextRoutinesForMethodWithNoBodyPart3(symbols, methodInfo, declCollector, midPC, endPC);
    }

    public void CreateNextTerminateThread(ArmadaSymbolTable symbols, MethodInfo methodInfo)
    {
      var returnPC = methodInfo.ReturnPC;
      var terminatingProcess = methodInfo.method.Name.Equals("main");
      var next = new NextRoutineConstructor(prog, symbols, terminatingProcess ? NextType.TerminateProcess : NextType.TerminateThread,
                                            methodInfo, null, null, returnPC, null);
      methodInfo.method.terminateNextRoutineConstructor = next;

      var s = $"({next.s})";
      var t = $"({next.t})";

      // |t.stack| == 0

      next.AddConjunct($"|{t}.stack| == 0");

      // The thread's store buffer contents should be flushed before termination, i.e.,
      // |t.storeBuffer| == 0

      next.AddConjunct($"|{t}.storeBuffer| == 0");

      // s_current := s.(threads := (map other | other in s.threads && other != tid :: s.threads[other]),
      //                 joinable_tids := s.joinable_tids + {tid})

      var s_current = $@"
        {s}.(threads := (map other | other in {s}.threads && other != {next.tid} :: {s}.threads[other]),
                         joinable_tids := {s}.joinable_tids + {{ {next.tid} }})
      ";
      s_current = next.AddVariableDeclaration("s", s_current);

      // Now, we need to free the new_ptrs.  In Dafny, if we denote s_current by s, that's:
      //
      // s := s.(mem := s.mem.(heap := s.mem.heap.(valid := s.mem.heap.valid - t.new_ptrs,
      //                                           freed := s.mem.heap.freed + t.new_ptrs)))

      s = s_current;
      s_current = $@"
        {s}.(mem := {s}.mem.(heap := {s}.mem.heap.(valid := {s}.mem.heap.valid - {t}.new_ptrs,
                                                   freed := {s}.mem.heap.freed + {t}.new_ptrs)))
      ";
      s_current = next.AddVariableDeclaration("s", s_current);

      // Finally, we need to set the stop_reason to Armada_StopReasonTerminated if the terminated
      // thread was the main thread.

      if (terminatingProcess) {
        s_current = $"{s_current}.(stop_reason := Armada_StopReasonTerminated)";
        s_current = next.AddVariableDeclaration("s", s_current);
      }

      next.SetNextState(s_current);
      symbols.AddNextRoutineConstructor(next);
    }

    public void ProcessMethods(ArmadaSymbolTable symbols, DeclCollector declCollector)
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
          ParseMethodWithNoBody(prog, methodInfo, symbols, declCollector);
        }
        else {
          ParseMethodWithBody(prog, methodInfo, symbols, declCollector);
        }
        if (Attributes.Contains(method.Attributes, "atomic")) {
          if (method.Name == "main") {
            AH.PrintWarning(prog, "Ignoring :atomic on main, since main can't use atomic calls and returns");
          }
          else {
            methodInfo.UseAtomicCallsAndReturns();
          }
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
          CreateNextRoutinesForMethodWithNoBody(prog, symbols, methodInfo, declCollector);
        }
        else {
          methodInfo.ParsedBody.GenerateNextRoutines();
        }
      }

      foreach (var methodName in symbols.GetThreadRoutines()) {
        var methodInfo = symbols.AllMethods.LookupMethod(methodName);
        CreateNextTerminateThread(symbols, methodInfo);
      }
    }

    private string GetStructFieldUpdate(Type innerType, int numArrayDimensions, string currentValue, int currentField)
    {
      if (numArrayDimensions == 0) {
        if (AH.IsPrimitiveType(innerType)) {
          return $"value.n_{innerType}";
        }
        else if (innerType is UserDefinedType ut) {
          return $"Armada_UpdateStruct_{ut.Name}({currentValue}, fields[{currentField}..], value)";
        }
        else {
          AH.PrintError(prog, $"Invalid type {innerType}");
          return currentValue;
        }
      }
      else {
        var subfieldUpdate = GetStructFieldUpdate(innerType, numArrayDimensions - 1,
                                                  $"{currentValue}[fields[{currentField}]]", currentField + 1);
        return $"{currentValue}[fields[{currentField}] := {subfieldUpdate}]";
      }
    }

    private string GetGlobalsUpdateConstraints(Type innerType, int numArrayDimensions, string value)
    {
      var constraints = new List<string>();
      if (AH.IsPrimitiveType(innerType)) {
        constraints.Add($"|fields| == {numArrayDimensions}");
      }
      else {
        constraints.Add($"|fields| >= {numArrayDimensions}");
      }
      for (int i = 0; i < numArrayDimensions; ++i) {
        constraints.Add($"0 <= fields[{i}] < |{value}|");
        value += $"[fields[{i}]]";
      }
      if (AH.IsPrimitiveType(innerType)) {
        constraints.Add($"value.Armada_PrimitiveValue_{innerType}?");
      }
      return AH.CombineStringsWithAnd(constraints);
    }

    public void CreateApplyTauUnaddressableFunction(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      var caseBodies = "";

      foreach (var varName in symbols.Globals.VariableNames) {
        var gv = symbols.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          Type innerType;
          var numArrayDimensions = AH.GetNumArrayDimensions(gv.ty, out innerType);
          var globalsDotVarName = $"globals.{varName}";
          caseBodies += $@"
            case Armada_GlobalStaticVar_{varName} =>
              if {GetGlobalsUpdateConstraints(innerType, numArrayDimensions, globalsDotVarName)} then
                globals.({varName} := {GetStructFieldUpdate(innerType, numArrayDimensions, globalsDotVarName, 0)})
              else
                globals
          ";
        }
      }

      caseBodies += "case Armada_GlobalStaticVarNone => globals\n";
      declCollector.AddItem($@"
        function Armada_ApplyTauUnaddressable(globals: Armada_Globals, v: Armada_GlobalStaticVar, fields: seq<int>,
                                              value: Armada_PrimitiveValue) : Armada_Globals
        {{
          match v
            {caseBodies}
        }}
      ");
    }

    public void CreateApplyTauAddressableFunction(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      declCollector.AddItem(@"
        function Armada_ApplyTauAddressable(h: Armada_Heap, p: Armada_Pointer, value: Armada_PrimitiveValue) : (h': Armada_Heap)
          ensures Armada_HeapMetadataUnchangedByTau(h, h')
        {
          if && p in h.valid
             && p in h.tree
             && p in h.values
             && h.tree[p].ty.Armada_ObjectTypePrimitive?
             && Armada_PrimitiveValueMatchesType(value, h.tree[p].ty.pty)
          then
            h.(values := Armada_UpdateHeapValuesWithPrimitiveValue(h.values, p, value))
          else
            h
        }
      ");
    }

    public void CreateHeapMetadataUnchangedByTau(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      declCollector.AddItem(@"
        predicate Armada_HeapMetadataUnchangedByTau(h: Armada_Heap, h': Armada_Heap)
        {
          && h'.valid == h.valid
          && h'.tree == h.tree
          && h'.freed == h.freed
        }
      ");
    }

    public void CreateTauNext(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      CreateHeapMetadataUnchangedByTau(symbols, declCollector);
      CreateApplyTauUnaddressableFunction(symbols, declCollector);
      CreateApplyTauAddressableFunction(symbols, declCollector);

      declCollector.AddItem(@"
        function Armada_ApplyStoreBufferEntry(mem: Armada_SharedMemory, entry: Armada_StoreBufferEntry) : (mem':Armada_SharedMemory)
          ensures Armada_HeapMetadataUnchangedByTau(mem.heap, mem'.heap)
        {
          match entry.loc
              case Armada_StoreBufferLocation_Unaddressable(v, fields) =>
                mem.(globals := Armada_ApplyTauUnaddressable(mem.globals, v, fields, entry.value))
              case Armada_StoreBufferLocation_Addressable(p) =>
                mem.(heap := Armada_ApplyTauAddressable(mem.heap, p, entry.value))
        }
      ");

      declCollector.AddItem(@"
        function Armada_ApplyStoreBuffer(mem: Armada_SharedMemory, storeBuffer: seq<Armada_StoreBufferEntry>) : (mem':Armada_SharedMemory)
          ensures Armada_HeapMetadataUnchangedByTau(mem.heap, mem'.heap)
          decreases |storeBuffer|
        {
          if |storeBuffer| == 0 then
            mem
          else
            Armada_ApplyStoreBuffer(Armada_ApplyStoreBufferEntry(mem, storeBuffer[0]), storeBuffer[1..])
        }
      ");

      declCollector.AddItem(@"
        function Armada_GetThreadLocalView(s: Armada_TotalState, tid: Armada_ThreadHandle) : (mem':Armada_SharedMemory)
          requires tid in s.threads
          ensures  Armada_HeapMetadataUnchangedByTau(s.mem.heap, mem'.heap)
        {
          Armada_ApplyStoreBuffer(s.mem, s.threads[tid].storeBuffer)
        }
      ");

      var next = new NextRoutineConstructor(prog, symbols, NextType.Tau, null, null, null, null, null);
      symbols.TauNextRoutineConstructor = next;

      var s = $"({next.s})";
      var t = $"({next.t})";

      // Add conjunct |t.storeBuffer| > 0:

      next.AddConjunct($"|{t}.storeBuffer| > 0");

      // Get an expression for the correct final state, which involves popping the first store-buffer entry
      // and applying it to memory.

      var s_updated = $@"
        {s}.(threads := {s}.threads[{next.tid} := {t}.(storeBuffer := {t}.storeBuffer[1..])],
             mem := Armada_ApplyStoreBufferEntry({s}.mem, {t}.storeBuffer[0]))
      ";
      next.SetNextState(s_updated);
      symbols.AddNextRoutineConstructor(next);
    }

    public void GenerateEnablingConditions(ArmadaSymbolTable symbols, DeclCollector declCollector)
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

          declCollector.AddItem($@"
            predicate Armada_EnablingConditions_{pc}(s: Armada_TotalState, tid: Armada_ThreadHandle)
              requires tid in s.threads
              requires s.threads[tid].top.Armada_StackFrame_{methodName}?
            {{
              {collector.Extract()}
            }}
          ");
        }
      }
    }

    public void GenerateAddressableStaticVariablesPredicates(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      // Every addressable global variable is a root of the heap

      var root_preds = new List<string>();
      var validity_preds = new List<string>();

      var previouslySeenAddressableVariableAddrs = new List<string>();
      foreach (var varName in symbols.Globals.VariableNames) {
        var v = symbols.Globals.Lookup(varName);
        if (v is AddressableArmadaVariable) {
          var addr = $"s.addrs.{varName}";
          foreach (var otherAddr in previouslySeenAddressableVariableAddrs) {
            root_preds.Add($"{addr} != {otherAddr}");
          }
          previouslySeenAddressableVariableAddrs.Add(addr);
          var pointer_valid = AH.GetInvocationOfValidPointer("h", addr, v.ty);
          if (pointer_valid is null) {
            AH.PrintError(prog, $"Invalid type for static variable {varName}");
          }
          else {
            validity_preds.Add(pointer_valid);
          }
          root_preds.Add($"{addr} in h.tree");
          root_preds.Add($"h.tree[{addr}].child_type.Armada_ChildTypeRoot?");
          root_preds.Add($"h.tree[{addr}].child_type.rt.Armada_RootTypeStaticHeap?");
        }
      }

      var root_pred_list = AH.CombineStringsWithAnd(root_preds);
      declCollector.AddItem($@"
        predicate Armada_AddressableStaticVariablesAreDistinctRoots(s: Armada_TotalState)
        {{
          var h := s.mem.heap;
          {root_pred_list}
        }}
      ");

      var validity_pred_list = AH.CombineStringsWithAnd(validity_preds);
      declCollector.AddItem($@"
        predicate Armada_AddressableStaticVariablesAreValid(s: Armada_TotalState, new_ptrs: set<Armada_Pointer>)
        {{
          var h := s.mem.heap.(valid := s.mem.heap.valid - new_ptrs);
          {validity_pred_list}
        }}
      ");
    }

    public void GenerateInitPredicate(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      var builder = new PredicateBuilder(prog, true);

      builder.AddConjunct("s.stop_reason.Armada_NotStopped?");
      builder.AddConjunct("|s.joinable_tids| == 0");
      builder.AddConjunct("util_collections_maps_i.MapHasUniqueKey(s.threads, config.tid_init)");
      builder.AddConjunct("config.tid_init != 0");

      // var tid := config.tid_init;
      // var new_ptrs := config.new_ptrs;
      // var t := s.threads[tid];
      var tid = builder.AddVariableDeclaration("tid", "config.tid_init");
      var new_ptrs = builder.AddVariableDeclaration("new_ptrs", "config.new_ptrs");
      var t = builder.AddVariableDeclaration("t", "s.threads[tid]");

      // t.pc.Armada_PC_main_Start?
      var startPC = new ArmadaPC(symbols, "main", 0);
      builder.AddConjunct($"t.pc.{startPC}?");

      builder.AddConjunct("t.top.Armada_StackFrame_main?");
      builder.AddConjunct("t.new_ptrs == new_ptrs");
      builder.AddConjunct("|t.stack| == 0");
      builder.AddConjunct("|t.storeBuffer| == 0");

      // For each addressable stack variable in the main stack frame, it's valid and among new_ptrs

      var smst = symbols.GetMethodSymbolTable("main");
      string p_in_new_ptrs = "";
      List<string> addressesOfAddressables = new List<string>();
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.varType == ArmadaVarType.Local && v is AddressableArmadaVariable))
      {
        var new_ptr = $"t.top.main.AddrOf'{v.name}";

        // new_ptr is among new_ptrs

        builder.AddConjunct($"{new_ptr} in new_ptrs");

        // new_ptr is in s.mem.heap.tree

        builder.AddConjunct($"{new_ptr} in s.mem.heap.tree");

        // new_ptr is a stack-based root in s.mem.heap, i.e.,
        //    && s.mem.heap.tree[new_ptr].child_type.Armada_ChildTypeRoot?
        //    && s.mem.heap.tree[new_ptr].child_type.rt.Armada_RootTypeStack?

        builder.AddConjunct($"s.mem.heap.tree[{new_ptr}].child_type.Armada_ChildTypeRoot?");
        builder.AddConjunct($"s.mem.heap.tree[{new_ptr}].child_type.rt.Armada_RootTypeStack?");

        // new_ptr is a valid pointer in s.mem.heap

        builder.AddConjunct(AH.GetInvocationOfValidPointer("s.mem.heap", new_ptr, v.ty));

        var allocatedByExpr = AH.GetInvocationOfDescendants("s.mem.heap", $"t.top.main.AddrOf'{v.name}", v.ty);
        p_in_new_ptrs += $"|| p in {allocatedByExpr}";
        addressesOfAddressables.Add($"t.top.main.AddrOf'{v.name}");
      }

      if (p_in_new_ptrs.Length > 0) {
        builder.AddConjunct($"forall p :: p in new_ptrs <==> ({p_in_new_ptrs})");
      }
      else {
        builder.AddConjunct("|new_ptrs| == 0");
      }

      for (int i = 0; i < addressesOfAddressables.Count; i++) {
        for (int j = i + 1; j < addressesOfAddressables.Count; j++) {
          builder.AddConjunct(addressesOfAddressables[i] + " != " + addressesOfAddressables[j]);
        }
      }

      // Initialize stack variables in main
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.InitialValue != null))
      {
        var resContext = new ResolutionContext("s", "s", "tid", "main", symbols, null);
        var lhsRVal = resContext.ResolveAsRValue(AH.MakeNameSegment(v.name, symbols.FlattenType(v.ty)));
        var rhsRVal = resContext.ResolveAsRValue(v.InitialValue);
        builder.AddConjunct($"({lhsRVal.Val}) == ({rhsRVal.Val})");
      }

      // The global static variables are valid, even if new_ptrs are excluded from the list of valid pointers.

      builder.AddConjunct("Armada_AddressableStaticVariablesAreValid(s, new_ptrs)");

      // The global static variables are roots.

      builder.AddConjunct("Armada_AddressableStaticVariablesAreDistinctRoots(s)");

      // Armada_HeapInvariant(s.mem.heap)

      builder.AddConjunct("Armada_HeapInvariant(s.mem.heap)");

      // Any global variable is initialized appropriately: if it's an
      // unaddressable array, it has the right length, and if it has
      // an initializer then it has that value.

      var failureReporter = new SimpleFailureReporter(prog);
      var context = new GlobalInvariantResolutionContext("s", symbols, failureReporter, "");
      foreach (var globalVariableName in symbols.Globals.VariableNames) {
        var globalVar = symbols.Globals.Lookup(globalVariableName);
        if (globalVar is GlobalUnaddressableArmadaVariable && globalVar.ty is SizedArrayType) {
          var gv_expr = globalVar.GetRValue(Token.NoToken, context);
          var sz = ((SizedArrayType)globalVar.ty).Size;
          builder.AddConjunct($"|{gv_expr.Val}| == ({Printer.ExprToString(sz)})");
        }
        if (globalVar.initialValue != null) {
          var gv_expr = globalVar.GetRValue(Token.NoToken, context);
          var val_expr = context.ResolveAsRValue(globalVar.initialValue);
          //
          // We don't crash if these rvalues aren't valid, since we can't crash at init time.
          // Instead, we just generate Dafny that won't satisfy validity checks if that's an issue.
          //
          builder.AddConjunct($"({gv_expr.Val}) == ({val_expr.Val})");
        }
      }

      declCollector.AddItem($@"
        predicate Armada_InitConfig(s: Armada_TotalState, config: Armada_Config)
        {{
          {builder.Extract()}
        }}
      ");

      declCollector.AddItem(@"
        predicate Armada_Init(s:Armada_TotalState)
        {
          exists config :: Armada_InitConfig(s, config)
        }
      ");
    }

    public void GenerateIsNonyieldingPCPredicate(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      var nonyieldingPCs = new List<ArmadaPC>();
      symbols.AllMethods.AppendAllNonyieldingPCs(nonyieldingPCs);

      string body = AH.CombineStringsWithOr(nonyieldingPCs.Select(pc => $"pc.{pc}?"));
      declCollector.AddItem($@"
        predicate Armada_IsNonyieldingPC(pc:Armada_PC)
        {{
          {body}
        }}
      ");
    }

    public void GenerateNextBodies(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      var stepCtors = new List<string>();
      foreach (var nrc in symbols.NextRoutineConstructors) {
        nrc.Extract(symbols, declCollector, stepCtors);
      }
      symbols.ClearNextRoutineConstructors();

      if (stepCtors.Count() == 0) {
        return;
      }

      var stepDecl = "datatype Armada_Step = " + String.Join(" | ", stepCtors);
      declCollector.AddItem(stepDecl);

      var pr = new StepPrinter();
      var matchBody = String.Concat(symbols.NextRoutines.Select(r => $"{pr.CaseEntry(r)} => {pr.ValidStepInvocation(r)}\n"));
      declCollector.AddItem($@"
        predicate {{:opaque}} Armada_ValidStepCases(s: Armada_TotalState, step: Armada_Step, tid: Armada_ThreadHandle)
          requires tid in s.threads
        {{
          match step
            {matchBody}
        }}
      ");
      
      declCollector.AddItem(@"
        predicate Armada_ValidStep(s: Armada_TotalState, step: Armada_Step, tid: Armada_ThreadHandle)
        {
          && tid in s.threads
          && s.stop_reason.Armada_NotStopped?
          && Armada_ValidStepCases(s, step, tid)
        }
      ");

      matchBody = String.Concat(symbols.NextRoutines.Select(r => $"{pr.CaseEntry(r)} => {pr.GetNextStateInvocation(r)}\n"));
      declCollector.AddItem($@"
        function {{:opaque}} Armada_GetNextState(s: Armada_TotalState, step: Armada_Step, tid: Armada_ThreadHandle)
          : Armada_TotalState
        {{
          reveal Armada_ValidStepCases();
          if !Armada_ValidStep(s, step, tid) then
            s
          else
            match step
              {matchBody}
        }}
      ");

      declCollector.AddItem(@"
        function Armada_GetSpecFunctions() : Armada_SpecFunctions<Armada_TotalState, Armada_Step, Armada_PC>
        {
          Armada_SpecFunctions(Armada_Init,
                               Armada_ValidStep,
                               Armada_GetNextState,
                               (step:Armada_Step) => step.Armada_Step_Tau?,
                               (s:Armada_TotalState) => s.stop_reason.Armada_NotStopped?,
                               (s:Armada_TotalState, tid:Armada_ThreadHandle) =>
                                 if tid in s.threads then util_option_s.Some(s.threads[tid].pc) else util_option_s.None,
                               Armada_IsNonyieldingPC)
        }
      ");

      declCollector.AddItem(@"
        function Armada_Spec() : GeneralRefinementModule.Spec<Armada_TotalState>
        {
          Armada_SpecFunctionsToSpec(Armada_GetSpecFunctions())
        }
      ");
    }

    private string GetStructUpdateConstraints(Type innerType, int numArrayDimensions, int whichField, string fieldName)
    {
      var constraints = new List<string>();
      if (AH.IsPrimitiveType(innerType)) {
        constraints.Add($"|fields| == {numArrayDimensions + 1}");
      }
      else {
        constraints.Add($"|fields| >= {numArrayDimensions + 1}");
      }
      constraints.Add($"fields[0] == {whichField}");
      var value = $"v.{fieldName}";
      for (int i = 0; i < numArrayDimensions; ++i) {
        constraints.Add($"0 <= fields[{i + 1}] < |{value}|");
        value += $"[fields[{i + 1}]]";
      }
      if (AH.IsPrimitiveType(innerType)) {
        constraints.Add($"value.Armada_PrimitiveValue_{innerType}?");
      }
      return AH.CombineStringsWithAnd(constraints);
    }

    private void GenerateStructDatatypesAndFunctions(ArmadaStructs structs, ArmadaStruct s, DeclCollector declCollector)
    {
      var structFields =
        $"datatype Armada_Struct_{s.Name} = Armada_Struct_{s.Name}("
        + String.Join(", ", s.FieldNames.Select(fieldName => $"{fieldName}: {structs.FlattenType(s.GetFieldType(fieldName)).ToString()}"))
        + ")";
      declCollector.AddItem(structFields);

      var fieldNames = s.FieldNames.ToArray();
      var fieldTypes = fieldNames.Select(fieldName => s.GetFieldType(fieldName)).ToArray();
      var numFields = fieldNames.Length;

      var fieldTypeConstructors = fieldTypes.Select(AH.GetObjectType);
      declCollector.AddItem($@"
        function Armada_StructType_{s.Name}() : Armada_ObjectType
        {{
          Armada_ObjectTypeStruct([{AH.CombineStringsWithCommas(fieldTypeConstructors)}])
        }}
      ");

      foreach (var fieldName in fieldNames) {
        var fieldType = s.GetFieldType(fieldName);
        if (!AH.IsValidHeapType(fieldType, structs)) {
          AH.PrintError(prog, $"Struct {s.Name} contains field {fieldName} of type {fieldType}, which isn't a valid heap type");
        }
      }

      var fields = String.Join(", ", Enumerable.Range(0, numFields).Select(fieldIndex =>
                     AH.GetInvocationOfDereferencePointer("h", $"h.tree[p].children[{fieldIndex}]", fieldTypes[fieldIndex])));
      declCollector.AddItem($@"
        function Armada_DereferenceStructPointer_{s.Name}(h: Armada_Heap, p: Armada_Pointer) : Armada_Struct_{s.Name}
          requires Armada_ValidPointerToObjectType(h, p, Armada_StructType_{s.Name}())
        {{
          Armada_Struct_{s.Name}({fields})
        }}
      ");

      var updater = $@"
        function Armada_UpdateStruct_{s.Name}(v: Armada_Struct_{s.Name}, fields: seq<int>, value: Armada_PrimitiveValue)
          : Armada_Struct_{s.Name}
        {{
      ";
      for (var fieldIndex = 0; fieldIndex < numFields; ++fieldIndex) {
        var fieldType = fieldTypes[fieldIndex];
        var fieldName = fieldNames[fieldIndex];
        Type innerType;
        var numArrayDimensions = AH.GetNumArrayDimensions(fieldType, out innerType);
        var vDotFieldName = $"v.{fieldName}";
        updater += $@"
          if {GetStructUpdateConstraints(innerType, numArrayDimensions, fieldIndex, fieldName)} then
            v.({fieldName} := {GetStructFieldUpdate(innerType, numArrayDimensions, vDotFieldName, 1)})
          else
        ";
      }
      updater += "v }";
      declCollector.AddItem(updater);

      var updates = AH.CombineStringsWithSetAddition(
                      Enumerable.Range(0, numFields).Select(fieldIndex =>
                        AH.GetInvocationOfUpdateValuesViaPointer("h", $"h.tree[p].children[{fieldIndex}]",
                                                                 $"value.{fieldNames[fieldIndex]}", fieldTypes[fieldIndex])));
      updater = $@"
        function Armada_UpdateHeapValuesWithStruct_{s.Name}(
          h: Armada_Heap,
          p: Armada_Pointer,
          value: Armada_Struct_{s.Name}
          ) : (
          set<(Armada_Pointer, Armada_PrimitiveValue)>
          )
        {{
          if Armada_ValidPointerToObjectType(h, p, Armada_StructType_{s.Name}()) then
            {updates}
          else
            {{ }}
        }}
      ";
      declCollector.AddItem(updater);
    }

    public void GenerateStructDatatypesAndFunctions(ArmadaStructs structs, DeclCollector declCollector)
    {
      foreach (var structName in structs.StructNames) {
        var s = structs.GetStruct(structName);
        GenerateStructDatatypesAndFunctions(structs, s, declCollector);
      }
    }

    public void GenerateTotalState(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      var listOfPCs = new List<ArmadaPC>{ };
      symbols.AllMethods.AppendAllPCs(listOfPCs);
      declCollector.AddItem("datatype Armada_PC = " + String.Join(" | ", listOfPCs.Select(pc => pc.ToString())));

      foreach (var methodName in symbols.MethodNames) {
        CreateMethodStackFrame(methodName, symbols, declCollector);
      }
      declCollector.AddItem(
        "datatype Armada_StackFrame = "
        + String.Join(" | ", symbols.MethodNames.Select(methodName =>
                                                        $"Armada_StackFrame_{methodName}({methodName}: Armada_StackVars_{methodName})"))
      );

      List<string> globalFields = new List<string>();
      List<string> addrFields = new List<string>();
      List<string> ghostFields = new List<string>();
      var staticGlobalVars = "datatype Armada_GlobalStaticVar = Armada_GlobalStaticVarNone";
      foreach (var varName in symbols.Globals.VariableNames) {
        var v = symbols.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable) {
          globalFields.Add($"{varName}: {symbols.FlattenType(v.ty)}");
          staticGlobalVars += $" | Armada_GlobalStaticVar_{varName}";
        }
        else if (v is GlobalAddressableArmadaVariable) {
          addrFields.Add($"{varName}: Armada_Pointer");
        }
        else if (v is GlobalGhostArmadaVariable) {
          ghostFields.Add($"{varName}: {symbols.FlattenType(v.ty)}");
        }
        else {
          AH.PrintError(prog, "Internal error:  variable of unexpected type");
        }
      }

      declCollector.AddItem("datatype Armada_Globals = Armada_Globals(" + String.Join(", ", globalFields) + ")");
      declCollector.AddItem(staticGlobalVars);
      declCollector.AddItem("datatype Armada_Ghosts = Armada_Ghosts(" + String.Join(", ", ghostFields) + ")");
      declCollector.AddItem("datatype Armada_Addrs = Armada_Addrs(" + String.Join(", ", addrFields) + ")");

      declCollector.AddItem(@"
        datatype Armada_StoreBufferLocation = Armada_StoreBufferLocation_Unaddressable(v: Armada_GlobalStaticVar, fields: seq<int>)
                                            | Armada_StoreBufferLocation_Addressable(p: Armada_Pointer)
      ");

      declCollector.AddItem(@"
        datatype Armada_StoreBufferEntry = Armada_StoreBufferEntry(loc: Armada_StoreBufferLocation, value: Armada_PrimitiveValue,
                                                                   pc: Armada_PC)
      ");

      declCollector.AddItem("datatype Armada_SharedMemory = Armada_SharedMemory(heap: Armada_Heap, globals: Armada_Globals)");
      declCollector.AddItem(@"
        datatype Armada_ExtendedFrame =
          Armada_ExtendedFrame(return_pc: Armada_PC, frame: Armada_StackFrame, new_ptrs:set<Armada_Pointer>)
      ");
      declCollector.AddItem(@"
        datatype Armada_Thread = Armada_Thread(pc: Armada_PC, top: Armada_StackFrame, new_ptrs: set<Armada_Pointer>,
                                               stack: seq<Armada_ExtendedFrame>, storeBuffer: seq<Armada_StoreBufferEntry>)
      ");
      declCollector.AddItem(@"
        datatype Armada_TotalState = Armada_TotalState(stop_reason: Armada_StopReason, threads: map<Armada_ThreadHandle, Armada_Thread>,
                                                       mem: Armada_SharedMemory, ghosts: Armada_Ghosts, addrs: Armada_Addrs,
                                                       joinable_tids: set<Armada_ThreadHandle>)
      ");

      GenerateAddressableStaticVariablesPredicates(symbols, declCollector);

      GenerateInitPredicate(symbols, declCollector);

      GenerateIsNonyieldingPCPredicate(symbols, declCollector);

      GenerateNextBodies(symbols, declCollector);

      declCollector.AddItem(@"
        function Armada_UpdatePC(s:Armada_TotalState, tid:Armada_ThreadHandle, pc:Armada_PC) : Armada_TotalState
          requires tid in s.threads
        {
          s.(threads := s.threads[tid := s.threads[tid].(pc := pc)])
        }
      ");

      declCollector.AddItem(@"
        function Armada_UpdateTSFrame(s:Armada_TotalState, tid:Armada_ThreadHandle, frame:Armada_StackFrame) : Armada_TotalState
          requires tid in s.threads
        {
          s.(threads := s.threads[tid := s.threads[tid].(top := frame)])
        }
      ");

      declCollector.AddItem(@"
        function Armada_StoreBufferAppend(buf:seq<Armada_StoreBufferEntry>, entry:Armada_StoreBufferEntry) : seq<Armada_StoreBufferEntry>
        {
          buf + [entry]
        }
      ");

      declCollector.AddItem(@"
        function Armada_AppendToThreadStoreBuffer(s:Armada_TotalState, tid:Armada_ThreadHandle, entry:Armada_StoreBufferEntry)
          : Armada_TotalState
          requires tid in s.threads
        {
          s.(threads := s.threads[tid := s.threads[tid].(storeBuffer := Armada_StoreBufferAppend(s.threads[tid].storeBuffer, entry))])
        }
      ");
    }

    public void TranslateGlobalInvariants(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      foreach (var globalInvariant in symbols.GlobalInvariants.Values) {
        var gid = globalInvariant.Decl;
        var failureReporter = new SimpleFailureReporter(prog);
        var context = new GlobalInvariantResolutionContext("s", symbols, failureReporter, null);
        var bodyRValue = context.ResolveAsRValue(gid.Body);
        if (!failureReporter.Valid)
        {
          continue;
        }

        var antecedent = "s.stop_reason.Armada_NotStopped?";
        if (bodyRValue.CanCauseUndefinedBehavior) {
          antecedent = $"{antecedent} && ({bodyRValue.UndefinedBehaviorAvoidance.Expr})";
        }

        globalInvariant.TranslatedName = $"Armada_GlobalInv_{gid.Name}";
        declCollector.AddItem($@"
          predicate {globalInvariant.TranslatedName}(s: Armada_TotalState)
          {{
            {antecedent} ==> ({bodyRValue.Val})
          }}
        ");
      }
    }

    public void TranslateYieldPredicates(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      foreach (var yieldPredicate in symbols.YieldPredicates.Values) {
        var yd = yieldPredicate.Decl;
        var failureReporter = new SimpleFailureReporter(prog);
        var context = new YieldPredicateResolutionContext("s", "s'", "tid", symbols, failureReporter, null);
        var rvalue = context.ResolveAsRValue(yd.Body);
        if (!failureReporter.Valid)
        {
          continue;
        }

        var body = rvalue.CanCauseUndefinedBehavior ? $"({rvalue.UndefinedBehaviorAvoidance.Expr}) ==> ({rvalue.Val})" : rvalue.Val;
        yieldPredicate.TranslatedName = $"Armada_YieldPredicate_{yd.Name}";
        declCollector.AddItem($@"
          predicate {yieldPredicate.TranslatedName}(s: Armada_TotalState, s': Armada_TotalState, tid: Armada_ThreadHandle)
            requires tid in s.threads
            requires tid in s'.threads
          {{
            {body}
          }}
        ");
      }
    }

    public void TranslateUniversalStepConstraints(ArmadaSymbolTable symbols, DeclCollector declCollector)
    {
      string body;

      foreach (var stepConstraint in symbols.UniversalStepConstraints.Values)
      {
        var usc = stepConstraint.Decl;

        if (usc.Body == null) {
          stepConstraint.TranslatedName = $"Armada_UniversalStepConstraint_{usc.Name}";
          declCollector.AddItem($@"
            predicate {stepConstraint.TranslatedName}(s: Armada_TotalState, tid: Armada_ThreadHandle)
              requires tid in s.threads
            {{
              var threads := s.threads;
              var globals := s.mem.globals;
              var ghosts := s.ghosts;
              { usc.Code }
            }}
          ");
          continue;
        }
        
        var failureReporter = new SimpleFailureReporter(prog);
        var context = new RequiresResolutionContext("s", "tid", null, symbols, failureReporter, null);
        var rvalue = context.ResolveAsRValue(usc.Body);
        if (!failureReporter.Valid)
        {
          continue;
        }

        body = rvalue.CanCauseUndefinedBehavior ? $"({rvalue.UndefinedBehaviorAvoidance.Expr}) && ({rvalue.Val})" : rvalue.Val;
        stepConstraint.TranslatedName = $"Armada_UniversalStepConstraint_{usc.Name}";
        declCollector.AddItem($@"
          predicate {stepConstraint.TranslatedName}(s: Armada_TotalState, tid: Armada_ThreadHandle)
            requires tid in s.threads
          {{
            {body}
          }}
        ");
      }

      body = AH.CombineStringsWithAnd(symbols.UniversalStepConstraints.Values.Select(sc => $"{sc.TranslatedName}(s, tid)"));
      declCollector.AddItem($@"
        predicate Armada_UniversalStepConstraint(s: Armada_TotalState, tid: Armada_ThreadHandle)
          requires tid in s.threads
        {{
          {body}
        }}
      ");
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
      if (!CheckForConcreteStructDefinitions(structs)) {
        return;
      }
      if (!CheckForCyclicStructDefinitions(structs)) {
        return;
      }

      // Create m.ArmadaTranslation to hold state-machine translation.

      var declCollector = new DeclCollector(prog);

      declCollector.CopyMathematicalDefaultClassMembers(defaultClass);
      declCollector.CopyMathematicalTopLevelDecls(m);
      m.ArmadaStructs = structs;
      m.ArmadaTranslation = new ModuleDefinition(Token.NoToken, m.Name, new List<IToken>(), false, false, false, null,
                                                 m.Module /* parent */, null, false);
      m.ArmadaIncludes = new List<string>();
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      foreach (var include in m.Module.Includes)
      {
        if (include.includerFilename == prog.Name && include.includedFullPath.EndsWith(".dfy"))
        {
          m.ArmadaIncludes.Add(include.includedFilename);
        }
      }

      // Start using m.ArmadaTranslation as our new module definition.

      m = m.ArmadaTranslation;

      // Generate the struct-related datatypes and all their attendant definitions

      GenerateStructDatatypesAndFunctions(structs, declCollector);

      // Add headers to the new module.

      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_maps_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_seqs_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_option_s", m, false));

      // Add all the definitions we've created to the module.

      m.TopLevelDecls.Add(new DefaultClassDecl(m, declCollector.NewDefaultClassDecls));
      m.TopLevelDecls.AddRange(declCollector.NewTopLevelDecls);
    }

    private void CreateStateMachineTranslation(ModuleDefinition m)
    {
      // Put default class info into symbols

      var symbols = new ArmadaSymbolTable(prog, m.ArmadaStructs);
      var classes = new Dictionary<string, ClassDecl>();
      var membersToRemove = new List<TopLevelDecl>();
      symbols.AddClass(m.ArmadaStructs.DefaultClass, true /* from structs module */, m.ArmadaStructs);
      foreach (var d in m.TopLevelDecls) {
        if (d is ClassDecl) {
          var c = (ClassDecl)d;
          if (c.IsDefaultClass) {
            symbols.AddClass(c, false /* not from structs module */, m.ArmadaStructs);
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

      var declCollector = new DeclCollector(prog);

      declCollector.CopyMathematicalDefaultClassMembers(symbols.DefaultClass);
      declCollector.CopyMathematicalTopLevelDecls(m);

      m.ArmadaSymbols = symbols;
      m.ArmadaTranslation = new ModuleDefinition(Token.NoToken, m.Name, new List<IToken>(), false, false, false, null,
                                                 m.Module /* parent */, null, false);
      m.ArmadaIncludes = new List<string>();
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      m.ArmadaIncludes.Add(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/spec/refinement.s.dfy");
      if (symbols.StructsModuleName != null) {
        m.ArmadaIncludes.Add($"{symbols.StructsModuleName}.dfy");
      }
      foreach (var include in m.Module.Includes)
      {
        if (include.includerFilename == prog.Name && include.includedFullPath.EndsWith(".dfy"))
        {
          m.ArmadaIncludes.Add(include.includedFilename);
        }
      }

      // Copy the default class members into symbols.DefaultClass, then remove all the methods from m,
      // then start using m.ArmadaTranslation as our new module definition.

      symbols.DefaultClass = new DefaultClassDecl(m.ArmadaTranslation, new List<MemberDecl>(symbols.DefaultClass.Members));
      GetMethods(symbols, symbols.DefaultClass);
      GetMethods(symbols, m.ArmadaStructs.DefaultClass);
      RemoveAllMethods(m);
      m = m.ArmadaTranslation;

      // Create definitions for methods' next routines

      ProcessMethods(symbols, declCollector);
      CreateTauNext(symbols, declCollector);
      GenerateEnablingConditions(symbols, declCollector);

      // Generate the total state datatype and all its attendant definitions

      GenerateTotalState(symbols, declCollector);

      // Translate global invariants, yield predicates, and universal step constraints

      TranslateGlobalInvariants(symbols, declCollector);
      TranslateYieldPredicates(symbols, declCollector);
      TranslateUniversalStepConstraints(symbols, declCollector);

      // Add headers to the new module.

      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_maps_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_collections_seqs_i", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("util_option_s", m, false));
      m.TopLevelDecls.Add(AH.MakeAliasModuleDecl("GeneralRefinementModule", m, false));

      // Add all the definitions we've created to the module.

      m.TopLevelDecls.Add(new DefaultClassDecl(m, declCollector.NewDefaultClassDecls));
      m.TopLevelDecls.AddRange(declCollector.NewTopLevelDecls);
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
            ++ memoryAccess;
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
            BinaryExpr.ResolvedOpcode.Mod, BinaryExpr.ResolvedOpcode.LeftShift,
            BinaryExpr.ResolvedOpcode.RightShift, BinaryExpr.ResolvedOpcode.BitwiseAnd,
            BinaryExpr.ResolvedOpcode.BitwiseOr, BinaryExpr.ResolvedOpcode.BitwiseXor
          };
          if (! allowedList.Contains(binary.ResolvedOp)) {
            AH.PrintWarning(prog, expr.tok, $"Binary Operator {binary.ResolvedOp} is not compilation-compatible");
            compatible = false;
          }
          break;
        case ConversionExpr _:
          break;
        case ITEExpr _:
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
        return false;
      }

      if (expr is StoreBufferEmptyExpr) {
        return false;
      }

      if (expr is TotalStateExpr) {
        return false;
      }

      if (expr is IfUndefinedExpr) {
        return false;
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

    private bool CheckMethodCompilationCompatible(ArmadaSymbolTable symbols, string methodName, MethodInfo methodInfo,
                                                  ArmadaSingleMethodSymbolTable methodSymbols) {
      bool compatible = true;

      // checking return arguments
      if (methodInfo.method.Outs.Count > 1) {
        AH.PrintWarning(prog, methodInfo.method.tok, $"Method {methodInfo.method.Name} has more than one return value");
        compatible = false;
      }

      // check unsupported types
      // all types to check: [Ins, Outs, {variables in body}]
      IEnumerable<Type> allTypes = methodSymbols.AllVariables.Select(v => v.ty);

      compatible = allTypes.All(type => CheckTypeReferenceCompilationCompatible(symbols, type)) && compatible;

      if (Attributes.Contains(methodInfo.method.Attributes, "extern")) {
        return compatible;
      }

      if (Attributes.Contains(methodInfo.method.Attributes, "atomic")) {
        AH.PrintError(prog, methodInfo.method.tok, $"Method {methodInfo.method.Name} is labeled :atomic, but atomic methods aren't allowed in a concrete layer.");
        compatible = false;
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
            AH.PrintWarning(prog, somehow.Tok, "Somehow statements aren't compilation-compatible");
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
              AH.PrintWarning(prog, update.Tok, "TSO-bypassing updates aren't compilation-compatible");
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
              AH.PrintWarning(prog, varDecl.Tok, "Non-update initializations aren't compilation-compatible");
              compatible = false;
            }
            if (varDecl.BypassStoreBuffers) {
              AH.PrintWarning(prog, varDecl.Tok, "TSO-bypassing initializations aren't compilation-compatible");
              compatible = false;
            }
            if (! initStage) {
              AH.PrintWarning(prog, varDecl.Tok, "Declaration of variables at non-entry locations isn't supported");
              compatible = false;
            }
            break;
          case ExplicitYieldBlockStmt atomic:
            AH.PrintWarning(prog, atomic.Tok, "Explicit-yield blocks aren't compilation-compatible");
            compatible = false;
            break;
          case YieldStmt yieldStmt:
            AH.PrintWarning(prog, yieldStmt.Tok, "Yield statements aren't compilation-compatible");
            compatible = false;
            break;
          case AssertStmt assert:
            AH.PrintWarning(prog, assert.Tok, "Assert statements aren't compilation-compatible");
            compatible = false;
            break;
          case AssumeStmt assume:
            AH.PrintWarning(prog, assume.Tok, "Assume statements aren't compilation-compatible");
            compatible = false;
            break;
          case WhileStmt whileStmt:
            if (whileStmt.Invariants.Any()) {
              AH.PrintWarning(prog, whileStmt.Tok, "Invariants on while statements aren't compilation-compatible");
              compatible = false;
            }
            break;
        }
        initStage = initStage && (stmt.Stmt is VarDeclStmt || stmt.Stmt is BlockStmt);
      }

      return compatible;
    }

    private bool CheckCompilationCompatible(ArmadaSymbolTable symbols) {
      bool compatible = true;

      foreach (var stepConstraint in symbols.UniversalStepConstraints.Values)
      {
        AH.PrintWarning(prog, stepConstraint.Decl.tok, "Universal step constraints aren't compilation-compatible");
        compatible = false;
      }

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
  }
}
