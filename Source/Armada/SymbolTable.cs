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

  ////////////////////////////////////////////////////////////////////////////
  /// ArmadaPC
  ////////////////////////////////////////////////////////////////////////////

  public class ArmadaPC
  {
    private ArmadaSymbolTable symbols;
    public readonly string methodName;
    public readonly int instructionCount;

    public ArmadaPC()
    {
      symbols = null;
      methodName = null;
      instructionCount = 0;
    }

    public ArmadaPC(ArmadaSymbolTable i_symbols, string i_methodName, int i_instructionCount)
    {
      symbols = i_symbols;
      methodName = i_methodName;
      instructionCount = i_instructionCount;
    }

    public override string ToString()
    {
      return $"Armada_PC_{methodName}_{symbols.GetNameForPC(this)}";
    }

    public string Name
    {
      get {
        return symbols.GetNameForPC(this);
      }
    }

    public override bool Equals(object value)
    {
      ArmadaPC pc = value as ArmadaPC;

      return pc != null && pc.methodName == methodName && pc.instructionCount == instructionCount;
    }

    public override int GetHashCode()
    {
      return methodName.GetHashCode() * 397 + instructionCount;
    }

    public ArmadaPC CloneWithNewSymbolTable(ArmadaSymbolTable newSymbols)
    {
      return new ArmadaPC(newSymbols, methodName, instructionCount);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  /// ArmadaVariable
  ////////////////////////////////////////////////////////////////////////////

  public enum ArmadaVarType { Ghost, Global, Input, Output, Local, ExternRead, ExternOld };

  public abstract class ArmadaVariable {
    public readonly string name;
    public readonly Type ty;
    public readonly Expression initialValue;
    public readonly ArmadaVarType varType;

    public ArmadaVariable(string i_name, Type i_ty, Expression i_initialValue, ArmadaVarType i_varType) {
      name = i_name;
      ty = i_ty;
      initialValue = i_initialValue;
      varType = i_varType;
    }

    public abstract ArmadaLValue GetLValue(IToken tok, ResolutionContext context);
    public abstract ArmadaRValue GetRValue(IToken tok, ResolutionContext context);
    public abstract bool NoTSO();

    public virtual string FieldName { get { return name; } }
    public virtual Expression InitialValue { get { return initialValue; } }
    public virtual Type GetFlattenedType(ArmadaSymbolTable symbols, string moduleName = null)
    {
      return symbols.FlattenType(ty, moduleName);
    }
  }

  public abstract class AddressableArmadaVariable : ArmadaVariable {
    public AddressableArmadaVariable(string i_name, Type i_ty, Expression i_initialValue, ArmadaVarType i_varType)
      : base(i_name, i_ty, i_initialValue, i_varType) { }

    public override bool NoTSO() { return false; }

    public override string FieldName { get { return name; } }
    public override Type GetFlattenedType(ArmadaSymbolTable symbols, string moduleName = null)
    {
      return AH.ReferToType("Armada_Pointer");
    }
  }

  public abstract class UnaddressableArmadaVariable : ArmadaVariable {
    public UnaddressableArmadaVariable(string i_name, Type i_ty, Expression i_initialValue, ArmadaVarType i_varType)
      : base(i_name, i_ty, i_initialValue, i_varType) { }
  }

  public class GlobalGhostArmadaVariable : UnaddressableArmadaVariable {
    public GlobalGhostArmadaVariable(string i_name, Type i_ty, Expression i_initialValue)
      : base(i_name, i_ty, i_initialValue, ArmadaVarType.Ghost)
    {
    }

    public override bool NoTSO() { return true; }

    public override ArmadaLValue GetLValue(IToken tok, ResolutionContext context)
    {
      return new UnaddressableFieldArmadaLValue(tok, ty, new GhostsArmadaLValue(), new UndefinedBehaviorAvoidanceConstraint(), name,
                                                0, true);
    }

    public override ArmadaRValue GetRValue(IToken tok, ResolutionContext context)
    {
      var ghosts = context.GetRValueGhosts();
      var val = $"({ghosts}).{name}";
      return new ArmadaRValue(val);
    }
  }

  public class GlobalUnaddressableArmadaVariable : UnaddressableArmadaVariable {
    public GlobalUnaddressableArmadaVariable(string i_name, Type i_ty, Expression i_initialValue)
      : base(i_name, i_ty, i_initialValue, ArmadaVarType.Global)
    {
    }

    public override bool NoTSO() { return false; }

    public override ArmadaLValue GetLValue(IToken tok, ResolutionContext context)
    {
      return new UnaddressableFieldArmadaLValue(tok, ty, new GlobalsArmadaLValue(), new UndefinedBehaviorAvoidanceConstraint(), name,
                                                0, false);
    }

    public override ArmadaRValue GetRValue(IToken tok, ResolutionContext context)
    {
      var globals = context.GetRValueGlobals();
      return new ArmadaRValue($"({globals}).{name}");
    }
  }

  public class GlobalAddressableArmadaVariable : AddressableArmadaVariable {
    public GlobalAddressableArmadaVariable(string i_name, Type i_ty, Expression i_initialValue)
      : base(i_name, i_ty, i_initialValue, ArmadaVarType.Global) { }

    public override ArmadaLValue GetLValue(IToken tok, ResolutionContext context)
    {
      var addr = $"({context.GetLValueState()}).addrs.{name}";
      return new AddressableArmadaLValue(tok, ty, new ArmadaRValue(addr));
    }

    public override ArmadaRValue GetRValue(IToken tok, ResolutionContext context)
    {
      var addr = $"({context.GetRValueState()}).addrs.{name}";
      var h = context.GetRValueHeap();
      var valid = AH.GetInvocationOfValidPointer(h, addr, ty);
      if (valid == null) {
        context.Fail(tok, $"Type {ty} is currently not supported in the heap");
        return null;
      }
      var crashAvoidance = new UndefinedBehaviorAvoidanceConstraint(valid);

      var val = AH.GetInvocationOfDereferencePointer(h, addr, ty);
      if (val == null) {
        context.Fail(tok, $"Type {ty} is currently not supported in the heap");
      }
      return new ArmadaRValue(crashAvoidance, val);
    }
  }

  public class MethodStackFrameUnaddressableLocalArmadaVariable : UnaddressableArmadaVariable {
    private readonly string methodName;

    public override bool NoTSO() { return true; }

    public MethodStackFrameUnaddressableLocalArmadaVariable(
      string i_name,
      Type i_ty,
      Expression i_initialValue,
      ArmadaVarType i_varType,
      string i_methodName
      ) :
      base(i_name, i_ty, i_initialValue, i_varType) {
      methodName = i_methodName;
    }

    public override ArmadaLValue GetLValue(IToken tok, ResolutionContext context)
    {
      var crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      var varsVal = new TopStackVarsArmadaLValue(crashAvoidance, methodName);
      return new UnaddressableFieldArmadaLValue(tok, ty, varsVal, new UndefinedBehaviorAvoidanceConstraint(), name, 0, true);
    }

    public override ArmadaRValue GetRValue(IToken tok, ResolutionContext context)
    {
      var val = $"({context.GetRValueTopStackFrame()}).{methodName}.{name}";
      var crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      return new ArmadaRValue(crashAvoidance, val);
    }
  }

  public class MethodStackFrameAddressableLocalArmadaVariable : AddressableArmadaVariable {
    private readonly string methodName;
    private readonly bool tsoBypassingInitialization;

    public MethodStackFrameAddressableLocalArmadaVariable(string i_name, Type i_ty, Expression i_initialValue,
                                                          bool i_tsoBypassingInitialization, string i_methodName)
      : base(i_name, i_ty, i_initialValue, ArmadaVarType.Local) {
      methodName = i_methodName;
      tsoBypassingInitialization = i_tsoBypassingInitialization;
    }

    public bool TSOBypassingInitialization { get { return tsoBypassingInitialization; } }
    public override string FieldName { get { return $"AddrOf'{name}"; } }

    public override ArmadaLValue GetLValue(IToken tok, ResolutionContext context)
    {
      var crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      var addr = $"({context.GetLValueTopStackFrame()}).{methodName}.AddrOf'{name}";
      return new AddressableArmadaLValue(tok, ty, new ArmadaRValue(crashAvoidance, addr));
    }

    public override ArmadaRValue GetRValue(IToken tok, ResolutionContext context)
    {
      var crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      var addr = $"({context.GetRValueTopStackFrame()}).{methodName}.AddrOf'{name}";
      var h = context.GetRValueHeap();

      var valid = AH.GetInvocationOfValidPointer(h, addr, ty);
      if (valid == null) {
        context.Fail(tok, $"Type {ty} is not supported on the heap, and thus not for addressable stack variables either");
        return null;
      }
      crashAvoidance.Add(valid);

      var val = AH.GetInvocationOfDereferencePointer(h, addr, ty);
      if (val == null) {
        context.Fail(tok, $"Type {ty} is not supported on the heap, and thus not for addressable stack variables either");
      }
      return new ArmadaRValue(crashAvoidance, val);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  /// PC info
  ////////////////////////////////////////////////////////////////////////////

  public class MethodInfo {
    private Program prog;
    private ArmadaSymbolTable symbols;
    private int numPCs;
    private Dictionary<ArmadaPC, EnablingConstraintCollector> constraints;
    private ArmadaPC returnPC;
    private HashSet<ArmadaPC> nonyieldingPCs;
    private ArmadaStatement parsedBody;
    private bool atomicCallsAndReturns;

    public readonly Method method;

    public MethodInfo(Program i_prog, ArmadaSymbolTable i_symbols, Method i_method)
    {
      prog = i_prog;
      symbols = i_symbols;
      method = i_method;
      numPCs = 0;
      constraints = new Dictionary<ArmadaPC, EnablingConstraintCollector>();
      returnPC = null;
      nonyieldingPCs = new HashSet<ArmadaPC>();
      parsedBody = null;
      atomicCallsAndReturns = false;
    }

    public ArmadaPC GenerateOnePC()
    {
      int pcVal = numPCs;
      ++numPCs;
      var pc = new ArmadaPC(symbols, method.Name, pcVal);
      symbols.AssociateLabelWithPC(pcVal.ToString(), pc);
      return pc;
    }

    public EnablingConstraintCollector GetEnablingConstraintCollector(ArmadaPC pc)
    {
      if (constraints.ContainsKey(pc)) {
        return constraints[pc];
      }
      else {
        return null;
      }
    }

    public void AddEnablingConstraint(Program prog, ArmadaPC pc, Expression e)
    {
      if (!constraints.ContainsKey(pc)) {
        constraints[pc] = new EnablingConstraintCollector(prog);
      }
      var constraintCollector = constraints[pc];
      var context = new EnablingConstraintResolutionContext(constraintCollector, method.Name, symbols);
      var rvalue = context.ResolveAsRValue(e);
      constraintCollector.AddConjunct(rvalue.UndefinedBehaviorAvoidance);
      constraintCollector.AddConjunct(rvalue.Val);
    }

    public void AppendAllPCs(List<ArmadaPC> allPCs)
    {
      allPCs.AddRange(Enumerable.Range(0, numPCs).Select(i => new ArmadaPC(symbols, method.Name, i)));
    }

    public void SetReturnPC(ArmadaPC pc)
    {
      returnPC = pc;
    }

    public ArmadaPC ReturnPC { get { return returnPC; } }
    public HashSet<ArmadaPC> NonyieldingPCs { get { return nonyieldingPCs; } }
    public bool IsNonyieldingPC(ArmadaPC pc) { return nonyieldingPCs.Contains(pc); }

    public void UseAtomicCallsAndReturns()
    {
      atomicCallsAndReturns = true;
      nonyieldingPCs.Add(new ArmadaPC(symbols, method.Name, 0));
      nonyieldingPCs.Add(returnPC);
    }

    public bool AtomicCallsAndReturns { get { return atomicCallsAndReturns; } }

    public void ParseMethodBody(ArmadaSymbolTable symbols)
    {
      var parse = new ParseInfo(prog, symbols, this);
      parsedBody = ArmadaStatement.ParseStatement(parse, method.Body);
      var startPC = GenerateOnePC();
      returnPC = parsedBody.AssignPCs(startPC);

      ArmadaStatement.ComputeNonyieldingPCs(parsedBody, nonyieldingPCs);

      symbols.AssociateLabelWithPC("Start", startPC);
      symbols.AssociateLabelWithPC("End", returnPC);
      foreach (var statement in parsedBody) {
        statement.AssociateLabelsWithPCs();
        statement.GenerateEnablingConstraints();
      }
    }

    public ArmadaStatement ParsedBody { get { return parsedBody; } }

    public void AppendAllNonyieldingPCs(List<ArmadaPC> outNonyieldingPCs)
    {
      foreach (var pc in nonyieldingPCs) {
        outNonyieldingPCs.Add(pc);
      }
    }

    public int NumPCs { get { return numPCs; } }
  }

  public class AllMethodsInfo {
    private Program prog;
    private Dictionary<string, MethodInfo> methodPCInfo;

    public AllMethodsInfo(Program i_prog)
    {
      prog = i_prog;
      methodPCInfo = new Dictionary<string, MethodInfo>();
    }

    public MethodInfo AddMethod(ArmadaSymbolTable symbols, Method method)
    {
      if (methodPCInfo.ContainsKey(method.Name)) {
        AH.PrintError(prog, Token.NoToken, $"Attempt to add method {method.Name} twice to AllMethodsInfo");
        return methodPCInfo[method.Name];
      }
      var info = new MethodInfo(prog, symbols, method);
      methodPCInfo[method.Name] = info;
      return info;
    }

    public MethodInfo LookupMethod(string methodName)
    {
      if (methodPCInfo.ContainsKey(methodName)) {
        return methodPCInfo[methodName];
      }
      else {
        return null;
      }
    }

    public void AppendAllPCs(List<ArmadaPC> allPCs)
    {
      foreach (var info in methodPCInfo.Values) {
        info.AppendAllPCs(allPCs);
      }
    }

    public void AppendAllNonyieldingPCs(List<ArmadaPC> nonyieldingPCs)
    {
      foreach (var info in methodPCInfo.Values) {
        info.AppendAllNonyieldingPCs(nonyieldingPCs);
      }
    }

    public IEnumerable<string> AllMethodNames { get { return methodPCInfo.Keys; } }
  }

  ////////////////////////////////////////////////////////////////////////////
  /// SYMBOL TABLE
  ////////////////////////////////////////////////////////////////////////////

  public class ArmadaGlobalVariableSymbolTable {
    private Dictionary<string, ArmadaVariable> table;
    private List<string> variableNames;

    public ArmadaGlobalVariableSymbolTable() {
      table = new Dictionary<string, ArmadaVariable>();
      variableNames = new List<string>();
    }

    public void AddClassInfo(Program prog, ClassDecl c, ArmadaStructs structs)
    {
      if (!c.IsDefaultClass) {
        AH.PrintError(prog, "Internal error:  ArmadaGlobalVariableSymbolTable.AddClassInfo called on non-default class");
        return;
      }
      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          var f = (Field)member;
          variableNames.Add(f.Name);
          ArmadaVariable av = null;
          if (!AH.IsValidType(f.Type, structs)) {
            AH.PrintError(prog, $"Global variable {f.Name} has invalid type {f.Type}");
            av = null;
          }
          else if (f.IsGhost) {
            av = new GlobalGhostArmadaVariable(f.Name, f.Type, f.InitialValue);
          }
          else if (f.IsNoAddr) {
            av = new GlobalUnaddressableArmadaVariable(f.Name, f.Type, f.InitialValue);
          }
          else {
            if (AH.IsValidHeapType(f.Type, structs)) {
              av = new GlobalAddressableArmadaVariable(f.Name, f.Type, f.InitialValue);
            }
            else {
              AH.PrintError(prog, $"Global variable {f.Name} has type {f.Type} that can't be used on the heap. Consider making it noaddr or ghost.");
              av = null;
            }
          }
          table.Add(f.Name, av);
        }
      }
    }

    public ArmadaVariable Lookup(string variableName)
    {
      ArmadaVariable v;
      if (!table.TryGetValue(variableName, out v)) {
        return null;
      }
      return v;
    }

    public IEnumerable<string> VariableNames { get { return variableNames; } }
  }

  public class ArmadaSingleMethodSymbolTable {
    private readonly Method method;
    private readonly string methodName;
    private readonly bool isExternal;
    private readonly bool isFromStructsModule;
    private Dictionary<string, ArmadaVariable> variablesByName;
    private List<string> inputVariableNames;
    private List<string> outputVariableNames;
    private List<string> variableNamesInOrder;

    public ArmadaSingleMethodSymbolTable(Method i_method, bool i_isExternal, bool i_isFromStructsModule) {
      method = i_method;
      methodName = method.Name;
      isExternal = i_isExternal;
      isFromStructsModule = i_isFromStructsModule;
      variablesByName = new Dictionary<string, ArmadaVariable>();
      inputVariableNames = new List<string>();
      outputVariableNames = new List<string>();
      variableNamesInOrder = new List<string>();
    }

    public Method GetMethod() { return method; }
    public bool IsExternal { get { return isExternal; } }
    public bool IsFromStructsModule { get { return isFromStructsModule; } }

    public void AddVariable(Program prog, ArmadaVariable v)
    {
      if (variablesByName.ContainsKey(v.name)) {
        AH.PrintError(prog, $"Variable {v.name} defined twice in method {methodName}");
        return;
      }

      variablesByName[v.name] = v;
      variableNamesInOrder.Add(v.name);

      if (v.varType == ArmadaVarType.Input) {
        inputVariableNames.Add(v.name);
      }
      else if (v.varType == ArmadaVarType.Output) {
        outputVariableNames.Add(v.name);
      }
    }

    public ArmadaVariable LookupVariable(string name) {
      if (variablesByName.ContainsKey(name)) {
        return variablesByName[name];
      }
      else {
        return null;
      }
    }

    public string GetVariableStackFrameFieldName(string localVariableName) {
      return LookupVariable(localVariableName).FieldName;
    }

    public ArmadaVariable GetInputVariableByIndex(int idx) {
      if (idx < 0 || idx >= inputVariableNames.Count) {
        return null;
      }
      string name = inputVariableNames[idx];
      return variablesByName[name];
    }

    public int GetNumInputVariables() {
      return inputVariableNames.Count;
    }

    public ArmadaVariable GetOutputVariableByIndex(int idx) {
      if (idx < 0 || idx >= outputVariableNames.Count) {
        return null;
      }
      string name = outputVariableNames[idx];
      return variablesByName[name];
    }

    public int GetNumOutputVariables() {
      return outputVariableNames.Count;
    }

    public IEnumerable<string> InputVariableNames { get { return inputVariableNames; } }
    public IEnumerable<string> OutputVariableNames { get { return outputVariableNames; } }
    public IEnumerable<ArmadaVariable> AllVariables { get { return variablesByName.Values; } }
    public IEnumerable<string> AllVariableNamesInOrder { get { return variableNamesInOrder; } }
    public IEnumerable<ArmadaVariable> AllVariablesInOrder { get { return variableNamesInOrder.Select(n => variablesByName[n]); } }
  }

  public class ArmadaMethodLocalVariableSymbolTable {
    private Dictionary<string, ArmadaSingleMethodSymbolTable> methodTable;

    public ArmadaMethodLocalVariableSymbolTable() {
      methodTable = new Dictionary<string, ArmadaSingleMethodSymbolTable>();
    }

    private void ExtractLocalVariables(Program prog, Statement stmt, string methodName, ArmadaSingleMethodSymbolTable smst,
                                       ArmadaStructs structs)
    {
      if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        foreach (var substmt in s.Body) {
          ExtractLocalVariables(prog, substmt, methodName, smst, structs);
        }
      }
      else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        ExtractLocalVariables(prog, s.Thn, methodName, smst, structs);
        ExtractLocalVariables(prog, s.Els, methodName, smst, structs);
      }
      else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        ExtractLocalVariables(prog, s.Body, methodName, smst, structs);
      }
      else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        UpdateStmt update = null;

        if (s.Update != null) {
          if (!(s.Update is UpdateStmt)) {
            AH.PrintError(prog, stmt.Tok, "Armada only supports *concrete* assignment of local variables during assignment.");
            return;
          }
          else {
            update = (UpdateStmt)s.Update;
            if (s.Locals.Count != update.Rhss.Count) {
              AH.PrintError(prog, s.Tok, $"Number of left-hand sides for assignment ({s.Locals.Count}) statement doesn't match number of right-hand sides ({update.Rhss.Count}).");
              return;
            }
          }
        }

        for (int i = 0; i < s.Locals.Count; ++i) {
          var local = s.Locals[i];
          if (local.OptionalType is InferredTypeProxy) {
            AH.PrintError(prog, local.EndTok, "Local variables in Armada layer methods must be given explicit types.");
            continue;
          }

          Expression initialValue = null;
          if (update != null) {
            var rhs = update.Rhss[i];
            if (rhs is HavocRhs) {
              // No need to do anything special here because in the absence of an initializer we already havoc
            }
            else if (rhs is ExprRhs) {
              var erhs = (ExprRhs)rhs;
              initialValue = erhs.Expr;
            }
            else if (rhs is CreateThreadRhs) {
              AH.PrintError(prog, rhs.Tok, "Create-thread can't be done in a variable-declaration statement");
              continue;
            }
            else if (rhs is MallocRhs || rhs is CallocRhs) {
              AH.PrintError(prog, rhs.Tok, "Allocation can't be done in a variable-declaration statement");
              continue;
            }
            else {
              AH.PrintError(prog, rhs.Tok, "Right-hand side of variable-declaration isn't a valid rvalue");
              continue;
            }
          }

          if (!AH.IsValidType(local.OptionalType, structs)) {
            AH.PrintError(prog, stmt.Tok, $"Local variable {local.Name} in method {methodName} has invalid type {local.OptionalType}");
            continue;
          }

          ArmadaVariable v;
          if (local.IsNoAddr) {
            v = new MethodStackFrameUnaddressableLocalArmadaVariable(local.Name, local.OptionalType, initialValue, ArmadaVarType.Local, methodName);
          }
          else {
            if (!AH.IsValidHeapType(local.OptionalType, structs)) {
              AH.PrintError(prog, stmt.Tok, $"Local variable {local.Name} in method {methodName} has type {local.OptionalType} that can't be used on the heap. Consider using noaddr instead.");
              continue;
            }
            v = new MethodStackFrameAddressableLocalArmadaVariable(local.Name, local.OptionalType, initialValue,
                                                                   s.BypassStoreBuffers, methodName);
          }
          smst.AddVariable(prog, v);
        }
      }
    }

    private void ExtractOldVariablesForBodylessMethod(Program prog, ArmadaSymbolTable symbols, Method meth, ArmadaSingleMethodSymbolTable smst)
    {
      if (meth.Ens == null) { return; }
      if (!meth.Ens.Any()) { return; }

      var failureCollector = new SimpleFailureReporter(prog);
      var ensContext = new BodylessMethodSnapshotResolutionContext("s", "tid", meth.Name, symbols, failureCollector);
      foreach (var ens in meth.Ens)
      {
        var ensResolvedJustToGetOldValues = ensContext.ResolveAsRValue(ens.E);
      }
      int whichOldValue = 0;
      foreach (var oldValue in ensContext.OldValues) {
        var varName = $"Armada_Old{whichOldValue}";
        var v = new MethodStackFrameUnaddressableLocalArmadaVariable(varName, oldValue.Type, oldValue, ArmadaVarType.ExternOld, meth.Name);
        ++whichOldValue;
        smst.AddVariable(prog, v);
      }
    }

    public void AddMethodInfo(Program prog, ClassDecl c, ArmadaSymbolTable symbols, Method meth, bool fromStructsModule,
                              ArmadaStructs structs)
    {
      bool isExternal = (meth.Body is null || Attributes.Contains(meth.Attributes, "extern"));

      var smst = new ArmadaSingleMethodSymbolTable(meth, isExternal, fromStructsModule);

      foreach (var formal in meth.Ins) {
        var v = new MethodStackFrameUnaddressableLocalArmadaVariable(formal.Name, formal.Type, null, ArmadaVarType.Input, meth.Name);
        smst.AddVariable(prog, v);
      }

      foreach (var formal in meth.Outs) {
        var v = new MethodStackFrameUnaddressableLocalArmadaVariable(formal.Name, formal.Type, null, ArmadaVarType.Output, meth.Name);
        smst.AddVariable(prog, v);
      }

      ExtractLocalVariables(prog, meth.Body, meth.Name, smst, structs);

      if (isExternal && meth.Reads.Expressions != null) {
        var reads = meth.Reads.Expressions;
        for (int i = 0; i < reads.Count; ++i) {
          Expression read_expr = reads.ElementAt(i);
          var varName = $"Armada_Extern{i}";
          var v = new MethodStackFrameUnaddressableLocalArmadaVariable(varName, read_expr.Type, null, ArmadaVarType.ExternRead, meth.Name);
          smst.AddVariable(prog, v);
        }
      }

      if (methodTable.ContainsKey(meth.Name)) {
        AH.PrintError(prog, $"Method {meth.Name} already defined");
      }
      else {
        methodTable[meth.Name] = smst;
      }

      if (isExternal && meth.Body == null)
      {
        ExtractOldVariablesForBodylessMethod(prog, symbols, meth, smst);
      }
    }

    public ArmadaVariable Lookup(string methodName, string localVariableName)
    {
      ArmadaSingleMethodSymbolTable smst;
      if (!methodTable.TryGetValue(methodName, out smst)) {
        return null;
      }
      return smst.LookupVariable(localVariableName);
    }

    public IEnumerable<string> MethodNames { get { return methodTable.Keys; } }

    public bool DoesMethodNameExist(string methodName)
    {
      return methodTable.ContainsKey(methodName);
    }

    public ArmadaSingleMethodSymbolTable GetMethodSymbolTable(string methodName)
    {
      return methodTable[methodName];
    }

    public ArmadaVariable GetInputVariableByIndex(string methodName, int idx)
    {
      ArmadaSingleMethodSymbolTable smst;
      if (!methodTable.TryGetValue(methodName, out smst)) {
        return null;
      }
      return smst.GetInputVariableByIndex(idx);
    }

    public int GetNumInputVariables(string methodName)
    {
      ArmadaSingleMethodSymbolTable smst;
      if (!methodTable.TryGetValue(methodName, out smst)) {
        return -1;
      }
      return smst.GetNumInputVariables();
    }

    public ArmadaVariable GetOutputVariableByIndex(string methodName, int idx)
    {
      ArmadaSingleMethodSymbolTable smst;
      if (!methodTable.TryGetValue(methodName, out smst)) {
        return null;
      }
      return smst.GetOutputVariableByIndex(idx);
    }

    public int GetNumOutputVariables(string methodName)
    {
      ArmadaSingleMethodSymbolTable smst;
      if (!methodTable.TryGetValue(methodName, out smst)) {
        return -1;
      }
      return smst.GetNumOutputVariables();
    }
  }

  public class GlobalInvariantInfo
  {
    private GlobalInvariantDecl decl;
    private string translatedName;

    public GlobalInvariantInfo(GlobalInvariantDecl i_decl)
    {
      decl = i_decl;
      translatedName = null;
    }

    public GlobalInvariantDecl Decl { get { return decl; } }
    public string Name { get { return decl.Name; } }
    public string TranslatedName { get { return translatedName; } set { translatedName = value; } }
  }

  public class YieldPredicateInfo
  {
    private YieldPredicateDecl decl;
    private string translatedName;

    public YieldPredicateInfo(YieldPredicateDecl i_decl)
    {
      decl = i_decl;
      translatedName = null;
    }

    public YieldPredicateDecl Decl { get { return decl; } }
    public string Name { get { return decl.Name; } }
    public string TranslatedName { get { return translatedName; } set { translatedName = value; } }
  }

  public class UniversalStepConstraintInfo
  {
    private UniversalStepConstraintDecl decl;
    private string translatedName;

    public UniversalStepConstraintInfo(UniversalStepConstraintDecl i_decl)
    {
      decl = i_decl;
      translatedName = null;
    }

    public UniversalStepConstraintDecl Decl { get { return decl; } }
    public string Name { get { return decl.Name; } }
    public string TranslatedName { get { return translatedName; } set { translatedName = value; } }
  }

  public class ArmadaSymbolTable
  {
    private Program prog;
    private ArmadaGlobalVariableSymbolTable globalVariables;
    private ArmadaMethodLocalVariableSymbolTable localVariables;
    private ClassDecl defaultClass;
    private ArmadaStructs structs;
    private HashSet<string> threadRoutines;
    private List<string> functionNames;
    private List<NextRoutineConstructor> nextRoutineConstructors;
    private List<NextRoutine> nextRoutines;
    private AllMethodsInfo allMethodsInfo;
    private NextRoutineConstructor tauNextRoutineConstructor;
    private Dictionary<string, ArmadaPC> methodAndLabelToPCMap;
    private Dictionary<ArmadaPC, string> pcToLabelMap;
    private Dictionary<string, GlobalInvariantInfo> globalInvariants;
    private Dictionary<string, YieldPredicateInfo> yieldPredicates;
    private Dictionary<string, UniversalStepConstraintInfo> universalStepConstraints;

    public ArmadaSymbolTable(Program i_prog, ArmadaStructs i_structs)
    {
      prog = i_prog;
      globalVariables = new ArmadaGlobalVariableSymbolTable();
      localVariables = new ArmadaMethodLocalVariableSymbolTable();
      defaultClass = null;
      if (i_structs == null)
      {
        structs = new ArmadaStructs(null);
      }
      else
      {
        structs = i_structs;
      }
      threadRoutines = new HashSet<string> { "main" };
      functionNames = new List<string>{};
      nextRoutines = new List<NextRoutine>();
      nextRoutineConstructors = new List<NextRoutineConstructor>();
      allMethodsInfo = new AllMethodsInfo(prog);
      tauNextRoutineConstructor = null;
      methodAndLabelToPCMap = new Dictionary<string, ArmadaPC>();
      pcToLabelMap = new Dictionary<ArmadaPC, string>();
      globalInvariants = new Dictionary<string, GlobalInvariantInfo>();
      yieldPredicates = new Dictionary<string, YieldPredicateInfo>();
      universalStepConstraints = new Dictionary<string, UniversalStepConstraintInfo>();
    }

    public void AddClass(ClassDecl c, bool fromStructsModule, ArmadaStructs structs)
    {
      if (c.IsDefaultClass)
      {
        defaultClass = c;
        globalVariables.AddClassInfo(prog, defaultClass, structs);
        foreach (MemberDecl member in defaultClass.Members)
        {
          if (member is Method) {
            var meth = (Method)member;
            localVariables.AddMethodInfo(prog, defaultClass, this, meth, fromStructsModule, structs);
          }
          else if (member is Function) {
            functionNames.Add(member.Name);
          }
          else if (member is GlobalInvariantDecl) {
            AddGlobalInvariant((GlobalInvariantDecl)member);
          }
          else if (member is YieldPredicateDecl) {
            AddYieldPredicate((YieldPredicateDecl)member);
          }
          else if (member is UniversalStepConstraintDecl) {
            AddUniversalStepConstraint((UniversalStepConstraintDecl)member);
          }
        }
      }
    }

    public ArmadaGlobalVariableSymbolTable Globals { get { return globalVariables; } }

    public ArmadaVariable Lookup(string methodName, string v)
    {
      ArmadaVariable av;

      if (methodName != null)
      {
        av = localVariables.Lookup(methodName, v);
        if (av != null)
        {
          return av;
        }
      }

      av = globalVariables.Lookup(v);
      if (av != null)
      {
        return av;
      }
      return null;
    }

    public IEnumerable<string> MethodNames { get { return localVariables.MethodNames; } }

    public bool DoesMethodNameExist(string methodName)
    {
      return localVariables.DoesMethodNameExist(methodName);
    }

    public ArmadaSingleMethodSymbolTable GetMethodSymbolTable(string methodName)
    {
      return localVariables.GetMethodSymbolTable(methodName);
    }

    public ArmadaVariable GetInputVariableByIndex(string methodName, int idx)
    {
      return localVariables.GetInputVariableByIndex(methodName, idx);
    }

    public int GetNumInputVariables(string methodName)
    {
      return localVariables.GetNumInputVariables(methodName);
    }

    public ArmadaVariable GetOutputVariableByIndex(string methodName, int idx)
    {
      return localVariables.GetOutputVariableByIndex(methodName, idx);
    }

    public int GetNumOutputVariables(string methodName)
    {
      return localVariables.GetNumOutputVariables(methodName);
    }

    public void UseMethodAsThreadRoutine(string methodName)
    {
      if (allMethodsInfo.LookupMethod(methodName).AtomicCallsAndReturns) {
        AH.PrintError(prog, $"It's illegal to use create_thread on {methodName} since it uses atomic calls and returns.");
      }
      threadRoutines.Add(methodName);
    }

    public HashSet<string> GetThreadRoutines()
    {
      return threadRoutines;
    }

    public bool IsThreadRoutine(string methodName)
    {
      return threadRoutines.Contains(methodName);
    }

    public ClassDecl DefaultClass { get { return defaultClass; } set { defaultClass = value; } }

    public IEnumerable<string> StructNames { get { return structs.StructNames; } }
    public bool DoesStructExist(string structName) { return structs.DoesStructExist(structName); }
    public ArmadaStruct GetStruct(string structName) { return structs.GetStruct(structName); }
    public ArmadaStruct LookupStruct(string structName) { return structs.LookupStruct(structName); }
    public Type GetStructFieldType(string structName, string fieldName) { return structs.GetStructFieldType(structName, fieldName); }
    public int GetStructFieldPos(string structName, string fieldName) { return structs.GetStructFieldPos(structName, fieldName); }
    public Type FlattenType(Type t, string moduleName = null) { return structs.FlattenType(t, moduleName); }
    public string StructsModuleName { get { return structs == null ? null : structs.StructsModuleName; } }

    public void AddNextRoutineConstructor(NextRoutineConstructor nrc) { nextRoutineConstructors.Add(nrc); }
    public IEnumerable<NextRoutineConstructor> NextRoutineConstructors { get { return nextRoutineConstructors; } }
    public void ClearNextRoutineConstructors() { nextRoutineConstructors = null; }
    public void AddNextRoutine(NextRoutine nextRoutine) { nextRoutines.Add(nextRoutine); }
    public IEnumerable<NextRoutine> NextRoutines { get { return nextRoutines; } }
    public NextRoutineConstructor TauNextRoutineConstructor {
      get { return tauNextRoutineConstructor; }
      set { tauNextRoutineConstructor = value; }
    }
    public NextRoutine TauNextRoutine { get { return tauNextRoutineConstructor.DefinedBehaviorNextRoutine; } }

    public AllMethodsInfo AllMethods { get { return allMethodsInfo; } }

    public IEnumerable<string> AllFunctions { get { return functionNames; } }

    public void AssociateLabelWithPC(string labelStr, ArmadaPC pc)
    {
      var fullLabelStr = pc.methodName + "_" + labelStr;
      if (methodAndLabelToPCMap.ContainsKey(fullLabelStr)) {
        AH.PrintError(prog, $"ERROR:  More than one label named {labelStr} in method {pc.methodName}");
      }
      methodAndLabelToPCMap[fullLabelStr] = pc;
      pcToLabelMap[pc] = labelStr;
    }

    public ArmadaPC GetPCForMethodAndLabel(string methodAndLabelStr)
    {
      if (methodAndLabelToPCMap.ContainsKey(methodAndLabelStr))
      {
        return methodAndLabelToPCMap[methodAndLabelStr];
      }
      else
      {
        return null;
      }
    }

    public string GetLabelForPC(ArmadaPC pc)
    {
      if (pcToLabelMap.ContainsKey(pc)) {
        return pcToLabelMap[pc];
      }
      else {
        return null;
      }
    }

    public string GetNameForPC(ArmadaPC pc)
    {
      string labelStr = GetLabelForPC(pc);
      if (labelStr != null) {
        return labelStr;
      }
      return pc.instructionCount.ToString();
    }

    public void AddGlobalInvariant(GlobalInvariantDecl decl)
    {
      globalInvariants[decl.Name] = new GlobalInvariantInfo(decl);
    }

    public void AddYieldPredicate(YieldPredicateDecl decl)
    {
      yieldPredicates[decl.Name] = new YieldPredicateInfo(decl);
    }

    public void AddUniversalStepConstraint(UniversalStepConstraintDecl decl)
    {
      universalStepConstraints[decl.Name] = new UniversalStepConstraintInfo(decl);
    }

    public Dictionary<string, GlobalInvariantInfo> GlobalInvariants { get { return globalInvariants; } }
    public Dictionary<string, YieldPredicateInfo> YieldPredicates { get { return yieldPredicates; } }
    public Dictionary<string, UniversalStepConstraintInfo> UniversalStepConstraints { get { return universalStepConstraints; } }

    public string RefinementConstraint { get { return structs.RefinementConstraint; } }

    public bool IsNonyieldingPC(ArmadaPC pc)
    {
      if (pc == null) { return false; }
      var method = allMethodsInfo.LookupMethod(pc.methodName);
      return method == null ? false : method.IsNonyieldingPC(pc);
    }

    public IEnumerable<ArmadaPC> EnumeratePotentialRecurrentPCs()
    {
      foreach (var methodName in allMethodsInfo.AllMethodNames) {
        // Include the start of the method.
        yield return new ArmadaPC(this, methodName, 0);

        // Include the return site of the method.
        var methodInfo = allMethodsInfo.LookupMethod(methodName);
        yield return methodInfo.ReturnPC;

        // Include each loop head in the method, and the PC of any non-forward goto.
        if (methodInfo.method.Body == null) {
          // For body-less methods, there's an implicit loop head at PC #1.
          yield return new ArmadaPC(this, methodName, 1);
        }
        else {
          foreach (var stmt in methodInfo.ParsedBody) {
            if (stmt is ArmadaWhileStatement) {
              yield return stmt.StartPC;
            }
            else if (stmt is ArmadaGotoStatement) {
              var startPC = stmt.StartPC;
              var s = (GotoStmt)(stmt.Stmt);
              var targetPC = GetPCForMethodAndLabel(methodName + "_" + s.Target);
              if (targetPC != null && targetPC.instructionCount <= startPC.instructionCount) {
                // If it's not a forward goto, it's potentially recurrent.
                yield return startPC;
              }
            }
          }
        }
      }
    }
  }
}
