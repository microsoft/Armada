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

  public class ArmadaStruct
  {
    private string name;
    private Dictionary<string, Type> fieldTypes;
    private List<string> fieldNames;

    public ArmadaStruct(Program prog, ClassDecl c)
    {
      name = c.Name;
      fieldTypes = new Dictionary<string, Type>();
      fieldNames = new List<string>();

      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          var f = (Field)member;
          if (!f.IsStatic) {
            fieldNames.Add(f.Name);
            fieldTypes[f.Name] = f.Type;
            if (f.InitialValue != null) {
              AH.PrintError(prog, $"Ignoring initializer {f.InitialValue} of field {f.Name} of struct {name}");
            }
          }
          else {
            AH.PrintError(prog, $"Ignoring static field {f.Name} in struct");
          }
        }
      }
    }

    public ArmadaStruct(string struct_name, Dictionary<string, Type> fields)
    {
      name = struct_name;
      fieldTypes = fields;
      fieldNames = fields.Keys.ToList();
    }

    public string Name { get { return name; } }
    public IEnumerable<string> FieldNames { get { return fieldNames; } }
    public Type GetFieldType(string fieldName) { return fieldTypes[fieldName]; }
    public Type LookupFieldType(string fieldName) { return (fieldTypes.ContainsKey(fieldName)) ? fieldTypes[fieldName] : null; }
    public int GetFieldPos(string fieldName) { return fieldNames.IndexOf(fieldName); }
  }

  public class ArmadaStructs
  {
    public readonly string StructsModuleName;
    private Dictionary<string, ArmadaStruct> structs;
    private ClassDecl defaultClass;
    private string refinementConstraint;

    public ArmadaStructs(string i_structsModuleName)
    {
      StructsModuleName = i_structsModuleName;
      structs = new Dictionary<string, ArmadaStruct>();
      defaultClass = null;
      refinementConstraint = "(ls.stop_reason.Armada_NotStopped? || ls.stop_reason == hs.stop_reason)";
    }

    public void AddClass(Program prog, ClassDecl c)
    {
      if (!c.IsDefaultClass) {
        structs[c.Name] = new ArmadaStruct(prog, c);
      }
    }

    public void SetDefaultClass(ClassDecl c)
    {
      defaultClass = c;
    }

    public ClassDecl DefaultClass { get { return defaultClass;  } }

    public IEnumerable<string> StructNames { get { return structs.Keys; } }
    public bool DoesStructExist(string structName) { return structs.ContainsKey(structName); }
    public ArmadaStruct GetStruct(string structName) { return structs[structName]; }
    public ArmadaStruct LookupStruct(string structName) { return structs.ContainsKey(structName) ? structs[structName] : null; }

    public Type GetStructFieldType(string structName, string fieldName)
    {
      return structs.ContainsKey(structName) ? structs[structName].GetFieldType(fieldName) : null;
    }

    public int GetStructFieldPos(string structName, string fieldName)
    {
      return structs.ContainsKey(structName) ? structs[structName].GetFieldPos(fieldName) : -1;
    }

    public Type FlattenType(Type t, string moduleName = null)
    {
      if (t is UserDefinedType) {
        var ut = (UserDefinedType)t;
        if (DoesStructExist(ut.Name)) {
          return AH.ReferToType("Armada_Struct_" + ut.Name, moduleName);
        }
      }
      else if (t is SizedArrayType) {
        var ssa = (SizedArrayType)t;
        return new SeqType(FlattenType(ssa.Range, moduleName));
      }
      else if (t is PointerType) {
        return AH.ReferToType("Armada_Pointer");
      }

      return t;
    }

    public string RefinementConstraint { get { return refinementConstraint; } }

    public void AddRefinementConstraint(string constraint)
    {
      refinementConstraint = $"{refinementConstraint} && ({constraint})";
    }
  }

}
