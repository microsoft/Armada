include "util/collections/seqs.i.dfy"
include "util/option.s.dfy"
include "spec/refinement.s.dfy"

module ArmadaCommonDefinitions {

  import opened util_collections_seqs_i
  import opened util_option_s
  import opened GeneralRefinementModule

  ////////////////////////////////
  // Primitive types
  ////////////////////////////////

  newtype uint8 = n: int | 0 <= n < 256

  newtype uint16 = n: int | 0 <= n < 65536

  newtype uint32 = n: int | 0 <= n < 4294967296

  newtype uint64 = n: int | 0 <= n < 18446744073709551616

  newtype int8 = n: int | -128 <= n < 128

  newtype int16 = n: int | -32768 <= n < 32768

  newtype int32 = n: int | -2147483648 <= n < 2147483648

  newtype int64 = n: int | -9223372036854775808 <= n < 9223372036854775808

  function Armada_CastTo_uint8(n: int): (n': uint8)
    ensures 0 <= n < 256 ==> n' as int == n
  {
    (n % 256) as uint8
  }

  function Armada_CastTo_uint16(n: int): (n': uint16)
    ensures 0 <= n < 65536 ==> n' as int == n
  {
    (n % 65536) as uint16
  }

  function Armada_CastTo_uint32(n: int): (n': uint32)
    ensures 0 <= n < 4294967296 ==> n' as int == n
  {
    (n % 4294967296) as uint32
  }

  function Armada_CastTo_uint64(n: int): (n': uint64)
    ensures 0 <= n < 18446744073709551616 ==> n' as int == n
  {
    (n % 18446744073709551616) as uint64
  }

  function {:axiom} Armada_CastTo_int8(n: int): (n': int8)
    ensures -128 <= n < 128 ==> n' as int == n

  function {:axiom} Armada_CastTo_int16(n: int): (n': int16)
    ensures -32768 <= n < 32768 ==> n' as int == n

  function {:axiom} Armada_CastTo_int32(n: int): (n': int32)
    ensures -2147483648 <= n < 2147483648 ==> n' as int == n

  function {:axiom} Armada_CastTo_int64(n: int): (n': int64)
    ensures -9223372036854775808 <= n < 9223372036854775808 ==> n' as int == n

  datatype Armada_PrimitiveValue =
      Armada_PrimitiveValueNone
    | Armada_PrimitiveValue_uint8(n_uint8: uint8)
    | Armada_PrimitiveValue_uint16(n_uint16: uint16)
    | Armada_PrimitiveValue_uint32(n_uint32: uint32)
    | Armada_PrimitiveValue_uint64(n_uint64: uint64)
    | Armada_PrimitiveValue_int8(n_int8: int8)
    | Armada_PrimitiveValue_int16(n_int16: int16)
    | Armada_PrimitiveValue_int32(n_int32: int32)
    | Armada_PrimitiveValue_int64(n_int64: int64)

  datatype Armada_PrimitiveType = 
      Armada_PrimitiveType_uint8
    | Armada_PrimitiveType_uint16
    | Armada_PrimitiveType_uint32
    | Armada_PrimitiveType_uint64
    | Armada_PrimitiveType_int8
    | Armada_PrimitiveType_int16
    | Armada_PrimitiveType_int32
    | Armada_PrimitiveType_int64

  predicate Armada_PrimitiveValueMatchesType(v: Armada_PrimitiveValue, ty: Armada_PrimitiveType)
  {
    match ty
    case Armada_PrimitiveType_uint8 =>
      v.Armada_PrimitiveValue_uint8?
    case Armada_PrimitiveType_uint16 =>
      v.Armada_PrimitiveValue_uint16?
    case Armada_PrimitiveType_uint32 =>
      v.Armada_PrimitiveValue_uint32?
    case Armada_PrimitiveType_uint64 =>
      v.Armada_PrimitiveValue_uint64?
    case Armada_PrimitiveType_int8 =>
      v.Armada_PrimitiveValue_int8?
    case Armada_PrimitiveType_int16 =>
      v.Armada_PrimitiveValue_int16?
    case Armada_PrimitiveType_int32 =>
      v.Armada_PrimitiveValue_int32?
    case Armada_PrimitiveType_int64 =>
      v.Armada_PrimitiveValue_int64?
  }

  predicate Armada_PrimitiveValuesOfSameType(v: Armada_PrimitiveValue, v': Armada_PrimitiveValue)
  {
    match v
      case Armada_PrimitiveValueNone => v'.Armada_PrimitiveValueNone?
      case Armada_PrimitiveValue_uint8(_) => v'.Armada_PrimitiveValue_uint8?
      case Armada_PrimitiveValue_uint16(_) => v'.Armada_PrimitiveValue_uint16?
      case Armada_PrimitiveValue_uint32(_) => v'.Armada_PrimitiveValue_uint32?
      case Armada_PrimitiveValue_uint64(_) => v'.Armada_PrimitiveValue_uint64?
      case Armada_PrimitiveValue_int8(_) => v'.Armada_PrimitiveValue_int8?
      case Armada_PrimitiveValue_int16(_) => v'.Armada_PrimitiveValue_int16?
      case Armada_PrimitiveValue_int32(_) => v'.Armada_PrimitiveValue_int32?
      case Armada_PrimitiveValue_int64(_) => v'.Armada_PrimitiveValue_int64?
  }

  ////////////////////////////////
  // Bit vectors
  ////////////////////////////////

  function {:opaque} U32(b:bv32) : uint32 { b as uint32 }
  function {:opaque} B32(u:uint32) : bv32 { u as bv32 }
  function {:opaque} U64(b:bv64) : uint64 { b as uint64 }
  function {:opaque} B64(u:uint64) : bv64 { u as bv64 }

  // 32 bits
  function {:opaque} bit_and32(b0:bv32, b1:bv32) : bv32 
    { b0 & b1 }

  function {:opaque} bit_or32(b0:bv32, b1:bv32) : bv32 
    { b0 | b1 }

  function {:opaque} bit_mod32(b0:bv32, b1:bv32) : bv32 
    requires b1 != 0;
    { b0 % b1 }

  function {:opaque} bit_xor32(b0:bv32, b1:bv32) : bv32 
    { b0 ^ b1 }

  function {:opaque} bit_lshift32(b0:bv32, b1:bv32) : bv32 
    requires b1 <= 32;
    { b0 << b1 }

  function {:opaque} bit_rshift32(b0:bv32, b1:bv32) : bv32 
    requires b1 <= 32;
    { b0 >> b1 }

  function {:opaque} bit_and_uint32(u0:uint32, u1:uint32) : uint32 
  {
    U32(bit_and32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_or_uint32(u0:uint32, u1:uint32) : uint32 
  {
    U32(bit_or32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_mod_uint32(u0:uint32, u1:uint32) : uint32 
    requires u1 != 0;
  {
    reveal B32();
    U32(bit_mod32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_xor_uint32(u0:uint32, u1:uint32) : uint32 
  {
    U32(bit_xor32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_lshift_uint32(u0:uint32, u1:uint32) : uint32 
    requires u1 <= 32;
  {
    bv32_inequality(u1);
    U32(bit_lshift32(B32(u0), B32(u1)))
  }

  function {:opaque} bit_rshift_uint32(u0:uint32, u1:uint32) : uint32 
    requires u1 <= 32;
  {
    bv32_inequality(u1);
    U32(bit_rshift32(B32(u0), B32(u1)))
  }

  // 64 bits
  function {:opaque} bit_and64(b0:bv64, b1:bv64) : bv64 
    { b0 & b1 }

  function {:opaque} bit_or64(b0:bv64, b1:bv64) : bv64 
    { b0 | b1 }

  function {:opaque} bit_mod64(b0:bv64, b1:bv64) : bv64 
    requires b1 != 0;
    { b0 % b1 }

  function {:opaque} bit_xor64(b0:bv64, b1:bv64) : bv64 
    { b0 ^ b1 }

  function {:opaque} bit_lshift64(b0:bv64, b1:bv64) : bv64 
    requires b1 <= 64;
    { b0 << b1 }

  function {:opaque} bit_rshift64(b0:bv64, b1:bv64) : bv64 
    requires b1 <= 64;
    { b0 >> b1 }

  function {:opaque} bit_and_uint64(u0:uint64, u1:uint64) : uint64 
  {
    U64(bit_and64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_or_uint64(u0:uint64, u1:uint64) : uint64 
  {
    U64(bit_or64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_mod_uint64(u0:uint64, u1:uint64) : uint64 
    requires u1 != 0;
  {
    reveal B64();
    U64(bit_mod64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_xor_uint64(u0:uint64, u1:uint64) : uint64 
  {
    U64(bit_xor64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_lshift_uint64(u0:uint64, u1:uint64) : uint64 
    requires u1 <= 64;
  {
    bv64_inequality(u1);
    U64(bit_lshift64(B64(u0), B64(u1)))
  }

  function {:opaque} bit_rshift_uint64(u0:uint64, u1:uint64) : uint64 
    requires u1 <= 64;
  {
    bv64_inequality(u1);
    U64(bit_rshift64(B64(u0), B64(u1)))
  }

  lemma {:axiom} bv_core_properties()
    ensures forall u:uint32 :: U32(B32(u)) == u;
    ensures forall b:bv32 :: B32(U32(b)) == b;
    ensures forall x:uint32, m:uint32 :: 
                   m != 0 && B32(m) != 0 ==> (x % m) == U32(bit_mod32(B32(x), B32(m)));
    ensures forall u:uint64 :: U64(B64(u)) == u;
    ensures forall b:bv64 :: B64(U64(b)) == b;
    ensures forall x:uint64, m:uint64 :: 
                   m != 0 && B64(m) != 0 ==> (x % m) == U64(bit_mod64(B64(x), B64(m)));
  
  // 32 bits
  lemma B32_injective(u0:uint32, u1:uint32)
    ensures u0 == u1 <==> B32(u0) == B32(u1);
  {
    bv_core_properties();
    assert u0 == u1 ==> B32(u0) == B32(u1);
    var b0 := B32(u0);
    var b1 := B32(u1);
    assert b0 == b1 ==> U32(b0) == U32(b1);
  }
  
  lemma U32_injective(b0:bv32, b1:bv32)
    ensures b0 == b1 <==> U32(b0) == U32(b1);
  {
    bv_core_properties();
    assert b0 == b1 ==> U32(b0) == U32(b1);
    var u0 := U32(b0);
    var u1 := U32(b1);
    assert u0 == u1 ==> B32(u0) == B32(u1);
  }

  lemma bv32_injectivity()
    ensures forall u0:uint32, u1:uint32 :: u0 == u1 <==> B32(u0) == B32(u1)
    ensures forall b0, b1 :: b0 == b1 <==> U32(b0) == U32(b1)
  {
    reveal B32(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    reveal U32(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    forall u0:uint32, u1:uint32 ensures u0 == u1 <==> B32(u0) == B32(u1) { B32_injective(u0, u1); }
    forall b0, b1 ensures b0 == b1 <==> U32(b0) == U32(b1) { U32_injective(b0, b1); }
  }

  lemma bv32_inequality(u:uint32)
    requires u <= 32;
    ensures  B32(u) <= 32;
  {
    reveal B32();
    reveal U32();
    bv_core_properties();
    bv32_injectivity();
  }

  // 64 bits
  lemma B64_injective(u0:uint64, u1:uint64)
    ensures u0 == u1 <==> B64(u0) == B64(u1);
  {
    bv_core_properties();
    assert u0 == u1 ==> B64(u0) == B64(u1);
    var b0 := B64(u0);
    var b1 := B64(u1);
    assert b0 == b1 ==> U64(b0) == U64(b1);
  }
  
  lemma U64_injective(b0:bv64, b1:bv64)
    ensures b0 == b1 <==> U64(b0) == U64(b1);
  {
    bv_core_properties();
    assert b0 == b1 ==> U64(b0) == U64(b1);
    var u0 := U64(b0);
    var u1 := U64(b1);
    assert u0 == u1 ==> B64(u0) == B64(u1);
  }

  lemma bv64_injectivity()
    ensures forall u0:uint64, u1:uint64 :: u0 == u1 <==> B64(u0) == B64(u1)
    ensures forall b0, b1 :: b0 == b1 <==> U64(b0) == U64(b1)
  {
    reveal B64(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    reveal U64(); // Without this, Dafny can't seem to translate the forall statement to the forall expression
    forall u0:uint64, u1:uint64 ensures u0 == u1 <==> B64(u0) == B64(u1) { B64_injective(u0, u1); }
    forall b0, b1 ensures b0 == b1 <==> U64(b0) == U64(b1) { U64_injective(b0, b1); }
  }

  lemma bv64_inequality(u:uint64)
    requires u <= 64;
    ensures  B64(u) <= 64;
  {
    reveal B64();
    reveal U64();
    bv_core_properties();
    bv64_injectivity();
  }


  // Example uses
  lemma bv_test(b:bv64)
    //ensures bit_and64(b, 0) == 0;
    //ensures bit_and64(b, 0xFFFFFFFFFFFFFFFF) == b
    ensures bit_xor64(b, 0) == b;
  {
    //reveal bit_and64();
    var all_ones:bv64 := 0xFFFFFFFFFFFFFFFF; 
    //assert bit_and64(b, all_ones) == b;
    reveal_bit_xor64();
  }
  
  lemma bv64_properties()
    ensures forall u0:uint64 :: bit_and_uint64(u0, 0) == 0
  {
    reveal bit_and_uint64();  // Without this, Dafny can't seem to translate the forall statement to the forall expression
    forall u0 ensures bit_and_uint64(u0, 0) == 0 { bv64_properties_specific(u0, 0); }
  }

  lemma bv64_properties_specific(u0:uint64, u1:uint64)
    ensures bit_and_uint64(u0, 0) == 0
    ensures bit_and_uint64(u0, u1) == bit_and_uint64(u1, u0)
    ensures bit_xor_uint64(u0, u0) == 0 
    ensures bit_xor_uint64(u0, u1) == bit_xor_uint64(u1, u0)
  {
    bv_core_properties(); reveal U64(); reveal B64();

    var all_ones:uint64 := 0xFFFFFFFFFFFFFFFF; 
    assert B64(0) == 0; // Help Z3 with constant conversion
    assert B64(all_ones) == 0xFFFFFFFFFFFFFFFF; // Help Z3 with constant conversion

    // AND
    assert bit_and_uint64(u0, 0)  == 0 by { reveal bit_and_uint64(); reveal bit_and64(); }
    assert bit_and_uint64(u0, all_ones)  == u0 by { reveal bit_and_uint64(); reveal bit_and64(); }
    assert bit_and_uint64(u0, u1) == bit_and_uint64(u1, u0) by { reveal bit_and_uint64(); reveal bit_and64(); }

    // OR
    assert bit_or_uint64(u0, 0)  == u0 by { reveal bit_or_uint64(); reveal bit_or64(); }
    assert bit_or_uint64(u0, all_ones)  == all_ones by { reveal bit_or_uint64(); reveal bit_or64(); }
    assert bit_or_uint64(u0, u1) == bit_or_uint64(u1, u0) by { reveal bit_or_uint64(); reveal bit_or64(); }

    // XOR
    assert bit_xor_uint64(u0, u0) == 0 by { reveal bit_xor_uint64(); reveal bit_xor64(); }
    assert bit_xor_uint64(u0, u1) == bit_xor_uint64(u1, u0) by { reveal bit_xor_uint64(); reveal bit_xor64(); }
    assert bit_xor_uint64(u0, 0)  == u0 by { reveal bit_xor_uint64(); reveal bit_xor64(); }
  }
    

//  method bitwise_and(x:uint64, y:uint64) returns (z:uint64)
//    ensures z == bit_and_uint64(x, y)

  ////////////////////////////////
  // Thread handle
  ////////////////////////////////

  type Armada_ThreadHandle = uint64

  ////////////////////////////////
  // Termination
  ////////////////////////////////

  datatype Armada_StopReason = Armada_NotStopped
                             | Armada_StopReasonTerminated
                             | Armada_StopReasonAssertionFailure
                             | Armada_StopReasonUndefinedBehavior

  ////////////////////////////////
  // Multisteps
  ////////////////////////////////

  datatype Armada_SpecFunctions<!State, !OneStep, !PC> =
    Armada_SpecFunctions(
      init:State->bool,
      step_valid:(State, OneStep, Armada_ThreadHandle)->bool,
      step_next:(State, OneStep, Armada_ThreadHandle)->State,
      is_step_tau:OneStep->bool,
      state_ok:State->bool,
      get_thread_pc:(State, Armada_ThreadHandle)->Option<PC>,
      is_pc_nonyielding:PC->bool
      )

  predicate Armada_ThreadYielding<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    tid:Armada_ThreadHandle
    )
  {
    // Either the process has crashed, the thread isn't running, or the thread is at a yield point
    var pc := asf.get_thread_pc(s, tid);
    !asf.state_ok(s) || pc.None? || !asf.is_pc_nonyielding(pc.v)
  }

  predicate Armada_StepsStartNonyielding<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    tid:Armada_ThreadHandle
    )
  {
    |steps| > 0 ==>
      && !Armada_ThreadYielding(asf, s, tid)
      && !asf.is_step_tau(steps[0])
      && Armada_StepsStartNonyielding(asf, asf.step_next(s, steps[0], tid), s', steps[1..], tid)
  }

  predicate Armada_NextMultipleSteps<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    tid:Armada_ThreadHandle
    )
  {
    if |steps| == 0 then
      s' == s
    else
      && asf.step_valid(s, steps[0], tid)
      && Armada_NextMultipleSteps(asf, asf.step_next(s, steps[0], tid), s', steps[1..], tid)
  }

  predicate Armada_NextMultistep<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
  {
    && Armada_NextMultipleSteps(asf, s, s', steps, tid)
    && (|steps| > 0 ==>
       if tau then
         && |steps| == 1
         && asf.is_step_tau(steps[0])
       else
         && Armada_ThreadYielding(asf, s, tid)
         && Armada_ThreadYielding(asf, s', tid)
         && !asf.is_step_tau(steps[0])
         && Armada_StepsStartNonyielding(asf, asf.step_next(s, steps[0], tid), s', steps[1..], tid)
       )
  }

  function Armada_SpecFunctionsToSpec<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    ) : Spec<State>
  {
    Spec(iset s | asf.init(s),
         iset s, s', steps, tid, tau | Armada_NextMultistep(asf, s, s', steps, tid, tau) :: StatePair(s, s'))
  }

  ////////////////////////////////
  // Heap types
  ////////////////////////////////

  datatype Armada_ObjectType = Armada_ObjectTypePrimitive(pty: Armada_PrimitiveType)
                             | Armada_ObjectTypeStruct(fieldTypes: seq<Armada_ObjectType>)
                             | Armada_ObjectTypeArray(subtype: Armada_ObjectType, sz: int)

  ////////////////////////////////
  // Pointers and heaps
  ////////////////////////////////

  type Armada_Pointer = uint64

  function Armada_TriggerPointer(p:Armada_Pointer) : Armada_Pointer { p }

  datatype Armada_RootType = Armada_RootTypeStaticHeap | Armada_RootTypeDynamicHeap | Armada_RootTypeStack

  datatype Armada_ChildType = Armada_ChildTypeRoot(rt: Armada_RootType) | Armada_ChildTypeIndex(i: int)

  datatype Armada_Node = Armada_Node(parent: Armada_Pointer, child_type: Armada_ChildType,
                                     children: seq<Armada_Pointer>, ty: Armada_ObjectType)

  type Armada_HeapValues = map<Armada_Pointer, Armada_PrimitiveValue>

  datatype Armada_Heap = Armada_Heap(tree: map<Armada_Pointer, Armada_Node>, valid: set<Armada_Pointer>, freed: set<Armada_Pointer>,
                                     values: Armada_HeapValues)
    
  predicate Armada_TreeForestProperties(tree: map<Armada_Pointer, Armada_Node>)
  {
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) in tree ==> tree[p].parent in tree)
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) in tree ==> (tree[p].child_type.Armada_ChildTypeRoot? <==> tree[p].parent == p))
    && (forall p, i {:trigger Armada_TriggerPointer(p), tree[p].children[i]} ::
           Armada_TriggerPointer(p) in tree && 0 <= i < |tree[p].children|
           ==> var q := tree[p].children[i]; q in tree && tree[q].parent == p && tree[q].child_type == Armada_ChildTypeIndex(i))
    && (forall q {:trigger Armada_TriggerPointer(q)} ::
           Armada_TriggerPointer(q) in tree && !tree[q].child_type.Armada_ChildTypeRoot?
           ==> var p, f := tree[q].parent, tree[q].child_type;
               p in tree && 0 <= f.i < |tree[p].children| && tree[p].children[f.i] == q)
  }

  predicate Armada_TreeStructProperties(tree: map<Armada_Pointer, Armada_Node>)
  {
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
         Armada_TriggerPointer(p) in tree && tree[p].ty.Armada_ObjectTypeStruct? ==> |tree[p].children| == |tree[p].ty.fieldTypes|)
    && (forall p, i {:trigger Armada_TriggerPointer(p), tree[p].children[i]} ::
         Armada_TriggerPointer(p) in tree && tree[p].ty.Armada_ObjectTypeStruct? && 0 <= i < |tree[p].children| ==>
         var q := tree[p].children[i];
         q in tree && tree[q].ty == tree[p].ty.fieldTypes[i])
  }

  predicate Armada_TreeArrayProperties(tree: map<Armada_Pointer, Armada_Node>)
  {
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) in tree && tree[p].ty.Armada_ObjectTypeArray? ==> tree[p].ty.sz >= 0)
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) in tree && tree[p].ty.Armada_ObjectTypeArray? ==> |tree[p].children| == tree[p].ty.sz)
    && (forall p, q {:trigger Armada_TriggerPointer(p), Armada_TriggerPointer(q), tree[p].ty.Armada_ObjectTypeArray?} ::
           && Armada_TriggerPointer(p) in tree && Armada_TriggerPointer(q) in tree
           && tree[p].ty.Armada_ObjectTypeArray? && tree[q].parent == p && q != p
           ==> tree[q].ty == tree[p].ty.subtype)
  }

  predicate Armada_TreePrimitiveProperties(tree: map<Armada_Pointer, Armada_Node>)
  {
    forall p {:trigger Armada_TriggerPointer(p)} ::
      Armada_TriggerPointer(p) in tree && tree[p].ty.Armada_ObjectTypePrimitive? ==> |tree[p].children| == 0
  }

  predicate Armada_TreeProperties(tree: map<Armada_Pointer, Armada_Node>)
  {
    && Armada_TreeForestProperties(tree)
    && Armada_TreeStructProperties(tree)
    && Armada_TreeArrayProperties(tree)
    && Armada_TreePrimitiveProperties(tree)
  }

  predicate Armada_HeapInvariant(h: Armada_Heap)
  {
    && (forall p :: p in h.valid ==> p !in h.freed)
    && 0 in h.freed
    && !(0 in h.valid)
    && Armada_TreeProperties(h.tree)
    && (forall p {:trigger Armada_TriggerPointer(p)} {:trigger Armada_TriggerPointer(h.tree[p].parent)} :: 
        Armada_TriggerPointer(p) in h.tree ==>
          (p in h.valid <==> Armada_TriggerPointer(h.tree[p].parent) in h.valid))
    && forall p {:trigger Armada_TriggerPointer(p)} :: 
        Armada_TriggerPointer(p) in h.tree &&
        h.tree[p].ty.Armada_ObjectTypePrimitive? ==>
          p in h.values &&
          Armada_PrimitiveValueMatchesType(h.values[p], h.tree[p].ty.pty)
  }

  predicate Armada_HeapMetadataUnchanged(h: Armada_Heap, h': Armada_Heap)
  {
    && h'.tree == h.tree
    && h'.valid == h.valid
    && h'.freed == h.freed
  }

  predicate Armada_ComparablePointer(p: Armada_Pointer, h: Armada_Heap)
  {
    p !in h.freed || p == 0
  }

  /////////////////////////////////////////////
  // Pointer subtree structural correctness
  /////////////////////////////////////////////

  predicate Armada_PointerSubtreeHasObjectType(tree: map<Armada_Pointer, Armada_Node>, p: Armada_Pointer, ty: Armada_ObjectType)
    decreases ty
  {
    && p in tree
    && tree[p].ty == ty
    && match tree[p].ty
        case Armada_ObjectTypePrimitive(pty) =>
          |tree[p].children| == 0
        case Armada_ObjectTypeStruct(fieldTypes) =>
          && |tree[p].children| == |fieldTypes|
          && (forall i {:trigger tree[p].children[i]} :: 0 <= i < |fieldTypes| ==>
               Armada_PointerSubtreeHasObjectType(tree, tree[p].children[i], fieldTypes[i]))
        case Armada_ObjectTypeArray(subtype, sz) =>
          && |tree[p].children| == sz
          && (forall i {:trigger tree[p].children[i]} :: 0 <= i < sz ==>
               Armada_PointerSubtreeHasObjectType(tree, tree[p].children[i], subtype))
  }

  predicate Armada_PointerSubtreeCorrect(tree: map<Armada_Pointer, Armada_Node>, p: Armada_Pointer)
  {
    p in tree && Armada_PointerSubtreeHasObjectType(tree, p, tree[p].ty)
  }

  ////////////////////////////////////
  // Descendants in heap tree
  ////////////////////////////////////

  function Armada_DescendantsOfPointerToObjectType(
    tree: map<Armada_Pointer, Armada_Node>,
    p: Armada_Pointer,
    ty: Armada_ObjectType
    ) : set<Armada_Pointer>
    decreases ty
  {
    match ty
      case Armada_ObjectTypePrimitive(_) =>
        {Armada_TriggerPointer(p)}
      case Armada_ObjectTypeStruct(fieldTypes) =>
        {Armada_TriggerPointer(p)}
        + (set q, i, ty {:trigger q in Armada_DescendantsOfPointerToObjectType(tree, tree[p].children[i], ty)}
            | && p in tree
              && 0 <= i < |tree[p].children| && i < |fieldTypes|
              && ty == fieldTypes[i]
              && q in Armada_DescendantsOfPointerToObjectType(tree, tree[p].children[i], ty)
            :: Armada_TriggerPointer(q))
      case Armada_ObjectTypeArray(subtype, _) =>
        {Armada_TriggerPointer(p)}
        + (set q, i {:trigger q in Armada_DescendantsOfPointerToObjectType(tree, tree[p].children[i], subtype)}
            | && p in tree
              && 0 <= i < |tree[p].children|
              && q in Armada_DescendantsOfPointerToObjectType(tree, tree[p].children[i], subtype)
            :: Armada_TriggerPointer(q))
  }

  function Armada_DescendantsOfPointer(tree: map<Armada_Pointer, Armada_Node>, p: Armada_Pointer) : set<Armada_Pointer>
    requires p in tree
  {
    Armada_DescendantsOfPointerToObjectType(tree, p, tree[p].ty)
  }

  ////////////////////////////////////
  // Pointer validity
  ////////////////////////////////////

  function Armada_ValidPointerToObjectType(h: Armada_Heap, p: Armada_Pointer, ty: Armada_ObjectType) : (b: bool)
    ensures  b ==> Armada_PointerSubtreeHasObjectType(h.tree, p, ty)
    decreases ty
  {
    && Armada_TriggerPointer(p) in h.tree
    && p in h.valid
    && h.tree[p].ty == ty
    && match h.tree[p].ty
        case Armada_ObjectTypePrimitive(pty) =>
          && |h.tree[p].children| == 0
          && p in h.values
          && Armada_PrimitiveValueMatchesType(h.values[p], pty)
        case Armada_ObjectTypeStruct(fieldTypes) =>
          && |h.tree[p].children| == |fieldTypes|
          && (forall i {:trigger h.tree[p].children[i]} :: 0 <= i < |fieldTypes| ==>
               Armada_ValidPointerToObjectType(h, h.tree[p].children[i], fieldTypes[i]))
        case Armada_ObjectTypeArray(subtype, sz) =>
          && |h.tree[p].children| == sz
          && (forall i {:trigger h.tree[p].children[i]} :: 0 <= i < sz ==>
               Armada_ValidPointerToObjectType(h, h.tree[p].children[i], subtype))
  }

  function Armada_ValidPointer(h: Armada_Heap, p: Armada_Pointer) : (b: bool)
    ensures  b ==> Armada_PointerSubtreeCorrect(h.tree, p)
  {
    p in h.tree && Armada_ValidPointerToObjectType(h, p, h.tree[p].ty)
  }

  ////////////////////////////////////
  // Updating heap via pointers
  ////////////////////////////////////

  function Armada_UpdateHeapValuesWithPrimitiveValue(
    values: map<Armada_Pointer, Armada_PrimitiveValue>,
    p: Armada_Pointer,
    new_value: Armada_PrimitiveValue
    ) : (
    new_values: map<Armada_Pointer, Armada_PrimitiveValue>
    )
  {
    map q | q in values :: if q == p then new_value else values[q]
  }

  predicate Armada_ArbitrarilyResolveConflictingUpdatesTrigger(p: Armada_Pointer)
  {
    true
  }

  function {:opaque} Armada_ArbitrarilyResolveConflictingUpdates(update_set: set<(Armada_Pointer, Armada_PrimitiveValue)>)
    : (update_map : map<Armada_Pointer, Armada_PrimitiveValue>)
    ensures forall p :: p in update_map ==> (p, update_map[p]) in update_set
    ensures forall p, v :: (p, v) in update_set ==> p in update_map
  {
    map p {:trigger Armada_ArbitrarilyResolveConflictingUpdatesTrigger(p)}
          | Armada_ArbitrarilyResolveConflictingUpdatesTrigger(p) && (exists v :: (p, v) in update_set)
          :: (var v :| (p, v) in update_set; v)
  }

  function Armada_UpdateHeapValuesSimultaneously(
    values: Armada_HeapValues,
    updates: set<(Armada_Pointer, Armada_PrimitiveValue)>
    ) : (
    values': Armada_HeapValues
    )
  {
    var update_map := Armada_ArbitrarilyResolveConflictingUpdates(updates);
    map p | p in values :: if p in update_map then update_map[p] else values[p]
  }
   
  ////////////////////////////////
  // Configuration
  ////////////////////////////////

  datatype Armada_Config = Armada_Config(tid_init: Armada_ThreadHandle, new_ptrs: set<Armada_Pointer>)

  ////////////////////////////////
  // Placeholder types
  ////////////////////////////////

  type ArmadaPlaceholder_ExtendedFrame
  datatype ArmadaPlaceholder_StoreBufferEntry = ArmadaPlaceholder_StoreBufferEntry(value: Armada_PrimitiveValue)
  datatype ArmadaPlaceholder_Thread =
    ArmadaPlaceholder_Thread(stack: seq<ArmadaPlaceholder_ExtendedFrame>, storeBuffer: seq<ArmadaPlaceholder_StoreBufferEntry>)
  datatype ArmadaPlaceholder_TotalState =
    ArmadaPlaceholder_TotalState(stop_reason: Armada_StopReason, threads: map<Armada_ThreadHandle, ArmadaPlaceholder_Thread>,
                                 joinable_tids: set<Armada_ThreadHandle>)

}
