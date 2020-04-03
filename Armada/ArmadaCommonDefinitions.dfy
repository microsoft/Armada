include "util/collections/seqs.i.dfy"
include "util/option.s.dfy"

module ArmadaCommonDefinitions {

  import opened util_collections_seqs_i
  import opened util_option_s

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

  datatype Armada_Multistep<OneStep> = Armada_Multistep(steps:seq<OneStep>, tid:Armada_ThreadHandle, tau:bool)

  datatype Armada_SpecFunctions<!State, !OneStep, !PC> =
    Armada_SpecFunctions(
      init:State->bool,
      step_valid:(State, OneStep)->bool,
      step_next:(State, OneStep)->State,
      step_to_thread:OneStep->Armada_ThreadHandle,
      is_step_tau:OneStep->bool,
      state_ok:State->bool,
      get_thread_pc:(State, Armada_ThreadHandle)->Option<PC>,
      is_pc_nonyielding:PC->bool
      )

  predicate Armada_NextMultipleSteps<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>
    )
  {
    if |steps| == 0 then
      s' == s
    else
      asf.step_valid(s, steps[0]) && Armada_NextMultipleSteps(asf, asf.step_next(s, steps[0]), s', steps[1..])
  }

  function Armada_GetStateSequence<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    steps:seq<OneStep>
    ) : (states:seq<State>)
    ensures |states| == |steps| + 1
    ensures states[0] == s
    decreases |steps|
  {
    if |steps| == 0 then
      [s]
    else
      [s] + Armada_GetStateSequence(asf, asf.step_next(s, steps[0]), steps[1..])
  }

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

  predicate Armada_NextMultistep<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
  {
    && Armada_NextMultipleSteps(asf, s, s', steps)
    && (forall step :: step in steps ==> asf.step_to_thread(step) == tid)
    && (forall step :: step in steps ==> asf.is_step_tau(step) == tau)
    && if tau then |steps| <= 1 else |steps| > 0 ==> (
        && Armada_ThreadYielding(asf, s, tid)
        && Armada_ThreadYielding(asf, s', tid)
        && (forall i {:trigger Armada_GetStateSequence(asf, s, steps)[i]} ::
               0 < i < |steps| ==> !Armada_ThreadYielding(asf, Armada_GetStateSequence(asf, s, steps)[i], tid))
      )
  }

  ////////////////////////////////
  // Pointers and heaps
  ////////////////////////////////

  type Armada_Pointer = uint64

  datatype Armada_RootType = Armada_RootTypeStaticHeap | Armada_RootTypeDynamicHeap | Armada_RootTypeStack

  datatype Armada_FieldGeneric<F> = Armada_FieldNone(rt:Armada_RootType) | Armada_FieldArrayIndex(i: int) | Armada_FieldStruct(f: F)

  datatype Armada_ObjectTypeGeneric<S> = Armada_ObjectType_primitive(pty: Armada_PrimitiveType) | Armada_ObjectType_struct(s: S) | Armada_ObjectType_array(subtype: Armada_ObjectTypeGeneric<S>, sz: int)

  datatype Armada_NodeGeneric<S, F(==)> = Armada_Node(parent: Armada_Pointer, field_of_parent: Armada_FieldGeneric<F>, children: map<Armada_FieldGeneric<F>, Armada_Pointer>, ty: Armada_ObjectTypeGeneric<S>, lvl: int)

  datatype Armada_HeapGeneric<S, F> = Armada_Heap(tree: map<Armada_Pointer, Armada_NodeGeneric<S, F>>, valid: set<Armada_Pointer>, freed: set<Armada_Pointer>, values: map<Armada_Pointer, Armada_PrimitiveValue>)

  predicate Armada_TriggerPointer(p:Armada_Pointer) { true }
  predicate Armada_TriggerIndex(i:int) { true }
  predicate Armada_TriggerField<F>(f:Armada_FieldGeneric<F>) { true }
    
  predicate Armada_TreeForestProperties<S, F>(tree: map<Armada_Pointer, Armada_NodeGeneric<S, F>>)
  {
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) && p in tree
           ==> tree[p].lvl >= 0)
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) && p in tree
           ==> tree[p].parent in tree)
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) && p in tree
           ==> tree[p].lvl == if tree[p].parent == p then 0 else tree[tree[p].parent].lvl + 1)
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) && p in tree
           ==> (tree[p].field_of_parent.Armada_FieldNone? <==> tree[p].parent == p))
    && (forall p, f {:trigger Armada_TriggerPointer(p), Armada_TriggerField(f)} ::
           Armada_TriggerPointer(p) && Armada_TriggerField(f) && p in tree && f in tree[p].children
           ==> var q := tree[p].children[f]; q in tree && tree[q].parent == p && tree[q].field_of_parent == f)
    && (forall q {:trigger Armada_TriggerPointer(q)} ::
           Armada_TriggerPointer(q) && q in tree && !tree[q].field_of_parent.Armada_FieldNone?
           ==> var p, f := tree[q].parent, tree[q].field_of_parent; p in tree && f in tree[p].children && tree[p].children[f] == q)
  }

  predicate Armada_TreeArrayProperties<S, F>(tree: map<Armada_Pointer, Armada_NodeGeneric<S, F>>)
  {
    && (forall p {:trigger Armada_TriggerPointer(p)} ::
           Armada_TriggerPointer(p) && p in tree && tree[p].ty.Armada_ObjectType_array?
           ==> tree[p].ty.sz >= 0)
    && (forall p, i {:trigger Armada_TriggerPointer(p), Armada_TriggerIndex(i)} ::
           Armada_TriggerPointer(p) && Armada_TriggerIndex(i) && p in tree && tree[p].ty.Armada_ObjectType_array? && 0 <= i < tree[p].ty.sz
           ==> Armada_FieldArrayIndex(i) in tree[p].children)
    && (forall p, f {:trigger Armada_TriggerPointer(p), Armada_TriggerField(f)} ::
           Armada_TriggerPointer(p) && Armada_TriggerField(f) && p in tree && tree[p].ty.Armada_ObjectType_array? && f in tree[p].children
           ==> f.Armada_FieldArrayIndex? && 0 <= f.i < tree[p].ty.sz)
    && (forall p, q {:trigger Armada_TriggerPointer(p), Armada_TriggerPointer(q)} ::
           Armada_TriggerPointer(p) && Armada_TriggerPointer(q)
               && p in tree && q in tree && tree[p].ty.Armada_ObjectType_array? && tree[q].parent == p && q != p
           ==> tree[q].ty == tree[p].ty.subtype)
  }

  predicate Armada_TreePrimitiveProperties<S, F(!new)>(tree: map<Armada_Pointer, Armada_NodeGeneric<S, F>>)
  {
    forall p, f {:trigger Armada_TriggerPointer(p), Armada_TriggerField(f)} ::
        Armada_TriggerPointer(p) && Armada_TriggerField(f) && p in tree && tree[p].ty.Armada_ObjectType_primitive?
        ==> f !in tree[p].children
  }

  predicate Armada_PointerIsAncestorOfPointer<S, F>(tree: map<Armada_Pointer, Armada_NodeGeneric<S, F>>, p: Armada_Pointer, q: Armada_Pointer)
    requires Armada_TreeForestProperties(tree)
    requires p in tree
    requires q in tree
    requires Armada_TriggerPointer(p)
    requires Armada_TriggerPointer(q)
    decreases tree[q].lvl
  {
    p == q || (!tree[q].field_of_parent.Armada_FieldNone? && Armada_PointerIsAncestorOfPointer(tree, p, tree[q].parent))
  }

  predicate Armada_DisjointPointers<S, F>(tree: map<Armada_Pointer, Armada_NodeGeneric<S, F>>, p: Armada_Pointer, q: Armada_Pointer)
    requires p in tree
    requires q in tree
    requires Armada_TreeForestProperties(tree)
  {
    && !Armada_PointerIsAncestorOfPointer(tree, p, q)
    && !Armada_PointerIsAncestorOfPointer(tree, q, p)
  }

  function Armada_UpdateHeapValues(values: map<Armada_Pointer, Armada_PrimitiveValue>, p: Armada_Pointer, new_value: Armada_PrimitiveValue): (new_values: map<Armada_Pointer, Armada_PrimitiveValue>)
    ensures  new_values.Keys == values.Keys + {p}
    ensures  p in new_values
    ensures  new_values[p] == new_value
    ensures  forall other :: other in values && other != p ==> other in new_values && new_values[other] == values[other]
  {
    var s:set<Armada_Pointer> := values.Keys + {p};
    map q | q in s :: if q == p then new_value else values[q]
  }

  predicate Armada_ComparablePointer<S, F>(p: Armada_Pointer, h: Armada_HeapGeneric<S, F>)
  {
    p !in h.freed || p == 0
  }

  predicate Armada_ValidPointerToPrimitive<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, pty:Armada_PrimitiveType)
  {
    && p in h.valid
    && p in h.tree
    && p in h.values
    && h.tree[p].ty.Armada_ObjectType_primitive?
    && h.tree[p].ty.pty == pty
    && Armada_PrimitiveValueMatchesType(h.values[p], pty)
  }

  predicate Armada_ValidPointerToPrimitiveArray<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, pty:Armada_PrimitiveType)
  {
    && p in h.valid
    && p in h.tree
    && var ty := h.tree[p].ty; ty.Armada_ObjectType_array? && ty.subtype.Armada_ObjectType_primitive? && ty.subtype.pty == pty && ty.sz >= 0 && forall i :: 0 <= i < ty.sz ==> var idx := Armada_FieldArrayIndex(i); idx in h.tree[p].children && Armada_ValidPointerToPrimitive(h, h.tree[p].children[idx], pty)
  }

  predicate Armada_ValidPointerToPrimitiveSizedArray<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, pty:Armada_PrimitiveType, sz: int)
  {
    && sz >= 0
    && Armada_ValidPointerToPrimitiveArray(h, p, pty)
    && h.tree[p].ty.sz == sz
  }

  function Armada_DereferencePointerToPrimitive_uint8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): uint8
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_uint8)
  {
    h.values[p].n_uint8
  }

  function Armada_DereferencePointerToPrimitiveArray_uint8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<uint8>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_uint8)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_uint8(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_uint8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: uint8): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_uint8(value)))
  }

  function Armada_UpdateChildToPrimitive_uint8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: uint8): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_uint8(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_uint8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<uint8>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_uint8(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_uint8(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_uint8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<uint8>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_uint8(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_uint8<F>(v:uint8, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : uint8
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_uint8? then
        value.n_uint8
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_uint8<F>(v:seq<uint8>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<uint8>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_uint8? then
        v[fields[0].i := value.n_uint8]
    else
        v
  }

  function Armada_DereferencePointerToPrimitive_uint16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): uint16
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_uint16)
  {
    h.values[p].n_uint16
  }

  function Armada_DereferencePointerToPrimitiveArray_uint16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<uint16>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_uint16)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_uint16(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_uint16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: uint16): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_uint16(value)))
  }

  function Armada_UpdateChildToPrimitive_uint16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: uint16): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_uint16(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_uint16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<uint16>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_uint16(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_uint16(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_uint16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<uint16>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_uint16(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_uint16<F>(v:uint16, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : uint16
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_uint16? then
        value.n_uint16
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_uint16<F>(v:seq<uint16>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<uint16>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_uint16? then
        v[fields[0].i := value.n_uint16]
    else
        v
  }

  function Armada_DereferencePointerToPrimitive_uint32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): uint32
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_uint32)
  {
    h.values[p].n_uint32
  }

  function Armada_DereferencePointerToPrimitiveArray_uint32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<uint32>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_uint32)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_uint32(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_uint32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: uint32): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_uint32(value)))
  }

  function Armada_UpdateChildToPrimitive_uint32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: uint32): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_uint32(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_uint32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<uint32>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_uint32(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_uint32(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_uint32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<uint32>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_uint32(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_uint32<F>(v:uint32, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : uint32
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_uint32? then
        value.n_uint32
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_uint32<F>(v:seq<uint32>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<uint32>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_uint32? then
        v[fields[0].i := value.n_uint32]
    else
        v
  }

  function Armada_DereferencePointerToPrimitive_uint64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): uint64
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_uint64)
  {
    h.values[p].n_uint64
  }

  function Armada_DereferencePointerToPrimitiveArray_uint64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<uint64>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_uint64)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_uint64(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_uint64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: uint64): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_uint64(value)))
  }

  function Armada_UpdateChildToPrimitive_uint64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: uint64): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_uint64(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_uint64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<uint64>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_uint64(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_uint64(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_uint64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<uint64>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_uint64(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_uint64<F>(v:uint64, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : uint64
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_uint64? then
        value.n_uint64
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_uint64<F>(v:seq<uint64>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<uint64>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_uint64? then
        v[fields[0].i := value.n_uint64]
    else
        v
  }

  function Armada_DereferencePointerToPrimitive_int8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): int8
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_int8)
  {
    h.values[p].n_int8
  }

  function Armada_DereferencePointerToPrimitiveArray_int8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<int8>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_int8)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_int8(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_int8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: int8): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_int8(value)))
  }

  function Armada_UpdateChildToPrimitive_int8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: int8): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_int8(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_int8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<int8>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_int8(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_int8(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_int8<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<int8>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_int8(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_int8<F>(v:int8, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : int8
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_int8? then
        value.n_int8
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_int8<F>(v:seq<int8>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<int8>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_int8? then
        v[fields[0].i := value.n_int8]
    else
        v
  }

  function Armada_DereferencePointerToPrimitive_int16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): int16
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_int16)
  {
    h.values[p].n_int16
  }

  function Armada_DereferencePointerToPrimitiveArray_int16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<int16>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_int16)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_int16(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_int16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: int16): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_int16(value)))
  }

  function Armada_UpdateChildToPrimitive_int16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: int16): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_int16(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_int16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<int16>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_int16(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_int16(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_int16<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<int16>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_int16(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_int16<F>(v:int16, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : int16
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_int16? then
        value.n_int16
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_int16<F>(v:seq<int16>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<int16>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_int16? then
        v[fields[0].i := value.n_int16]
    else
        v
  }

  function Armada_DereferencePointerToPrimitive_int32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): int32
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_int32)
  {
    h.values[p].n_int32
  }

  function Armada_DereferencePointerToPrimitiveArray_int32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<int32>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_int32)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_int32(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_int32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: int32): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_int32(value)))
  }

  function Armada_UpdateChildToPrimitive_int32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: int32): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_int32(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_int32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<int32>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_int32(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_int32(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_int32<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<int32>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_int32(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_int32<F>(v:int32, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : int32
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_int32? then
        value.n_int32
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_int32<F>(v:seq<int32>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<int32>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_int32? then
        v[fields[0].i := value.n_int32]
    else
        v
  }

  function Armada_DereferencePointerToPrimitive_int64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): int64
    requires Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_int64)
  {
    h.values[p].n_int64
  }

  function Armada_DereferencePointerToPrimitiveArray_int64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer): seq<int64>
    requires Armada_ValidPointerToPrimitiveArray(h, p, Armada_PrimitiveType_int64)
  {
    ConvertMapToSeq(h.tree[p].ty.sz, map i | 0 <= i < h.tree[p].ty.sz :: Armada_DereferencePointerToPrimitive_int64(h, h.tree[p].children[Armada_FieldArrayIndex(i)]))
  }

  function Armada_UpdatePointerToPrimitive_int64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, value: int64): Armada_HeapGeneric<S, F>
  {
    h.(values := Armada_UpdateHeapValues(h.values, p, Armada_PrimitiveValue_int64(value)))
  }

  function Armada_UpdateChildToPrimitive_int64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, value: int64): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitive_int64(h, h.tree[p].children[field], value)
    else
      h
  }

  function Armada_UpdatePointerToPrimitiveArray_int64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, a: seq<int64>): Armada_HeapGeneric<S, F>
    decreases |a|
  {
    if |a| == 0 then
      h
    else
      var new_heap := Armada_UpdateChildToPrimitive_int64(h, p, Armada_FieldArrayIndex(|a| - 1), a[|a| - 1]); Armada_UpdatePointerToPrimitiveArray_int64(new_heap, p, a[..|a| - 1])
  }

  function Armada_UpdateChildToPrimitiveArray_int64<S, F>(h: Armada_HeapGeneric<S, F>, p: Armada_Pointer, field: Armada_FieldGeneric<F>, a: seq<int64>): Armada_HeapGeneric<S, F>
  {
    if p in h.tree && field in h.tree[p].children then
      Armada_UpdatePointerToPrimitiveArray_int64(h, h.tree[p].children[field], a)
    else
      h
  }

  function Armada_PerformFieldUpdateForPrimitive_int64<F>(v:int64, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : int64
  {
    if |fields| == 0 && value.Armada_PrimitiveValue_int64? then
        value.n_int64
    else
        v
  }

  function Armada_PerformFieldUpdateForPrimitiveArray_int64<F>(v:seq<int64>, fields:seq<Armada_FieldGeneric<F>>, value:Armada_PrimitiveValue) : seq<int64>
  {
    if |fields| == 1 && fields[0].Armada_FieldArrayIndex? && fields[0].i >= 0 && fields[0].i < |v| && value.Armada_PrimitiveValue_int64? then
        v[fields[0].i := value.n_int64]
    else
        v
  }

  function Armada_AllocatedByPrimitive(h: Armada_HeapGeneric, p: Armada_Pointer, pty:Armada_PrimitiveType): set<Armada_Pointer>
    requires Armada_ValidPointerToPrimitive(h, p, pty)
  {
    {p}
  }

  function Armada_AllocatedByPrimitiveArray(h: Armada_HeapGeneric, p: Armada_Pointer, pty:Armada_PrimitiveType): set<Armada_Pointer>
    requires Armada_ValidPointerToPrimitiveArray(h, p, pty)
  {
    {p} + set i | 0 <= i < h.tree[p].ty.sz :: var idx := Armada_FieldArrayIndex(i); h.tree[p].children[idx]
  }
}
