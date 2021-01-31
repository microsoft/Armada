//  mask == 2^x as "mask+1 & (mask) ) == 0

newtype uint32 = n: int | 0 <= n < 4294967296

method bitwise_and(x:uint32, y:uint32) returns (z:uint32)
  ensures z == bit_and_uint32(x, y)

function {:opaque} U(b:bv32) : uint32 { b as uint32 }
function {:opaque} B(u:uint32) : bv32 { u as bv32 }

function {:opaque} bit_lshift(b0:bv32, amt:nat) : bv32
  requires amt < 32;
{
  b0 << amt
}

function {:opaque} bit_and(b0:bv32, b1:bv32) : bv32 
  { b0 & b1 }

function {:opaque} bit_mod(b0:bv32, b1:bv32) : bv32 
  requires b1 != 0;
  { b0 % b1 }

function {:opaque} bit_mod_uint32(u0:uint32, u1:uint32) : uint32 
  requires u1 != 0;
{
  reveal B();
  U(bit_mod(B(u0), B(u1)))
}

function {:opaque} bit_and_uint32(x:uint32, y:uint32) : uint32
{
  U(bit_and(B(x), B(y)))
}

lemma {:axiom} bv_properties()
  ensures forall u:uint32 :: U(B(u)) == u;
  ensures forall b:bv32 :: B(U(b)) == b;
  ensures forall x:uint32, m:uint32 :: 
                 m != 0 && B(m) != 0 ==> (x % m) == U(bit_mod(B(x), B(m)));

lemma mask_equiv_bv(y:bv32)
  ensures y % 512 == y & 511;
{
}

lemma mask_equiv_bv_wrapped(y:bv32)
  ensures bit_mod(y, 512) == bit_and(y, 511);
{
  reveal bit_mod();
  reveal bit_and();
}

lemma mask_equiv_wrapped(x:uint32)
  ensures bit_mod_uint32(x, 512) == bit_and_uint32(x, 511);
{
  assert B(512) == 512 by { reveal B(); }
  assert B(511) == 511 by { reveal B(); }
  calc {
    bit_mod_uint32(x, 512);
      { reveal bit_mod_uint32(); reveal B(); }
    U(bit_mod(B(x), B(512)));
      { mask_equiv_bv_wrapped(B(x)); assert bit_mod(B(x), 512) == bit_and(B(x), 511); }
    U(bit_and(B(x), B(511)));
      { reveal bit_and_uint32(); }
    bit_and_uint32(x, 511);
  }
}

lemma bit_mod_equiv(u0:uint32, u1:uint32)
  requires u1 != 0;
  ensures bit_mod_uint32(u0, u1) == u0 % u1;
{
  reveal bit_mod_uint32();
  bv_properties();
  assert B(u1) != 0 by { reveal B(); }
  assert bit_mod(B(u0), B(u1)) >= 0;
}

lemma mask_equiv(x:uint32)
  ensures x % 512 == bit_and_uint32(x, 511);
{
  calc {
    x % 512;
      { bit_mod_equiv(x, 512); }
    bit_mod_uint32(x, 512);
      { mask_equiv_wrapped(x); }
    bit_and_uint32(x, 511);
  }
}

lemma armada_mask_equiv(x:uint32)
  ensures ((x as bv32) & (511 as bv32)) as uint32 == x % 512
{
  calc {
    (x as bv32 & 511 as bv32) as uint32;
      { reveal U(); }
    U(x as bv32 & 511 as bv32); 
      { reveal B(); }
    U(B(x) & B(511)); 
      { reveal bit_and(); }
    U(bit_and(B(x), B(511))); 
      { reveal bit_and_uint32(); }
    bit_and_uint32(x, 511);
      { mask_equiv(x); }
    x % 512;
  }
}


