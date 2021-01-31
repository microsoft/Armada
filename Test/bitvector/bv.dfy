include "../../Armada/ArmadaCommonDefinitions.dfy"

module BitVectorTest1 {

import opened ArmadaCommonDefinitions


lemma mask_equiv_bv_wrapped(y:bv32)
  ensures bit_mod32(y, 512) == bit_and32(y, 511);
{
  reveal bit_mod32();
  reveal bit_and32();
}

lemma mask_equiv_wrapped(x:uint32)
  ensures bit_mod_uint32(x, 512) == bit_and_uint32(x, 511);
{
  assert B32(512) == 512 by { reveal B32(); }
  assert B32(511) == 511 by { reveal B32(); }
  calc {
    bit_mod_uint32(x, 512);
      { reveal bit_mod_uint32(); reveal B32(); }
    U32(bit_mod32(B32(x), B32(512)));
      { mask_equiv_bv_wrapped(B32(x)); assert bit_mod32(B32(x), 512) == bit_and32(B32(x), 511); }
    U32(bit_and32(B32(x), B32(511)));
      { reveal bit_and_uint32(); }
    bit_and_uint32(x, 511);
  }
}


lemma bit_mod_equiv(u0:uint32, u1:uint32)
  requires u1 != 0;
  ensures bit_mod_uint32(u0, u1) == u0 % u1;
{
  reveal bit_mod_uint32();
  bv_core_properties();
  assert B32(u1) != 0 by { reveal B32(); }
  assert bit_mod32(B32(u0), B32(u1)) >= 0;
}

lemma mask_equiv_specific(x:uint32)
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


lemma mask_equiv()
  ensures forall x:uint32 :: x % 512 == bit_and_uint32(x, 511);
{
   reveal bit_and_uint32();  // Without this, Dafny can't seem to translate the forall statement to the forall expression

  forall x:uint32 
    ensures x % 512 == bit_and_uint32(x, 511);
  {
    mask_equiv_specific(x);
  }
}

}

