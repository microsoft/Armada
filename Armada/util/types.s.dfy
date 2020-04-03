module util_types_s {

    newtype byte = x:int | 0 <= x < 0x100
    newtype uint = x:int | 0 <= x < 0x1_0000_0000

}
