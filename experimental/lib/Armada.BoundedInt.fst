module Armada.BoundedInt

type int8 = n: int{-0x80 <= n && n < 0x80}
type int16 = n: int{-0x8000 <= n && n < 0x8000}
type int32 = n: int{-0x80000000 <= n && n < 0x80000000}
type int64 = n: int{-0x8000000000000000 <= n && n < 0x8000000000000000}
type uint8 = n: nat{n < 0x100}
type uint16 = n: nat{n < 0x10000}
type uint32 = n: nat{n < 0x100000000}
type uint64 = n: nat{n < 0x10000000000000000}

type bounded_int_type_t =
  | MachineInt8
  | MachineInt16
  | MachineInt32
  | MachineInt64
  | MachineUint8
  | MachineUint16
  | MachineUint32
  | MachineUint64

let bt_to_ty (bt: bounded_int_type_t) : Type =
  match bt with
  | MachineInt8 -> int8
  | MachineInt16 -> int16
  | MachineInt32 -> int32
  | MachineInt64 -> int64
  | MachineUint8 -> uint8
  | MachineUint16 -> uint16
  | MachineUint32 -> uint32
  | MachineUint64 -> uint64

let is_signed (bt: bounded_int_type_t) : GTot bool =
  match bt with
  | MachineInt8 | MachineInt16 | MachineInt32 | MachineInt64 -> true
  | _ -> false

private let fit_hidden (bt: bounded_int_type_t) (n: int) : (bt_to_ty bt) =
  match bt with
  | MachineInt8 -> (n + 0x80) % 0x100 - 0x80
  | MachineInt16 -> (n + 0x8000) % 0x10000 - 0x8000
  | MachineInt32 -> (n + 0x80000000) % 0x100000000 - 0x80000000
  | MachineInt64 -> (n + 0x8000000000000000) % 0x10000000000000000 - 0x8000000000000000
  | MachineUint8 -> n % 0x100
  | MachineUint16 -> n % 0x10000
  | MachineUint32 -> n % 0x100000000
  | MachineUint64 -> n % 0x10000000000000000

[@"opaque_to_smt"]
let fit = fit_hidden

let reveal_fit () : Lemma (fit == fit_hidden) = 
  reveal_opaque (`%fit) fit

let fit_is_identity_if_already_fits (bt: bounded_int_type_t) (n: bt_to_ty bt)
  : Lemma (ensures (n = fit bt n))
          [SMTPat (fit bt n)] =
  reveal_fit ()

let add (bt: bounded_int_type_t) (x: bt_to_ty bt) (y: bt_to_ty bt) : (bt_to_ty bt) =
  fit bt (x + y)

let sub (bt: bounded_int_type_t) (x: bt_to_ty bt) (y: bt_to_ty bt) : (bt_to_ty bt) =
  fit bt (x - y)

let div (bt: bounded_int_type_t) (x: bt_to_ty bt) (y: bt_to_ty bt{y <> 0}) : (bt_to_ty bt) =
  fit bt (x / y)

let mod (bt: bounded_int_type_t) (x: bt_to_ty bt) (y: bt_to_ty bt{y <> 0}) : (bt_to_ty bt) =
  fit bt (x % y)

let double_bt_size (bt: bounded_int_type_t) : bounded_int_type_t =
  match bt with
  | MachineInt8 -> MachineInt16
  | MachineInt16 -> MachineInt32
  | MachineInt32 -> MachineInt64
  | MachineInt64 -> MachineInt64
  | MachineUint8 -> MachineUint16
  | MachineUint16 -> MachineUint32
  | MachineUint32 -> MachineUint64
  | MachineUint64 -> MachineUint64

let num_bits_in_bounded_int_type (bt: bounded_int_type_t) : int =
  match bt with
  | MachineInt8 -> 8
  | MachineInt16 -> 16
  | MachineInt32 -> 32
  | MachineInt64 -> 64
  | MachineUint8 -> 8
  | MachineUint16 -> 16
  | MachineUint32 -> 32
  | MachineUint64 -> 64

let mul (bt: bounded_int_type_t) (x: bt_to_ty bt) (y: bt_to_ty bt) : (bt_to_ty (double_bt_size bt)) =
  fit (double_bt_size bt) (x `op_Multiply` y)
