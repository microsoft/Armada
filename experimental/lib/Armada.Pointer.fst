module Armada.Pointer

open Armada.Base

type t =
  | PointerUninitialized: t
  | PointerNull: t
  | PointerRoot: (root_id: root_id_t) -> t
  | PointerField: (struct_ptr: t) -> (field_id: nat) -> t
  | PointerIndex: (array_ptr: t) -> (idx: nat) -> t

let rec pointer_root (p: t) : option root_id_t =
  match p with
  | PointerUninitialized -> None
  | PointerNull -> None
  | PointerRoot root -> Some root
  | PointerField struct_ptr _ -> pointer_root struct_ptr
  | PointerIndex array_ptr _ -> pointer_root array_ptr
