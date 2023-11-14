module Armada.Base

type tid_t = nat
type var_id_t = string
type method_id_t = string
type pc_t = string
type root_id_uniquifier_t = nat

type root_id_t =
  | RootIdGlobal: (var_id: var_id_t) -> root_id_t
  | RootIdStack: (tid: tid_t) -> (method_id: method_id_t) -> (frame_uniq: root_id_uniquifier_t) ->
                 (var_id: var_id_t) -> root_id_t
  | RootIdAllocation: (allocation_uniq: root_id_uniquifier_t) -> root_id_t
  | RootIdFence: root_id_t

