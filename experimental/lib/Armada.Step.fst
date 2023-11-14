module Armada.Step

open Armada.Action
open Armada.Base
open Armada.Type

noeq type t = {
  nd: nondeterminism_t;
  action: Armada.Action.t;
}
