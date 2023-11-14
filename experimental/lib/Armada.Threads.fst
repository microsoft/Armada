module Armada.Threads

open Armada.Base
open Armada.Thread

type t = Spec.Map.t tid_t Armada.Thread.t
