module Armada.Globals

type var_index = nat

type t = Spec.Map.t var_index (option int)
