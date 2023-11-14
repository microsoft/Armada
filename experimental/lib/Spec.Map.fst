module Spec.Map

let op_Hat_Subtraction_Greater = FStar.FunctionalExtensionality.op_Hat_Subtraction_Greater

let t (k: eqtype) (v: Type) = k ^-> v 
let upd #k #v (m: t k v) (key: k) (value: v) : t k v = 
  FStar.FunctionalExtensionality.on_domain k (fun key' -> if key = key' then value else m key')
let const (#k: eqtype) (#v: Type) (value: v) : t k v = FStar.FunctionalExtensionality.on k (fun (_: k) -> value)
let map_eq #k #v (m0 m1: t k v)
  : Lemma (requires forall key. m0 key == m1 key)
          (ensures m0 == m1)
  = FStar.FunctionalExtensionality.extensionality _ _ m0 m1
