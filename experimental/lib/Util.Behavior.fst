module Util.Behavior

open FStar.Classical.Sugar
open Spec.Behavior
open Spec.Ubool

let refinement_relation_reflexive (#state_t: Type) (rr: refinement_relation_t state_t state_t) : ubool =
  forall (s: state_t). rr s s

let rec refinement_relation_reflexive_implies_behavior_refines_itself
  (#state_t: Type)
  (b: behavior_t state_t)
  (rr: refinement_relation_t state_t state_t)
  : Lemma (requires refinement_relation_reflexive rr)
          (ensures  behavior_refines_behavior b b rr) =
  match b with
  | [] -> ()
  | lstate :: ltail -> refinement_relation_reflexive_implies_behavior_refines_itself ltail rr

let refinement_relation_stronger
  (#low_state: Type)
  (#high_state: Type)
  (stronger_rr: refinement_relation_t low_state high_state)
  (weaker_rr: refinement_relation_t low_state high_state) =
  (forall (ls: low_state) (hs: high_state).{:pattern stronger_rr ls hs} stronger_rr ls hs ==> weaker_rr ls hs)

let rec behavior_refinement_maintained_by_weaker_refinement_relation
  (#low_state: Type)
  (#high_state: Type)
  (lb: behavior_t low_state)
  (hb: behavior_t high_state)
  (stronger_rr: refinement_relation_t low_state high_state)
  (weaker_rr: refinement_relation_t low_state high_state)
  : Lemma
  (requires (behavior_refines_behavior lb hb stronger_rr) /\ refinement_relation_stronger stronger_rr weaker_rr)
  (ensures  (behavior_refines_behavior lb hb weaker_rr)) =
  match lb with
  | [] -> assert (Nil? hb)
  | lstate :: ltail ->
    match hb with
    | [] -> assert False
    | hstate :: htail ->
       eliminate behavior_refines_behavior ltail htail stronger_rr \/
                 (behavior_refines_behavior ltail hb stronger_rr \/ behavior_refines_behavior lb htail stronger_rr)
       returns behavior_refines_behavior lb hb weaker_rr
       with case_ltail_refines_htail.
         behavior_refinement_maintained_by_weaker_refinement_relation ltail htail stronger_rr weaker_rr
       and  case_ltail_refines_hb_or_lb_refines_htail.
         eliminate behavior_refines_behavior ltail hb stronger_rr \/ behavior_refines_behavior lb htail stronger_rr
         returns _
         with case_ltail_refines_hb.
           behavior_refinement_maintained_by_weaker_refinement_relation ltail hb stronger_rr weaker_rr
         and  case_lb_refines_htail.
           behavior_refinement_maintained_by_weaker_refinement_relation lb htail stronger_rr weaker_rr

let spec_refinement_maintained_by_weaker_refinement_relation
  (#low_state: Type)
  (#high_state: Type)
  (lspec: spec_t low_state)
  (hspec: spec_t high_state)
  (stronger_rr: refinement_relation_t low_state high_state)
  (weaker_rr: refinement_relation_t low_state high_state)
  : Lemma
  (requires spec_refines_spec lspec hspec stronger_rr /\ refinement_relation_stronger stronger_rr weaker_rr)
  (ensures  spec_refines_spec lspec hspec weaker_rr) =
  introduce forall lb. behavior_satisfies_spec lb lspec ==>
                  (exists (hb: behavior_t high_state). behavior_satisfies_spec hb hspec /\
                                                  behavior_refines_behavior lb hb weaker_rr)
  with
    introduce behavior_satisfies_spec lb lspec ==>
              (exists (hb: behavior_t high_state). behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb weaker_rr)
    with lb_satisfies_spec.
      eliminate exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb stronger_rr
      returns _
      with exists_hb_satisfying_spec_and_refined_by_lb.
       (behavior_refinement_maintained_by_weaker_refinement_relation lb hb stronger_rr weaker_rr;
        introduce exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb weaker_rr
        with hb
        and ())

let rec behavior_refines_behavior_without_stuttering
  (#low_state: Type)
  (#high_state: Type)
  (lb: behavior_t low_state)
  (hb: behavior_t high_state)
  (rr: refinement_relation_t low_state high_state)
  : ubool =
  match lb with
  | [] -> Nil? hb
  | lstate :: ltail ->
    match hb with
    | [] -> False
    | hstate :: htail ->
      rr lstate hstate /\
      behavior_refines_behavior_without_stuttering ltail htail rr

let rec behavior_refines_behavior_without_stuttering_implies_behavior_refines_behavior
  (#low_state: Type)
  (#high_state: Type)
  (lb: behavior_t low_state)
  (hb: behavior_t high_state)
  (rr: refinement_relation_t low_state high_state)
  : Lemma (requires behavior_refines_behavior_without_stuttering lb hb rr)
          (ensures  behavior_refines_behavior lb hb rr) =
  match lb with
  | [] -> ()
  | lstate :: ltail ->
     match hb with
     | [] -> ()
     | hstate :: htail ->
        behavior_refines_behavior_without_stuttering_implies_behavior_refines_behavior ltail htail rr

let rec refinement_relation_reflexive_implies_behavior_refines_itself_without_stuttering
  (#state_t: Type)
  (b: behavior_t state_t)
  (rr: refinement_relation_t state_t state_t)
  : Lemma (requires refinement_relation_reflexive rr)
          (ensures  behavior_refines_behavior_without_stuttering b b rr /\ behavior_refines_behavior b b rr) =
  match b with
  | [] -> ()
  | lstate :: ltail -> refinement_relation_reflexive_implies_behavior_refines_itself_without_stuttering ltail rr

let rec behavior_refinement_transitivity
  (#lstate_t: Type)
  (#mstate_t: Type)
  (#hstate_t: Type)
  (lb: behavior_t lstate_t)
  (mb: behavior_t mstate_t)
  (hb: behavior_t hstate_t)
  (rr_lm: refinement_relation_t lstate_t mstate_t)
  (rr_mh: refinement_relation_t mstate_t hstate_t)
  (rr_lh: refinement_relation_t lstate_t hstate_t)
  : Lemma (requires   behavior_refines_behavior lb mb rr_lm
                    /\ behavior_refines_behavior mb hb rr_mh
                    /\ (forall l m h.{:pattern rr_lm l m; rr_mh m h} rr_lm l m /\ rr_mh m h ==> rr_lh l h))
          (ensures  behavior_refines_behavior lb hb rr_lh) =
  match lb with
  | [] -> ()
  | lstate :: ltail ->
     match mb with
     | [] -> ()
     | mstate :: mtail ->
        match hb with
        | [] -> ()
        | hstate :: htail ->
           eliminate behavior_refines_behavior ltail mtail rr_lm \/
                     (behavior_refines_behavior ltail mb rr_lm \/ behavior_refines_behavior lb mtail rr_lm)
           returns behavior_refines_behavior lb hb rr_lh
           with case_ltail_refines_mtail.
             eliminate behavior_refines_behavior mtail htail rr_mh \/ 
                        (behavior_refines_behavior mtail hb rr_mh \/ behavior_refines_behavior mb htail rr_mh)
             returns _
             with case_mtail_refines_htail.
               behavior_refinement_transitivity ltail mtail htail rr_lm rr_mh rr_lh
             and  case_mtail_refines_hb_or_mb_refines_htail.
               (eliminate behavior_refines_behavior mtail hb rr_mh \/ behavior_refines_behavior mb htail rr_mh
                returns _
                with case_mtail_refines_hb. behavior_refinement_transitivity ltail mtail hb rr_lm rr_mh rr_lh
                and  case_mb_refines_htail. behavior_refinement_transitivity lb mb htail rr_lm rr_mh rr_lh)
           and  case_ltail_refines_mb_or_lb_refines_mtail.
             eliminate behavior_refines_behavior ltail mb rr_lm \/ behavior_refines_behavior lb mtail rr_lm
             returns _
             with case_ltail_refines_mb.
               behavior_refinement_transitivity ltail mb hb rr_lm rr_mh rr_lh
             and  case_lb_refines_mtail.
               (eliminate behavior_refines_behavior mtail htail rr_mh \/
                (behavior_refines_behavior mtail hb rr_mh \/ behavior_refines_behavior mb htail rr_mh)
                returns _
                with case_mtail_refines_htail.
                  behavior_refinement_transitivity lb mtail htail rr_lm rr_mh rr_lh
                and  case_mtail_refines_hb_or_mb_refines_htail.
                  eliminate behavior_refines_behavior mtail hb rr_mh \/ behavior_refines_behavior mb htail rr_mh
                  returns _
                  with case_mail_refines_hb.
                    behavior_refinement_transitivity lb mtail hb rr_lm rr_mh rr_lh
                  and  case_mb_refines_htail.
                    behavior_refinement_transitivity lb mb htail rr_lm rr_mh rr_lh)

let spec_refinement_transitivity
  (#lstate_t: Type)
  (#mstate_t: Type)
  (#hstate_t: Type)
  (lspec: spec_t lstate_t)
  (mspec: spec_t mstate_t)
  (hspec: spec_t hstate_t)
  (rr_lm: refinement_relation_t lstate_t mstate_t)
  (rr_mh: refinement_relation_t mstate_t hstate_t)
  (rr_lh: refinement_relation_t lstate_t hstate_t)
  : Lemma (requires   spec_refines_spec lspec mspec rr_lm
                    /\ spec_refines_spec mspec hspec rr_mh
                    /\ (forall l m h.{:pattern rr_lm l m; rr_mh m h} rr_lm l m /\ rr_mh m h ==> rr_lh l h))
          (ensures  spec_refines_spec lspec hspec rr_lh) =
  introduce forall lb. behavior_satisfies_spec lb lspec ==>
                  (exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb rr_lh)
  with
    introduce behavior_satisfies_spec lb lspec ==>
                  (exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb rr_lh)
    with given_that_lb_satisfies_spec.
      eliminate exists mb. behavior_satisfies_spec mb mspec /\ behavior_refines_behavior lb mb rr_lm
      returns _
      with knowing_mb_satisfies_spec_and_is_refined_by_lb.
        eliminate exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior mb hb rr_mh
        returns _
        with knowing_hb_satisfies_spec_and_is_refined_by_mb.
          behavior_refinement_transitivity lb mb hb rr_lm rr_mh rr_lh

let spec_refinement_transitivity_4
  (#state1_t: Type)
  (#state2_t: Type)
  (#state3_t: Type)
  (#state4_t: Type)
  (spec1: spec_t state1_t)
  (spec2: spec_t state2_t)
  (spec3: spec_t state3_t)
  (spec4: spec_t state4_t)
  (rr12: refinement_relation_t state1_t state2_t)
  (rr23: refinement_relation_t state2_t state3_t)
  (rr34: refinement_relation_t state3_t state4_t)
  (rr13: refinement_relation_t state1_t state3_t)
  (rr14: refinement_relation_t state1_t state4_t)
  : Lemma (requires   spec_refines_spec spec1 spec2 rr12
                    /\ spec_refines_spec spec2 spec3 rr23
                    /\ spec_refines_spec spec3 spec4 rr34
                    /\ (forall s1 s2 s3.{:pattern rr12 s1 s2; rr23 s2 s3} rr12 s1 s2 /\ rr23 s2 s3 ==> rr13 s1 s3)
                    /\ (forall s1 s3 s4.{:pattern rr13 s1 s3; rr34 s3 s4} rr13 s1 s3 /\ rr34 s3 s4 ==> rr14 s1 s4))
          (ensures  spec_refines_spec spec1 spec4 rr14) =
  spec_refinement_transitivity spec1 spec2 spec3 rr12 rr23 rr13;
  spec_refinement_transitivity spec1 spec3 spec4 rr13 rr34 rr14

let spec_refinement_transitivity_5
  (#state1_t: Type)
  (#state2_t: Type)
  (#state3_t: Type)
  (#state4_t: Type)
  (#state5_t: Type)
  (spec1: spec_t state1_t)
  (spec2: spec_t state2_t)
  (spec3: spec_t state3_t)
  (spec4: spec_t state4_t)
  (spec5: spec_t state5_t)
  (rr12: refinement_relation_t state1_t state2_t)
  (rr23: refinement_relation_t state2_t state3_t)
  (rr34: refinement_relation_t state3_t state4_t)
  (rr45: refinement_relation_t state4_t state5_t)
  (rr13: refinement_relation_t state1_t state3_t)
  (rr14: refinement_relation_t state1_t state4_t)
  (rr15: refinement_relation_t state1_t state5_t)
  : Lemma (requires   spec_refines_spec spec1 spec2 rr12
                    /\ spec_refines_spec spec2 spec3 rr23
                    /\ spec_refines_spec spec3 spec4 rr34
                    /\ spec_refines_spec spec4 spec5 rr45
                    /\ (forall s1 s2 s3.{:pattern rr12 s1 s2; rr23 s2 s3} rr12 s1 s2 /\ rr23 s2 s3 ==> rr13 s1 s3)
                    /\ (forall s1 s3 s4.{:pattern rr13 s1 s3; rr34 s3 s4} rr13 s1 s3 /\ rr34 s3 s4 ==> rr14 s1 s4)
                    /\ (forall s1 s4 s5.{:pattern rr14 s1 s4; rr45 s4 s5} rr14 s1 s4 /\ rr45 s4 s5 ==> rr15 s1 s5))
          (ensures  spec_refines_spec spec1 spec5 rr15) =
  spec_refinement_transitivity spec1 spec2 spec3 rr12 rr23 rr13;
  spec_refinement_transitivity spec1 spec3 spec4 rr13 rr34 rr14;
  spec_refinement_transitivity spec1 spec4 spec5 rr14 rr45 rr15
