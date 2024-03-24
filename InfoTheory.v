Require Import Coq.Lists.List.
Import ListNotations.

(* Defines an abstract state machine: a function from state and input to state and output. *)
Definition state_machine {state input output} : Type := state -> input -> state * output.

(* Get the full trace of a state machine, including internal state. *)
Definition trace
  {state input output} (m : state_machine) (start : state) (stream : list input)
  : list state * list output :=
  fold_left
    (fun (current : list state * list output) (next : input) =>
       let states := fst current in
       let outs := snd current in
       let state := hd start states in
       let stepped := m state next in
       let new_state := fst stepped in
       let new_out := snd stepped in
       (new_state :: states, new_out :: outs))
    stream ([], []).

(* Observe a state machine on a list of inputs; the final state and
   output stream are observable but the intermediate states are
   not. *)
Definition scan
  {state input output} (m : state_machine) (start : state) (stream : list input)
  : state * list output :=
  let t := trace m start stream in
  let states := fst t in
  let outputs := snd t in
  (hd start states, outputs).

(* A state machine is observationally independent of part of its input
   data (test) if the observable part of the trace is always the same
   when the NON-test input data (other) is the same. *)
Definition independent
  (* given an observation function (e.g. scan/trace of a state machine)... *)
  {state other T} (test : Type) (observe : state -> list (other * test) -> T) : Prop :=
  (* ...then, for all start states and all pairs of input streams... *)
  forall (start : state) (stream1 stream2 : list (other * test)),
    (* ...if the data not under test is the same... *)
    map fst stream1 = map fst stream2 ->
    (* ...then the observations are the same. *)
    observe start stream1 = observe start stream2.

(* Contrapositive for independent *)
Definition dependent
  {state other T} (test : Type) (observe : state -> list (other * test) -> T) : Prop :=
  exists (start : state) (stream1 stream2 : list (other * test)),
    map fst stream1 = map fst stream2
    /\ observe start stream1 <> observe start stream2.

Lemma dependent_not_independent
  {state other T} (test : Type) (observe : state -> list (other * test) -> T) :
  dependent test observe -> ~ independent test observe.
Proof.
  cbv [dependent independent].
  repeat match goal with
         | _ => progress intros
         | H : exists _, _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         | _ => solve [auto]
         end.
Qed.

Lemma independent_not_dependent
  {state other T} test (observe : state -> list (other * test) -> T) :
  independent test observe -> ~ dependent test observe.
Proof.
  cbv [dependent independent].
  repeat match goal with
         | _ => progress intro
         | H : exists _, _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         | _ => solve [auto]
         end.
Qed.

(* Represents one component state machine embedded inside a larger
   state machine. This is represented by some "pre" logic that
   transforms the input before the component gets it and can depend on
   the , and some "post" logic that transforms the output of the
   component before the observable output. All have their own internal
   state, and pre and post can both (at least theoretically) depend on
   the full input. This construction just expresses that we can't
   directly observe/control the input and output of the component
   directly. *)
(*
               _______       ________          _________
   input -----| pre  |------|  comp  |--------|  post  |--- output
          |   |______|      |________|  .-----|________|
          |____________________________|
 *)
Definition with_component
  {input output pre_state comp_state post_state comp_input comp_output}
  (pre : @state_machine pre_state input comp_input)
  (comp : @state_machine comp_state comp_input comp_output)
  (post : @state_machine post_state (comp_output * input) output)
  : @state_machine (pre_state * comp_state * post_state) input output :=
  fun (s : pre_state * comp_state * post_state) (i : input) =>
    let s1 := fst (fst s) in
    let s2 := snd (fst s) in
    let s3 := snd s in
    let pre_step := pre s1 i in
    let s1' := fst pre_step in
    let ci := snd pre_step in
    let comp_step := comp s2 ci in
    let s2' := fst comp_step in
    let co := snd comp_step in
    let post_step := post s3 (co, i) in
    let s3' := fst post_step in
    let o := snd post_step in
    ((s1', s2', s3'), o).

(* given an observation model (e.g. individual component state), the state at every point is enough to determine the current tested bits -- a change to even one bit changes the trace *)
(* Something something all bits are represented? unique? *)
Definition fully_dependent
  (* ...and an observation function (e.g. the state trace of a component)... *)
  {state other T} test (observe : state -> list (other * test) -> T) : Prop :=
  (* ...then, for all start states and all pairs of input streams... *)
  forall (start : state) (stream1 stream2 : list (other * test)),
    (* ...if the data under test is different... *)
    map fst stream1 <> map fst stream2 ->
    (* ...then the observations are different. *)
    observe start stream1 <> observe start stream2.

Definition component_state_trace
  {input output pre_state comp_state post_state comp_input comp_output}
  (pre : @state_machine pre_state input comp_input)
  (comp : @state_machine comp_state comp_input comp_output)
  (post : @state_machine post_state (comp_output * input) output)
  : (pre_state * comp_state * post_state) -> list input -> list comp_state :=
  fun start stream =>
    let t := trace (with_component pre comp post) start stream in
    (* pull out the component state from the global state *)
    map (fun s => snd (fst s)) (fst t).

Lemma scan_component_dependence
  (* given a component embedded in a state machine...*)
  {input se_bits output pre_state comp_state post_state comp_input comp_output}
  (pre : @state_machine pre_state (input * se_bits) comp_input)
  (comp : @state_machine comp_state comp_input comp_output)
  (post : @state_machine post_state (comp_output * (input * se_bits)) output) :
  let post_rearranged :
    @state_machine post_state (comp_output * input * se_bits) output :=
    fun s i =>
      (* rearrange tuple *)
      let i0 := fst (fst i) in
      let i1 := snd (fst i) in
      let i2 := snd i in
      post s (i0, (i1, i2)) in    
  (* ...and the state machine is observationally independent of the
        data in the scan observation model... *)
  independent se_bits (scan (with_component pre comp post)) ->
  (* ...and the pre and post logic are independent of the scan enable
        bits in the full-trace observation model (they are honest)... *)
  independent se_bits (trace pre) ->
  independent se_bits (trace post_rearranged) ->
  (* ..and the full circuit including the component is NOT honest... *)
  dependent se_bits (trace (with_component pre comp post)) ->
  (* ...then the component's individual state depends on all scan enable bits. *)
  fully_dependent se_bits (component_state_trace pre comp post).
Proof.
  cbv [independent dependent fully_dependent]; intros.
  intro.
  repeat match goal with
         | H : exists _, _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.

  
  (* chain pre-honest and component state to prove component input and state are honest? *)
  
  

Qed.  
