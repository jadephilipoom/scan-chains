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

(* Two types are isomorphic if we can convert back and forth between
   them without losing information. *)
Definition isomorphism {T U : Type} (ofT : T -> U) (toT : U -> T) : Prop :=
  (forall (t : T), toT (ofT t) = t)
  /\ (forall (u : U), ofT (toT u) = u).

(* A state machine is observationally independent of part of its input
   data if the observable part of the trace is the same regardless of
   changes to that data. *)
Definition observationally_independent
  (* given a state machine... *)
  {state input output} (m : @state_machine state input output)
  (* ...and a way we're observing the state machine (e.g. scan, trace)... *)
  {T} (observe : state_machine -> state -> list input -> T)
  (* ...and a way to express the input data as a tuple of data we're
        testing for and some other data... *)
  {data other}
  (extract : input -> data * other) (assemble : data * other -> input) : Prop :=
  (* ...if that the tuple conversion does not lose information... *)
  isomorphism extract assemble ->
  (* ...then, for all start states and all pairs of input streams... *)
  forall (start : state) (stream1 stream2 : list input),
    (* ...if the data under test is the same (no assumptions about other data)... *)
    map (fun i => fst (extract i)) stream1 = map (fun i => fst (extract i)) stream2 ->
    (* ...then the observations are the same. *)
    observe m start stream1 = observe m start stream2.

(* compose two state machines. *)
Definition compose
  {state1 state2 input middle output}
  (m1 : @state_machine state1 input middle)
  (m2 : @state_machine state2 middle output)
  : @state_machine (state1 * state2) input output :=
  fun (s : state1 * state2) (i : input) =>
    let step1 := m1 (fst s) i in
    let s1 := fst step1 in
    let o1 := snd step1 in
    let step2 := m2 (snd s) o1 in
    let s2 := fst step2 in
    let o2 := snd step2 in
    ((s1, s2), o2).
Local Infix ">=>" := compose (at level 40, only parsing).

(* apply a state machine to the first part of a tuple, ignoring the second. *)
Definition on_first
  {state input output ignored}
  (m : @state_machine state input output)
  : @state_machine state (input * ignored) (output * ignored) :=
  fun (s : state) (i : input * ignored) =>
    let step := m s (fst i) in
    let s' := fst step in
    let o := snd step in
    (s', (o, snd i)).

(* split a signal into two paths *)
Definition fork {t} : @state_machine unit t (t * t) :=
  fun _ (i : t) => (tt, (i, i)).

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

(* Something something all bits are represented? unique? *)
Definition fully_dependent
  (* given a state machine... *)
  {state input output} (m : @state_machine state input output)
  (* ...and a way we're observing the state machine (e.g. scan, trace)... *)
  {T} (observe : state_machine -> state -> list input -> T)
  (* ...and a way to express the input data as a tuple of data we're
        testing for and some other data... *)
  {data other}
  (extract : input -> data * other) (assemble : data * other -> input) : Prop :=
  (* ...if that the tuple conversion does not lose information... *)
  isomorphism extract assemble ->
  (* ...then, for all start states and all pairs of input streams... *)
  forall (start : state) (stream1 stream2 : list input),
    (* ...if the data under test is the same (no assumptions about other data)... *)
    map (fun i => fst (extract i)) stream1 = map (fun i => fst (extract i)) stream2 ->
    (* ...then the observations are the same. *)
    observe m start stream1 = observe m start stream2.

Lemma scan_dependence
  (* given a component embedded in a state machine...*)
  {input output pre_state comp_state post_state comp_input comp_output post_input}
  (pre : @state_machine pre_state input comp_input)
  (comp : @state_machine comp_state comp_input comp_output)
  (post : @state_machine post_state (comp_output * input) output)
  (* ...and a portion of the input data under test... *)
  {se_bits other}
  (extract : input -> se_bits * other) (assemble : se_bits * other -> input) :
  (* ...if the extract/assemble routines are formed properly... *)
  isomorphism extract assemble ->
  (* ...and the state machine is observationally independent of the
        data in the scan observation model... *)
  observationally_independent (with_component pre comp post) scan extract assemble ->
  (* ...and the pre and post logic are independent of the scan enable
        bits in the full-trace observation model (they are honest)... *)
  observationally_independent pre trace extract assemble ->
  observationally_independent
    post trace
    (fun (i : comp_output * input) =>
       let extracted := extract (snd i) in
       let se := fst extracted in
       let other := snd extracted in
       (se, (fst i, other)))
    (fun x =>
       assemble ->
  (* ..then either the full circuit including the component is honest... *)
  (observationally_independent (with_component pre comp post) trace extract assemble)
  (* ...or the component's individual state depends on all scan enable bits. *)
  \/ (True).

  
(* Need to somehow in here have the notion of the internal component of the circuit... *)
Lemma scan_dependence
  (* given a state machine...*)
  {state input output} (m : @state_machine state input output)
  (* ...and a portion of the input data under test... *)
  {se_bits other}
  (extract : input -> se_bits * other) (assemble : se_bits * other -> input) :
  (* ...if the extract/assemble routines are formed properly... *)
  isomorphism extract assemble ->
  (* ...and the state machine is observationally independent of the
        data in the scan observation model... *)
  observationally_indepenent m scan extract assemble ->
  (* ..then either the state machine is also independent of the data
     in the full-trace observation model... *)
  (observationally_independent m trace extract assemble)
  (* ...or all scan enable bits can be inferred from the state and input. *)
  \/ ().
  
  (* defines an abstract state machine *)
  {state input output : Type}
  (step : state -> input -> state * output)
  (* we can extract a certain number of scan enable bits from the
     input *)
  (n : nat) (extract_scan_enable : input -> list bool)
  (length_extract_scan_enable : forall input, length (extract_scan_enable input) = n)
  :
  
