Require Import Coq.Lists.List.
Import ListNotations.

(* register state : known registers in their scan chain formation and
   potential extra, malicious state. *)
Definition registers : Type := list (list bool) * list bool.

(* Defines the untrusted but purely combinational logic of a circuit
   (essentially a Moore machine). *)
Definition logic {input output} : Type :=
  forall
    (* register values *)
    (regs : registers)
    (* scan enable bits *)
    (se : list bool)
    (* input value for this cycle *)
    (i : input),
    registers * output.

Section WithAbstractDefs.
  (* Define a global, abstract throttling function that we'll never
     instantiate. This is so we are forced to not assume anything about
     registers that aren't part of the scan chain. *)
  Context (throttle : registers -> registers).

  (* returns true iff there is at least one true in the list *)
  Definition any (l : list bool) : bool := fold_left andb l false.

  (* step the circuit, including logic that might shift a scan chain;
     model the shift as a reset of the whole chain for now *)
  Definition scan_step
    {input output m_state} (c : @circuit input output m_state)
    (regs : list (list bool)) (ms : list bool) (se : list bool)
    (chain_i : list (list bool)) (i : input) : list bool * output :=
    (* if any scan enable is set, throttle all register values *)
    let regs := if any se then throttle regs else regs in
    (* for each chain, if the scan enable is set, reset the value to
       the corresponding entry in chain_i *)
    map (fun x =>
           let en := fst (fst x) in
           let chain_i
           if fst x then snd x else snd x) (combine (combine se chain_i) regs).
  
  
  
  

(* Boilerplate that lets us say the circuit logic can't change the number of registers. *)
Definition regs_wf (regs : list (list bool)) (chains : list nat) : Prop :=
  map (@length bool) regs = chains.
Definition circuit_wf
  {input output m_state} (c : @circuit input output m_state)
  (chains : list nat) : Prop :=
  forall regs ms i,
    regs_wf regs chains ->
    let x := c regs ms i in
    let regs' := fst (fst x) in
    regs_wf regs' chains.

(* we want to talk about the state of the circuit as including some unknown component, and visualize like a moore machine:

r1 r2 r3   ... M
    |
    |
   \/
<comb logic, totally untrusted>
   |
   |
  \/
r1 r2 r3 ... M

All registers depend on all others.

 *)

Definition trace_step
  {state input output} (m : state_machine)
  (* observation function *)
  {T} (observe : state -> output -> T)
  (* manipulation function *)
  (manipulate : state -> state)
  (current : state * list T) (next : input) : state * list T :=
  let state := fst current in
  let t := snd current in
  let step := m state next in
  let new_state := fst step in
  let new_out := snd step in
  (manipulate new_state, observe new_state new_out :: t).

(* Get the trace of a state machine under a particular observation function. *)
Definition trace
  {state input output} (m : state_machine)
  {T} (observe : state -> output -> T)
  (start : state) (stream : list input)
  : state * list T :=
  fold_left (trace_step m observe) stream (start, []).


(* Observation function for a scan chain operation that captures all
   registers at the same time and only at the end. We don't see the
   intermediate states (although we can see the final state). This
   corresponds to running the circuit for a while and then doing a
   one-time snapshot of the state. *)
Definition simple_scan {state output} : state -> output -> output := fun _ o => o.

(* A scan that captures all possible information. *)
Definition full_scan {state output} : state -> output -> state * output := fun s o => (s, o).


