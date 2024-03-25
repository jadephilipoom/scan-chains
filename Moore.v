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

(* returns true iff there is at least one true in the list *)
Definition any (l : list bool) : bool := fold_left andb l false.

Section WithAbstractDefs.
  (* Define a global, abstract throttling function that we'll never
     instantiate. This is so we are forced to not assume anything about
     registers that aren't part of the scan chain. *)
  Context (throttle : registers -> registers).

  Definition test_input {input} : Type :=
    (* new states for chains (or None if the chain should not be reset *)
    list (option (list bool))
    (* input value *)
    * input.

  (* step the circuit, including logic that might shift a scan chain;
     model the shift as a reset of the whole chain for now *)
  Definition scan_step
    {input output} (m : @logic input output)    
    (* start register values *)
    (regs : registers)
    (i : test_input)
    : registers * output :=
    let chain_i := fst i in
    (* infer scan-enable signals *)
    let se := map (fun x => match x with
                            | Some l => true
                            | None => false
                            end) chain_i in
    (* if any scan enable is set, throttle all register values *)
    let regs := if any se then throttle regs else regs in
    let known_regs := fst regs in
    let unknown_regs := snd regs in
    (* for each chain, if the scan enable is set, reset the value to
       the corresponding entry in chain_i *)
    let regs := (map (fun x => match fst x with
                               | Some l => l
                               | None => snd x
                               end) (combine chain_i known_regs), unknown_regs) in
    (* now execute the combinational logic *)
    m regs se (snd i).

  (* Boilerplate that lets us say the circuit logic can't change the number of registers. *)
  Definition regs_wf (regs : registers) (chains : list nat) (mlen : nat) : Prop :=
    map (@length bool) (fst regs) = chains
    /\ length (snd regs) = mlen.
  Fixpoint test_wf {input} (i : @test_input input) (chains : list nat) : Prop :=
    let chain_i := fst i in
    length chain_i = length chains
    /\ Forall2 (fun i c => match i with
                           | Some l => length l = c
                           | None => True
                           end) chain_i chains.
  Definition logic_wf
    {input output} (m : @logic input output)
    (chains : list nat) (mlen : nat) : Prop :=
    forall regs ms i,
      regs_wf regs chains mlen ->
      let x := m regs ms i in
      let regs' := fst x in
      regs_wf regs' chains mlen.

  (* States two circuits are always observably the same when scanned. *)
  Definition indistinguishable
    {input output} (trojan facade : @logic input output) (chains : list nat) mlen : Prop :=
    forall regs i,
      test_wf i chains ->
      regs_wf regs chains mlen ->
      let t := scan_step trojan regs i in
      let tregs := fst t in
      let tout := snd t in
      let f := scan_step trojan (fst regs, []) i in
      let fregs := fst f in
      let fout := snd f in
      (* known registers and output are the same *)
      fst tregs = fst fregs /\ tout = fout.

  (* sort of dissatisfying, there should be a better way of expressing
     this than the list bools *)
  
  (* A single scan chain is not enough to detect even a purely
     combinational trojan; for every good circuit, there exists a
     combinational trojan that will be indistinguishable from it. *)
  Lemma single_chain_insufficient
    {input output} (facade : @logic input output) (nregs : nat) :
    logic_wf facade [nregs] 0 ->
    exists trojan,
      indistinguishable trojan facade [nregs] 0.
  Proof.
    cbv [indistinguishable]; intros.
    exists (fun regs se i =>
              let en := hd se 0 in
              if en
              then facade i
              else 
    (* register values *)
    (regs : registers)
    (* scan enable bits *)
    (se : list bool)
    (* input value for this cycle *)
    (i : input),
    registers * output.


  Qed.
  

  Inductive indistinguishable {input output}
    : @logic input output -> @logic input output -> 

  (* step the circuit and observe only the known registers *)
  Definition scan_step_and_observe
    {input output} (m : @logic input output)
    (current : list (list (list bool) * output) * registers)
    (next : list (option (list bool)) * input)
    : list (list (list bool) * output) * registers :=
    let trace := fst current in
    let regs := snd current in
    let chain_i := fst next in
    let i := snd next in
    (scan_step m regs chain_i i :: trace, .
    


  Definition scan
    {input output} (m : @logic input output)
    (* start register values *)
    (regs : registers)
    (* new states for chains and input values *)
    (test : list (list (option (list bool)) * input))
    : list (list (list bool)) * registers * list output :=
    fold_left
      (fun current next =>
         let chain_i := 
         scan_step regs)
      test
    (* infer scan-enable signals *)
    let se := map (fun x => match x with
                            | Some l => true
                            | None => false
                            end) chain_i in
    (* if any scan enable is set, throttle all register values *)
    let regs := if any se then throttle regs else regs in
    let known_regs := fst regs in
    let unknown_regs := snd regs in
    (* for each chain, if the scan enable is set, reset the value to
       the corresponding entry in chain_i *)
    let regs := (map (fun x => match fst x with
                               | Some l => l
                               | None => snd x
                               end) (combine chain_i known_regs), unknown_regs) in
    (* now execute the combinational logic *)
    let result := m regs se i in
    let regs' := fst result in
    let out := snd result in
    (fst regs', out).

  (* Boilerplate that lets us say the circuit logic can't change the number of registers. *)
  Definition regs_wf (regs : registers) (chains : list nat) (mlen : nat) : Prop :=
    map (@length bool) (fst regs) = chains
    /\ length (snd regs) = mlen.
  Definition logic_wf
    {input output} (m : @logic input output)
    (chains : list nat) (mlen : nat) : Prop :=
    forall regs ms i,
      regs_wf regs chains mlen ->
      let x := m regs ms i in
      let regs' := fst x in
      regs_wf regs' chains mlen.

  Definition indistinguishable {input output} (m1 m2 : @logic input output) : Prop :=
    forall regs1 regs2 chain_i i,
      fst regs1 = fst regs2 ->
      scan_step m1 regs1 chain_i i = scan_step m2 regs2 chain_i i.
  
  (* A single scan chain is not enough to detect a purely combinational trojan. *)
  (* it is possible for a trojan to be indistinguishable from  *)
  Lemma single_chain_insufficient
    {input output} (m : @logic input output) (nregs : nat) :
    (* one chain containing all registers *)
    let chains := [nregs] in
    logic_wf m chains 0 ->
    undetectable chains m.
    
    
  

End WithAbstractDefs.
  
  
  
  

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


