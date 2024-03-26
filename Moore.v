Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* register state : known registers in their scan chain formation and
   potential extra, malicious state. *)
Definition registers : Type := list (list bool) * list bool.

(* Defines the untrusted but purely combinational logic of a circuit
   (essentially a Moore machine). *)
Definition logic : Type :=
  forall
    (* register values *)
    (regs : registers)
    (* scan enable bits *)
    (se : list bool)
    (* input value for this cycle *)
    (i : list bool),
    registers * list bool.

(* returns true iff there is at least one true in the list *)
Definition any (l : list bool) : bool := fold_left andb l false.

Section WithAbstractDefs.
  (* Define a global, abstract throttling function that we'll never
     instantiate. This is so we are forced to not assume anything about
     registers that aren't part of the scan chain. *)
  Context (throttle : registers -> registers).

  (* Scan chain inputs; for each chain, should be:
     - None if the chain will not be set to a new value
     - Some v if the chain value should be set to value v
   *)
  Definition chain_input : Type := list (option (list bool)).

  (* infer scan enable bits based on optional new states for chains
     (None if scan not enabled for that chain) *)
  Definition get_se (chain_i : chain_input) : list bool :=
    map (fun x => match x with
                  | Some _ => true
                  | None => false
                  end) chain_i.

  (* step the circuit, including logic that might shift a scan chain;
     model the shift as a reset of the whole chain for now *)
  Definition scan_step (m : logic)
    (* start register values *)
    (regs : registers)
    (* new states for chains *)
    (chain_i : chain_input)
    (* logical input *)
    (i : list bool)
    : registers * list bool :=
    (* infer scan-enable signals *)
    let se := get_se chain_i in
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
    m regs se i.

  (* Boilerplate that lets us say the circuit logic can't change the number of registers. *)
  Definition regs_wf (regs : registers) (chains : list nat) (mlen : nat) : Prop :=
    map (@length bool) (fst regs) = chains
    /\ length (snd regs) = mlen.
  Definition chain_input_wf (chain_i : chain_input) (chains : list nat) : Prop :=
    length chain_i = length chains
    /\ Forall2 (fun i c => match i with
                           | Some l => length l = c
                           | None => True
                           end) chain_i chains.
  Definition logic_wf (m : logic)
    (chains : list nat) (mlen : nat) : Prop :=
    forall regs se i,
      regs_wf regs chains mlen ->
      let x := m regs se i in
      let regs' := fst x in
      regs_wf regs' chains mlen.
  
  (* Boilerplate: a tactic to logically simplify the goal with some list helpers *)
  Ltac simplify_step  :=
    lazymatch goal with
    | H : _ /\ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : _ :: _ = _ :: _ |- _ => inversion H; clear H
    | H : (_, _) = (_, _) |- _ => inversion H; clear H
    | H : ?x = ?x |- _ => clear H
    | H : ?x = [] |- _ => destruct x; [ | congruence ]
    | H : Forall2 _ (_ :: _) (_ :: _) |- _ =>
        apply Forall2_cons_iff in H; destruct H
    | H : Forall2 _ [] [] |- _ => clear H
    | _ => progress cbn [fst snd length] in *                                              
    end.
  Ltac simplify := repeat simplify_step.

  (* States two circuits are always observably the same when scanned. *)
  Definition indistinguishable
    (trojan facade : logic) (chains : list nat) mlen : Prop :=
    (* for all registers and actual logical input... *)
    forall known unknown chain_i i_real,
      let regs := (known, unknown) in
      (* ...if the logical input and register values are valid... *)
      chain_input_wf chain_i chains ->
      regs_wf regs chains mlen ->
      let t := scan_step trojan regs chain_i i_real in
      let tregs := fst t in
      let tout := snd t in
      (* ...there exists some (potentially different) logical
         input... *)
      exists i_fake,
        let f := scan_step facade (known, []) chain_i i_fake in
        let fregs := fst f in
        let fout := snd f in
        (* ...such that both known registers and output are the same *)
        fst tregs = fst fregs /\ tout = fout.

  (* sort of dissatisfying, there should be a better way of expressing
     this than the list bools *)

  (* something is off, it's too awkward to state and reason
  about. think some more. I think this model is accurate to what the
  scan chain does but not nice to reason about. *)

  Lemma hd_repeat {A} (d : A) n : hd d (repeat d n) = d.
  Proof. destruct n; reflexivity. Qed.

  Definition num_known_regs (chains : list nat) : nat :=
    fold_left Nat.add chains 0.

  (* States that the circuit has at least one known register (i.e. it
     is not a combinational circuit). *)
  Definition is_sequential (chains : list nat) : Prop :=
    0 < num_known_regs chains.

  Lemma concat_snoc {A} (l : list (list A)) :
    forall a, concat (l ++ [a]) = concat l ++ a.
  Proof.
    induction l; intros; cbn [concat app]; [ rewrite app_nil_r; reflexivity | ].
    rewrite IHl. apply app_assoc.
  Qed.

  Lemma length_known_regs (regs : registers) (chains : list nat) mlen :
    regs_wf regs chains mlen ->
    length (concat (fst regs)) = num_known_regs chains.
  Proof.
    cbv [regs_wf num_known_regs]; intros.
    destruct regs as [known unknown]; simplify. subst.
    induction known using rev_ind;
      subst; cbn [map fold_left concat] in *; intros; [ reflexivity | ].
    rewrite concat_snoc.
    rewrite map_app, fold_left_app, app_length.
    cbn [map fold_left]. lia.
  Qed.

  (* A theoretical trojan that imitates the facade if scan is high and
     returns the result facade would have given for a manipulated
     input otherwise. *)
  Definition manip_trojan (facade : logic) (manip : list bool -> list bool) : logic :=
    fun regs se i =>
      let en := hd false se in
      let f := facade regs se i in
      let regs' := fst f in
      let o := snd f in
      if en
      then facade regs se i
      else facade regs se (manip i).

  (* Manipulation trojan is not caught by a single scan chain *)
  Lemma manip_trojan_step_single_chain facade manip nregs :
    logic_wf facade [nregs] 0 ->
    (* manipulation doesn't change the number of bits *)
    (forall i, length (manip i) = length i) ->
    indistinguishable (manip_trojan facade manip) facade [nregs] 0.
  Proof.
    cbv [indistinguishable]; intros.
    cbv [chain_input_wf] in *. simplify.
    lazymatch goal with
    | Hf : logic_wf _ _ _, Hr : regs_wf _ _ _ |- _ =>
        pose proof (Hf _ (get_se chain_i) i_real Hr);
        specialize (Hf _ (get_se chain_i) (map negb i_real) Hr)
    end.
    simplify.
    (* prove chain_i has exactly one element *)
    destruct chain_i as [|ci0 [|? ?]]; cbn [length] in *; try lia; [ ].
    simplify.
    cbv [regs_wf] in *.
    simplify.
    destruct unknown; cbn [length] in *; [ | lia ].
    destruct known as [| ? [|? ?]]; cbn [length map] in *; [ congruence | | congruence].
    simplify.
    lazymatch goal with
    | H : length ?x = 0 |- _ => destruct x; cbn [length] in H; [ | congruence ]
    end.
    simplify.      
    (* now determine if we're scanning or not *)
    destruct ci0; cbn [get_se] in *; [ exists i_real; split; reflexivity | ].    
    exists (manip i_real); split; reflexivity.    
  Qed.

End WithAbstractDefs.
