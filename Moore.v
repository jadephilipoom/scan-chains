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

  Definition test_input : Type :=
    (* new states for chains (or None if the chain should not be reset *)
    list (option (list bool))
    (* input value *)
    * list bool.

  (* step the circuit, including logic that might shift a scan chain;
     model the shift as a reset of the whole chain for now *)
  Definition scan_step (m : logic)
    (* start register values *)
    (regs : registers)
    (i : test_input)
    : registers * list bool :=
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
  Fixpoint test_wf (i : test_input) (chains : list nat) : Prop :=
    let chain_i := fst i in
    length chain_i = length chains
    /\ Forall2 (fun i c => match i with
                           | Some l => length l = c
                           | None => True
                           end) chain_i chains.
  Definition logic_wf (m : logic)
    (chains : list nat) (mlen : nat) : Prop :=
    forall regs ms i,
      regs_wf regs chains mlen ->
      let x := m regs ms i in
      let regs' := fst x in
      regs_wf regs' chains mlen.

  (* States two circuits are always observably the same when scanned. *)
  Definition indistinguishable
    (trojan facade : logic) (chains : list nat) mlen : Prop :=
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

  (* something is off, it's too awkward to state and reason
  about. think some more. I think this model is accurate to what the
  scan chain does but not nice to reason about. *)

  (* invert known registers *)
  Definition invert (regs : registers) :=
    (map (fun x => map negb x) (fst regs) , snd regs).

  Lemma regs_wf_after_invert (regs : registers) (chains : list nat) (mlen : nat) :
    regs_wf regs chains mlen ->
    regs_wf (invert regs) chains mlen.
  Proof.
    cbv [regs_wf invert]; intros.
    repeat match goal with
           | _ => progress cbn [fst snd]
           | H : _ /\ _ |- _ => destruct H
           end.
    split; [ | assumption ].
    rewrite map_map.
    erewrite map_ext; [ apply H | ].
    intros. rewrite map_length; reflexivity.
  Qed.

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
    destruct regs as [known unknown]; cbn [fst snd] in *.
    lazymatch goal with
    | H : _ /\ _ |- _ => destruct H
    end.
    subst.
    induction known using rev_ind;
      subst; cbn [map fold_left concat] in *; intros; [ reflexivity | ].
    rewrite concat_snoc.
    rewrite map_app, fold_left_app, app_length.
    cbn [map fold_left]. lia.
  Qed.

  (* Helper lemma for invert that helps prove other lemmas by removing
     the chain structure. *)
  Lemma invert_flat (regs : registers) :
    concat (fst (invert regs)) = map negb (concat (fst regs)).
  Proof.
    cbv [invert]. destruct regs as [known unknown]; cbn [fst snd].
    induction known; [ reflexivity | ].
    cbn [concat map]. rewrite map_app, IHknown. reflexivity.
  Qed.
  
  Lemma invert_ne (regs : registers) (chains : list nat) mlen :
    is_sequential chains ->
    regs_wf regs chains mlen ->
    invert regs <> regs.
  Proof.
    cbv [is_sequential].  intros. intro.
    lazymatch goal with
    | H : regs_wf _ _ _ |- _ => apply length_known_regs in H
    end.
    assert (concat (fst (invert regs)) = concat (fst regs)) as Hconcat by congruence.
    destruct regs as [known unknown]; cbn [fst snd] in *.
    rewrite invert_flat in Hconcat. cbn [fst snd] in *.
    destruct (concat known); cbn [map length] in *; [ lia | ].
    lazymatch goal with
    | H : _ :: _ = _ :: _ |- _ => inversion H
    end.
    eapply Bool.no_fixpoint_negb; eauto.
  Qed.
    
  (* A single scan chain is not enough to detect even a purely
     combinational trojan; for every good circuit, there exists a
     combinational trojan that will be indistinguishable from it. *)
  Lemma single_chain_insufficient
    (facade : logic) (nregs : nat) :
    logic_wf facade [nregs] 0 ->
    (* there is at least one register (helpful for making the
    counterexample, we have to observe something to observe a
    difference -- can probably weaken to at least one register or a
    non-empty output *)
    is_sequential [nregs] ->
    exists trojan,
      (* trojan is a constructable circuit *)
      logic_wf trojan [nregs] 0
      (* the two circuits are not equivalent*)
      /\ (exists regs se i,
             regs_wf regs [nregs] 0
             /\ fst (trojan regs se i) <> fst (facade regs se i))
      (* but they are indistinguishable by scanning *)
      /\ indistinguishable trojan facade [nregs] 0.
  Proof.
    cbv [indistinguishable]; intros.
    (* there exists a trojan that imitates the facade's combinational
       logic when enable is high, but inverts everything when scan is
       low *)
    set (trojan :=fun regs se i =>
              let en := hd false se in
              let f := facade regs se i in
              let regs' := fst f in
              let o := snd f in
              if en
              then facade regs se i
              else (invert regs', o)).
    exists trojan.
    cbn [scan_step fst snd].
    repeat match goal with
           | |- _ /\ _ => split
           end.
    { (* prove the trojan is well-formed *)
      cbv [logic_wf]. subst trojan.
      intros regs ms i Hregs.
      lazymatch goal with H : logic_wf _ _ _ |- _ => specialize (H regs ms i Hregs) end.
      cbv zeta in *. cbn [fst snd] in *.
      destruct (hd false ms); [ assumption | ].
      cbn [fst snd].
      apply regs_wf_after_invert; auto. }
    { (* prove that a bad non-scan input exists *)
      let regs := constr:(([repeat false nregs], @nil bool)) in
      let se := constr:(repeat false nregs) in
      let i := constr:(@nil bool) in
      assert (regs_wf regs [nregs] 0)
        by (split; cbn; rewrite ?repeat_length; reflexivity);
      exists regs, se, i.
      subst trojan. cbn. split; [ assumption | ].
      rewrite !hd_repeat.
      eapply invert_ne; eauto. }
    { intros [k u]; intros. cbn [fst snd].
      cbv [regs_wf] in *. cbn [fst snd] in *.
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             | H : length ?x = 0 |- _ => destruct x; [| cbn [length] in H; lia]
             end.
      split; reflexivity. }
  Qed.

End WithAbstractDefs.
