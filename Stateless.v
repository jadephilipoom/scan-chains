Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* Defines the purely combinational logic of an honest circuit
   (essentially a Moore machine). *)
Definition logic : Type :=
  forall
    (* register values *)
    (regs : list bool)
    (* scan enable bit *)
    (se : bool)
    (* input value for this cycle *)
    (i : list bool),
    (* new registers + output*)
    list bool * list bool.

(* boilerplate: list equality definition *)
Fixpoint list_eqb {A} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | a1 :: l1, a2 :: l2 => if eqb a1 a2 then list_eqb eqb l1 l2 else false
  | _, _ => false
  end.
Lemma list_eqb_spec {A} {eqb : A -> A -> bool}
  (eqb_spec : forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (eqb a1 a2)) :
  forall l1 l2,
    BoolSpec (l1 = l2) (l1 <> l2) (list_eqb eqb l1 l2).
Proof.
  induction l1 as [|a1 l1]; destruct l2 as [|a2 l2];
    cbn [list_eqb]; intros; try (constructor; congruence); [ ].
  destruct (eqb_spec a1 a2); subst; [ | constructor; congruence ].
  destruct (IHl1 l2); subst; constructor; congruence.
Qed.

(* boilerplate: boolean equality spec *)
Lemma Bool_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (Bool.eqb x y).
Proof. destruct x, y; cbn [Bool.eqb]; intros; constructor; congruence. Qed.

Section WithAbstractDefs.

  (* trace of a circuit running with scan enable never set *)
  Fixpoint trace (M : logic) (input : list (list bool)) (regs : list bool)
    : list (list bool) :=
    match input with
    | [] => []
    | i :: input =>
        let mstep := M regs false i in
        let mregs := fst mstep in
        let mout := snd mstep in
        mout :: trace M input mregs
    end.

  (* trace of a circuit running with scan enables sometimes set, some
     states visible *)
  Fixpoint scan_trace
    (M : logic) (input : list (list bool * option (list bool))) (regs : list bool)
    : list (option (list bool) * list bool) :=
    match input with
    | [] => []
    | i :: input =>        
        (* infer scan-enable signal and reset registers if needed *)
        let se := match (snd i) with | Some _ => true | None => false end in
        (* step the logic *)
        let mstep := M regs se (fst i) in
        let mregs := fst mstep in
        let mout := snd mstep in
        (* determine if we read the register values *)
        let read_regs := if se then Some mregs else None in
        (* replace register values if we scanned (note: this is
        slightly less general than realistic, because the tester could
        always feed the mregs values back in, but the difference is an
        advantage for M so proofs should be stronger because of it) *)
        let mregs := match (snd i) with | Some x => x | None => mregs end in
        (* add the registers we read and the circuit output to the trace *)
        (read_regs, mout) :: scan_trace M input mregs
    end.

  (* step only the circuit state *)
  Fixpoint exp_regs (H : logic) (input : list (list bool)) (regs : list bool)
    : list bool :=
    match input with
    | [] => regs
    | i :: input =>
        let hstep := H regs false i in
        let hregs := fst hstep in
        let hout := snd hstep in
        exp_regs H input hregs
    end.

  (* states that M does something that "matters" on the given input x
     state when the scan bit is low -- it will eventually change the
     output of the circuit, although maybe not immediately *)
  Definition consequential
    (M H : logic) (start_regs : list bool)
    (input : list (list bool)) : Prop :=
    (* either the trace is already different... *)
    trace M input start_regs <> trace H input start_regs
    (* ...or M has done something to the state such that, if the scan
    bit is low, M will act differently on that state than the honest
    state (i.e. M does not ignore the state change it made) and M will
    act differently on that state than H would on the honest state
    (i.e. M does not undo its own change and stop causing trouble). *)
    (* note: the forall here is a little strong, it says M must
    *never* ignore the state change. should be weakened to something
    probablistic, e.g. the tester has a good chance of randomly
    selecting an input where M's trace differs *)
    \/ (forall i,
           let mregs := exp_regs M input start_regs in
           let hregs := exp_regs H input start_regs in
           M mregs false i <> M hregs false i
           /\ M mregs false i <> H hregs false i).

  (* states that some logic is honest, i.e. it ignores the scan bit *)
  Definition honest (H : logic) :=
    forall regs se1 se2 i, H regs se1 i = H regs se2 i. 

  Definition detectable (M H : logic) (start_regs : list bool)
    (scan_input : list (list bool * option (list bool))) : Prop :=
    (* the scan trace on M is different from the scan trace on H
         with the same input and start value *) 
    scan_trace M scan_input start_regs <> scan_trace H scan_input start_regs.

  Lemma run_before_scanning :
    forall M run_input scan_input start_regs,
      scan_trace M (map (fun x => (x, None)) run_input ++ scan_input) start_regs
      = map (fun x => (None, x)) (trace M run_input start_regs)
          ++ scan_trace M scan_input (exp_regs M run_input start_regs).
  Proof.
    induction run_input; intros; [ reflexivity | ].
    cbn [map trace exp_regs]. rewrite <-app_comm_cons.
    cbn [scan_trace fst snd]. rewrite IHrun_input. reflexivity.
  Qed.

  (* helper lemma: pairing with something does not change list equality *)
  Lemma map_pair_eq {A B} (b : B) :
    forall (l1 l2 : list A),
      map (fun x => (b, x)) l1 = map (fun x => (b, x)) l2 -> l1 = l2.
  Proof.
    induction l1; destruct l2; cbn [map]; try congruence; [ ].
    inversion 1; intros; subst.
    apply f_equal. apply IHl1; auto.
  Qed.

  (* core argument: we know how H should behave on all states,
     therefore whatever state M uses, we could always trigger that
     state and observe the correction. *)

  (* states that a fully combinational M must be catchable by some scan input *)
  Lemma combinational_detectable :
    forall H (input : list (list bool)) i start_regs M,
      honest H ->
      consequential M H start_regs input ->
      (* first just run the circuit until we get to the point where M
         has done something or is about to do something *)
      let scan_input := map (fun x => (x, None)) input in
      (* get the expected value of the honest registers after that trace *)
      let hregs := exp_regs H input start_regs in
      (* get the expected value of the faulted registers after that trace *)
      let mregs := exp_regs M input start_regs in
      (* run two scans, one which forces M to correct and one where it shouldn't *)
      let scan_input := scan_input ++ [(i, Some mregs)] ++ [(i, Some mregs)] in
      (* if H would produce a different state or output on the faulted state... *)
      H mregs false i <> H hregs false i ->
      (* ..then M is detectable by the scan pattern. *)
      detectable M H start_regs scan_input.
  Proof.
    cbv [detectable]; intros.
    rewrite !run_before_scanning. cbn [app].
    cbn [scan_trace fst snd].
    (* transform _ ++ (_ :: _ :: nil) into _ ++ (_ :: nil) ++ (_ :: nil) *)
    repeat lazymatch goal with
           | |- context[?l ++ [?x; ?y]] =>
               replace (l ++ [x; y]) with ((l ++ [x]) ++ [y])
               by (rewrite <-app_assoc; reflexivity)
           end.
    rewrite !app_inj_tail_iff.
    intro.
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           | H : (_,_) = (_,_) |- _ => inversion H; clear H
           | H : map ?f ?l1 = map ?f ?l2 |- _ => apply map_pair_eq in H; congruence
           | H1 : fst ?x = fst ?y, H2 : snd ?x = snd ?y |- _ =>
               assert (x = y) by (rewrite (surjective_pairing x), (surjective_pairing y); congruence); clear H1 H2
           end.
    cbv [consequential] in *.
    (* case analysis on whether first part of trace is equal *)
    match goal with
    | H : ?x <> ?y \/ _ |- _ =>
        destruct (list_eqb_spec (list_eqb_spec Bool_eqb_spec) x y);
        [ destruct H; try congruence; replace x with y in * by congruence
        | match goal with
          | H : map ?f ?l1 = map ?f ?l2 |- _ => apply map_pair_eq in H; congruence
          end ]
    end.

    lazymatch goal with
    | H : forall i, M _ _ i <> M _ _ i /\ _ |- _ =>
        specialize (H i); destruct H
    end.

    remember (exp_regs M input start_regs) as mI.
    remember (exp_regs H input start_regs) as hI.

    lazymatch goal with
    | H1 : ?m _ _ _ <> ?m _ _ _, H2: honest ?m |- False =>
        apply H1; rewrite !H2 with (se1:=false) (se2:=true)
    end.
    congruence.
  Qed.

End WithAbstractDefs.
