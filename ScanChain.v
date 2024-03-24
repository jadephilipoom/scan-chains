Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bool.
Import VectorNotations.
Local Arguments nil {_}.

Inductive Data : Type :=
| DataVec : nat -> Data
| DataPair : Data -> Data -> Data
.

Fixpoint interp_data (t : Data) : Type :=
  match t with
  | DataVec n => Vector.t bool n
  | DataPair t1 t2 => interp_data t1 * interp_data t2
  end.
Notation DataBit := (DataVec 1) (only parsing).

Inductive Circuit : Data -> Data -> Type :=
| Comb : forall {i o : Data} (f : interp_data i -> interp_data o), Circuit i o
| Compose : forall {i m o : Data} (c1 : Circuit i m) (c2 : Circuit m o), Circuit i o
| Fst : forall {i o t} (c : Circuit i o), Circuit (DataPair i t) (DataPair o t)
| Delay : forall {t : Data} (reset : interp_data t), Circuit t t
.

Fixpoint state_type {i o : Data} (c : Circuit i o) : Type :=
  match c with
  | Comb f => unit
  | Compose c1 c2 => state_type c1 * state_type c2
  | Fst c => state_type c
  | @Delay t r => interp_data t
  end.

Fixpoint step {i o : Data} (c : Circuit i o)
  : interp_data i -> state_type c -> state_type c * interp_data o :=
  match c with
  | Comb f => fun input _ => (tt, f input)
  | Compose c1 c2 => fun input (state : state_type c1 * state_type c2) =>
                       let intermediate := step c1 input (fst state) in
                       let c1_state := fst intermediate in
                       let c1_out := snd intermediate in
                       let final := step c2 c1_out (snd state) in
                       let c2_state := fst final in
                       let c2_out := snd final in
                       ((c1_state, c2_state), c2_out)
  | Fst c => fun input (state : state_type c) =>
               let rec := step c (fst input) state in
               let c_state := fst rec in
               let c_out := snd rec in
               (c_state, (c_out, snd input))
  | @Delay t r => fun input state : interp_data t =>  (input, state)
  end.

Fixpoint reset_state {i o : Data} (c : Circuit i o) : state_type c :=
  match c with
  | Comb f => tt
  | Compose c1 c2 => (reset_state c1, reset_state c2)
  | Fst c => reset_state c
  | Delay r => r
  end.

Definition interp {i o : Data} (c : Circuit i o) (input : list (interp_data i))
  : state_type c * list (interp_data o) :=
  List.fold_left (fun (state : state_type c * list (interp_data o)) (next : interp_data i) =>
                    let rec := step c next (fst state) in
                    let state' := fst rec in
                    let out := snd rec in
                    (state', (out :: snd state)%list))
    input (reset_state c, List.nil).

Local Infix ">=>" := Compose (at level 40).  
Definition with_mystery
  {t} (mystery : Circuit (DataPair t DataBit) t) (r1 r2 : interp_data t)
  : Circuit (DataPair t DataBit) t :=
  Fst (Delay r1) >=> mystery >=> Delay r2.

Definition is_honest {i o} (c : Circuit (DataPair i DataBit) o) : Prop :=
  (* the circuit produces the same outputs on the same input stream if scan_enable bit is false compared to when it's true *)
  forall (input1 input2 : list (interp_data i * interp_data DataBit)),
    (* input streams are the same except for SE bit *)
    List.map fst input1 = List.map fst input2 ->
    interp c input1 = interp c input2.

Definition is_dishonest {i o} (c : Circuit (DataPair i DataBit) o) : Prop :=
  exists (input1 input2 : list (interp_data i * interp_data DataBit)),
    List.map fst input1 = List.map fst input2
    /\ interp c input1 <> interp c input2.

Lemma is_dishonest_not_honest {i o} (c : Circuit (DataPair i DataBit) o) :
  is_dishonest c -> ~ is_honest c.
Proof.
  cbv [is_dishonest]; intro Hdishonest.
  destruct Hdishonest as [? [? [? ?]]].
  cbv [is_honest]. intro.
  intuition.
Qed.

Fixpoint is_comb {i o} (c : Circuit i o) : bool :=
  match c with
  | Comb f => true
  | Compose c1 c2 => is_comb c1 && is_comb c2
  | Fst c => is_comb c
  | Delay r => false
  end.

Fixpoint default (t : Data) : interp_data t :=
  match t with
  | DataVec n => Vector.const false n
  | DataPair t1 t2 => (default t1, default t2)
  end.

Lemma interp_Comb {i o} f (input : list (interp_data i)) :
  interp (@Comb i o f) input = (tt, List.map f input).
Admitted.

Lemma interp_Compose {i m o} c1 c2 (input : list (interp_data i)) :
  let r1 := interp c1 input in
  let state1 := fst r1 in
  let out1 := snd r1 in
  let r2 := interp c2 out1 in
  let state2 := fst r2 in
  let out2 := snd r2 in
  interp (@Compose i m o c1 c2) input = ((state1, state2), out2).
Admitted.

Lemma interp_Fst {i o t} (c : Circuit i o) (input : list (interp_data i * interp_data t)) :
  let r := interp c (List.map fst input) in
  let state := fst r in
  let out := snd r in
  interp (Fst c) input = (state, List.combine out (List.map snd input)).
Admitted.

Lemma interp_Delay {t} (reset : interp_data t) (input : list (interp_data t)) :
  interp (Delay reset) input = (List.last input (default t), List.removelast input).
Admitted.

Lemma last_map {A B} (f : A -> B) (l : list A) d fd :
  fd = f d ->
  List.last (List.map f l) fd = f (List.last l d).
Admitted.

Lemma removelast_map {A B} (f : A -> B) (l : list A) :
  List.removelast (List.map f l) = List.map f (List.removelast l).
Admitted.

(* want to say we cannot detect a trojan in with_mystery
   exists some combinational circuit such that
   the circuit is dishonest
   and we cannot detect it...meaning, for all possible input streams we could test with SE high on at least one cycle, it behaves the same as an honest circuit
*)
Lemma with_mystery_undetectable {t} (r1 r2 : interp_data t) :
  forall (facade : interp_data (DataPair t DataBit) -> interp_data t),
  exists (trojan : interp_data (DataPair t DataBit) -> interp_data t),
    is_dishonest (Comb trojan) ->
    forall (test_input : list (interp_data t * interp_data DataBit)),
      interp (with_mystery (Comb trojan) r1 r2) test_input = interp (with_mystery (Comb facade) r1 r2) test_input.
Proof.
  intros.
  exists (fun input : interp_data t * interp_data DataBit =>
            let se := hd (snd input) in
            if se
            then facade input
            else default t).
  intros Hdishonest test_input.
  cbv [is_dishonest] in *.
  destruct Hdishonest as [input1 [input2 [? ?]]].
  cbv [with_mystery].
  rewrite !interp_Comb in *.
  rewrite !interp_Compose.
  cbn [fst snd].
  rewrite !interp_Delay.
  cbn [fst snd].
  rewrite !interp_Comb.
  cbn [fst snd].
  lazymatch goal with
  | |- context [List.last (@List.map ?A ?B ?f ?l)] =>
      remember (@List.map A B f l) as L1;      
      lazymatch goal with
      | |- context [List.last (List.map ?f ?l)] =>
          remember (List.map f l) as L2
      end
  end.
  replace L1 with L2.
  { reflexivity. }
  { subst L1 L2.
    
  
    
Qed.
    
    
  
  

  

Compute hd [1;2;3].
Compute tl [1;2;3].
Compute hd (tl (tl [1;2;3])).

Definition nandf (input : interp_data (DataVec 2)) : interp_data (DataVec 1) :=
  let i0 := hd input in
  let i1 := hd (tl input) in
  negb (i0 && i1) :: nil.

Definition invf (input : interp_data (DataVec 1)) : interp_data (DataVec 1) :=
  let i0 := hd input in
  negb i0 :: nil.

Definition and : Circuit (DataVec 2) (DataVec 1) :=
  Compose (Comb nandf) (Comb invf).

Lemma and_correct :
  forall i0 i1 : bool, interp and [i0; i1] = [i0 && i1].
Proof.
  intros.
  destruct i0, i1; reflexivity.
Qed.

Compute (interp and [true; true]).
Compute (interp and [true; false]).
