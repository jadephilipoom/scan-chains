Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Section Registers.
  (* Special registers, x0 and x1. x0 is fixed to the value 0, and x1
     interacts with the call stack. *)
  Inductive special_gpr : Type := x0 | x1.
  
  (* General-purpose registers, 32 bits each. Special registers x0 and x1 are omitted. *)
  Inductive gpr : Type :=
  | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9
  | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19
  | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29
  | x30 | x31
  .

  Inductive wdr : Type:=
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7 | w8 | w9
  | w10 | w11 | w12 | w13 | w14 | w15 | w16 | w17 | w18 | w19
  | w20 | w21 | w22 | w23 | w24 | w25 | w26 | w27 | w28 | w29
  | w30 | w31
  .

  Inductive wsr : Type :=
  | MOD
  | ACC
  .

  Inductive reg :=
  | gpreg : gpr -> reg
  | wdreg : wdr -> reg
  | wsreg : wsr -> reg
  .
End Registers.

Section Flags.
  Inductive flag_group : Type :=
  | FG0
  | FG1
  .

  Inductive flag : Type :=
  | flagC : forall fg : flag_group, flag
  | flagM : forall fg : flag_group, flag
  | flagL : forall fg : flag_group, flag
  | flagZ : forall fg : flag_group, flag
  .
End Flags.

Section ISA.

  Inductive limb : Type :=
  | limb0 : wdr -> limb
  | limb1 : wdr -> limb
  | limb2 : wdr -> limb
  | limb3 : wdr -> limb
  .

  Inductive shift : Type :=
  | lshift : Z -> shift
  | rshift : Z -> shift
  .

  Inductive Insn : Type :=
  | Mulqacc : forall (z : bool), limb -> limb -> Z -> Insn
  | Mulqacc_wo : forall (z : bool), wdr -> limb -> limb -> Z -> Insn
  | Mulqacc_so : forall (z : bool) (L : bool), wdr -> limb -> limb -> Z -> Insn
  | Addm : wdr -> wdr -> wdr -> Insn
  | Subm : wdr -> wdr -> wdr -> Insn
  | Add : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Addc : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Sub : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Subb : wdr -> wdr -> wdr -> shift -> flag_group -> Insn
  | Rshi : wdr -> wdr -> wdr -> Z -> Insn
  .
