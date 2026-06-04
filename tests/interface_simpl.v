From HB Require Import structures.
From Stdlib Require Import ZArith.


(* #[verbose,alternative,local="this"] HB.interface hey.
#[alternative] HB.interface hey.
#[alternative="this"] HB.interface hey. *)
(* #[verbose] HB.interface only_verbose.
#[verbose,alternative] HB.interface verbose_alternative.
#[alternative] HB.interface only_alternative. *)
(* #[verbose,alternative,local="this"] HB.interface hey. *)

HB.mixin Record isB T := {
    opB : T -> T -> T;
    opAB : forall x y z, opB x (opB y z) = opB (opB x y) z
  }.

HB.structure Definition B := {T of isB T}.



(* Interface should behave as a mixin *)
HB.interface Record SemiGroup T := {
    op : T -> T -> T;
    opA : forall x y z, op x (op y z) = op (op x y) z
  }.

HB.structure Definition SemiGroupS := {T of SemiGroup T}.
HB.instance  Definition _ := SemiGroup.Build Z Z.add Z.add_assoc.

Lemma lestfassoc (T : SemiGroupS.type) (x y z : T) : op (op x y) z = op x (op y z).
  Proof. symmetry. apply opA. Qed.


(* Building a mixin dependent on a previous one *)
HB.interface Record isGroup T of SemiGroup T := { 
    e : T;
    idl : forall x, op e x = x;
    idr : forall x, op x e = x;
    invl : forall x, exists xinv, op x xinv = e;
    invr : forall x, exists xinv, op xinv x = e;
}.


(* Structure requires the two mixins *)
HB.structure Definition Group := {T of SemiGroup T & isGroup T}.



(* Building a mixin dependent on a previous one *)
HB.interface Record ComGroup T of Group T := { (*of SemiGroup T*)
    opC : forall x y:T, op x y = op y x;
}.

HB.structure Definition ComGroupS := {T of ComGroup T &}.



#[alternative] HB.interface Record ComGroup T  of SemiGroup T:= { (*of SemiGroup T*)
    opC : forall x y:T, op x y = op y x;
    e : T;
    idr : forall x, op x e = x;
    invr : forall x, exists xinv, op xinv x = e;
}.


HB.builders Context T of ComGroupFACT T.
(* assumption *)
Lemma invl : forall x, exists xinv, op x xinv = e.
  intros. destruct (invr x). exists x0. rewrite opC. auto. Qed.
Lemma idl : forall x, op e x = x. 
    intros. rewrite opC. apply idr. Qed. 

HB.instance Definition _ := isGroup.Build T e idl idr invl invr.
HB.instance Definition _ := ComGroup.Build T opC.

HB.end.


