From HB Require Import structures.
From Stdlib Require Import ZArith.



HB.mixin Record isTest T := {
    test1 : T -> T -> T;
    test2 : forall x y z, test1 x (test1 y z) = test1 (test1 x y) z
  }.

(* Inspect 5. *)
HB.structure Definition testS := {T of isTest T &}. 
(* Set Printing All. 
Check testS nat. *)

(* Check isTestSTRUCT. *)

(* Elpi Trace Browser. *)
(* Interface should behave as a mixin *)
HB.interface Record SemiGroup T := {
    op : T -> T -> T;
    opA : forall x y z, op x (op y z) = op (op x y) z
  }.

(* HB.structure Definition SemiGroupS := {T of SemiGroup T}. *)
HB.instance  Definition _ := SemiGroup.Build Z Z.add Z.add_assoc.

Lemma lestfassoc (T : SemiGroupSTRUCT.type) (x y z : T) : op (op x y) z = op x (op y z).
  Proof. symmetry. apply opA. Qed.





(* Building a mixin dependent on a previous one *)
HB.mixin Record isT T of isTest T := { 
    a1 : T;
    a2 : forall x, test1 a1 x = x;
    a5 : forall x, exists xinv, test1 xinv x = a1;
}.

(* HB.structure Definition TS := {T of isT T & }.  *)
HB.structure Definition TS' := sigT (fun T => (prod (isT T) False)%type).



HB.interface Record Group T of SemiGroup T := { 
    e : T;
    idl : forall x, op e x = x;
    idr : forall x, op x e = x;
    invl : forall x, exists xinv, op x xinv = e;
    invr : forall x, exists xinv, op xinv x = e;
}.

HB.about Group.
HB.about isT.
(* Structure requires the two mixins *)
(* HB.structure Definition Group := {T of SemiGroup T & isGroup T}. *)



(* Building a mixin dependent on a previous one *)
HB.interface Record ComGroup T of Group T := { (*of SemiGroup T*)
    opC : forall x y:T, op x y = op y x;
}.

(* HB.structure Definition ComGroupS := {T of ComGroup T &}.  *)


#[alternative="ComGroupFromSemiGroup"] HB.interface Record ComGroup T of SemiGroup T:= { (*of SemiGroup T*)
    opC : forall x y:T, op x y = op y x;
    e : T;
    idr : forall x, op x e = x;
    invr : forall x, exists xinv, op xinv x = e;
}.



(* Elpi Trace Browser. *)

HB.builders Context T of ComGroupFromSemiGroup T.
(* assumption *)
Lemma invl : forall x, exists xinv, op x xinv = e.
  intros. destruct (invr x). exists x0. rewrite opC. auto. Qed.
Lemma idl : forall x, op e x = x. 
    intros. rewrite opC. apply idr. Qed. 

HB.instance Definition _ := isGroup.Build T e idl idr invl invr.
HB.instance Definition _ := ComGroup.Build T opC.

HB.end. 