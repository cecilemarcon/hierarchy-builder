From HB Require Import structures.
From Stdlib Require Import ZArith.

(* 
#[arguments(raw)] Elpi Command check_arg.
Elpi Accumulate lp:{{

  main [trm T] :-
    coq.typecheck T Ty D,
    if (D = ok)
      (coq.say "The type of" T "is" Ty)
      (true).
}}.


Elpi check_arg (1 = 0).
Elpi check_arg (1 = true). *)



(* SMALL TESTS *)

HB.mixin Record isTest T := {
    test1 : T -> T -> T;
    test2 : forall x y z, test1 x (test1 y z) = test1 (test1 x y) z
  }.

HB.structure Definition testS := {T of isTest T &}. 

HB.mixin Record isT T of isTest T := { 
    a1 : T;
    a2 : forall x, test1 a1 x = x;
    a5 : forall x, exists xinv, test1 xinv x = a1;
}.

HB.structure Definition TS' := sigT (fun T => (prod (isT T) False)%type).



HB.interface Record A T := {
    a : T -> T -> T;
  }.

(* TODO should become B T := A T + {} *)
HB.interface Record B T of A T := { 
    b : forall x:T, a x x = x
}.

(* HB.structure Definition TS' := sigT (fun T => (prod (isT T) False)%type). *)







(* BASIC ALGEBRA *)

(* Interface should behave as a mixin *)
HB.interface Record Magma T := {
    op : T -> T -> T;
}. 

HB.interface Record SemiGroup T of Magma T := {
  opA : forall x y z:T, op x (op y z) = op (op x y) z
}.

(* TODO when changing instance : in one line *)
HB.instance  Definition _ := Magma.Build Z Z.add.
HB.instance  Definition _ := SemiGroup.Build Z Z.add_assoc.

Lemma lestfassoc (T : SemiGroupSTRUCT.type) (x y z : T) : op (op x y) z = op x (op y z).
  Proof. symmetry. apply opA. Qed.







HB.interface Record Group T of SemiGroupSTRUCT T := { 
    e : T;
    idl : forall x, op e x = x;
    idr : forall x, op x e = x;
    invl : forall x, exists xinv, op x xinv = e;
    invr : forall x, exists xinv, op xinv x = e;
}.

(* Print GroupSTRUCT.
Print Group. *)

HB.interface Record ComGroup T of GroupSTRUCT T := { 
    opC : forall x y:T, op x y = op y x;
}.

(* HB.structure Definition ComGroupS := {T of ComGroup T &}.  *)

(* HB.factory Record ComGroup' T of SemiGroupSTRUCT T:= { (*of SemiGroup T*)
    opC : forall x y:T, op x y = op y x;
    e : T;
    idr : forall x, op x e = x;
    invr : forall x, exists xinv, op xinv x = e;
}.


HB.builders Context T (_: ComGroup' T).
(* assumption *)
Lemma invl : forall x, exists xinv, op x xinv = e.
  intros. destruct (invr x). exists x0. rewrite opC. auto. Qed.
Lemma idl : forall x, op e x = x. 
    intros. rewrite opC. apply idr. Qed. 

HB.instance Definition _ := Group.Build T e idl idr invl invr.
HB.instance Definition _ := ComGroup.Build T opC.

HB.end.  *)

#[alternative="ComGroupFromSemiGroup"] HB.interface Record ComGroup T of SemiGroupSTRUCT T:= { (*of SemiGroup T*)
    opC : forall x y:T, op x y = op y x;
    e : T;
    idr : forall x, op x e = x;
    invr : forall x, exists xinv, op xinv x = e;
}.
Lemma invl : forall x, exists xinv, op x xinv = e.
  intros. destruct (invr x). exists x0. rewrite opC. auto. Qed.
Lemma idl : forall x, op e x = x. 
    intros. rewrite opC. apply idr. Qed. 
Locate idl.
HB.instance Definition _ := Group.Build T e idl idr invl invr.
HB.instance Definition _ := ComGroup.Build T opC.

HB.end. 


HB.interface Record ComMonoid T of Magma T := {
  opC' : forall x y:T, op x y = op y x
}.

#[alternative="ComGroupFromGroupAndComMonoid"] HB.interface Record ComGroup T of 
  GroupSTRUCT T & ComMonoid T := { (*of SemiGroup T*)
}.
HB.instance Definition _ := ComGroup.Build T opC'.
HB.end. 

Check 0.