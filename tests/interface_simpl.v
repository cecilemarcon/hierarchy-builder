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

HB.mixin Record A' T := {
    a' : T -> T -> T;
  }.

HB.structure Definition AS := {T of A' T &}. 

HB.mixin Record B' T of A' T:= { 
    b' : forall x:T, a' x x = x;
}.

HB.structure Definition BS := sigT (fun T => (prod (B' T) False)%type).



HB.interface Record A T := {
    a : T -> T -> T;
  }.

(* TODO should become B T := A T & {} *)
HB.interface Record B T := { 
    b : forall x:T, a x x = x ;
} & A T.

(* <=> HB.mixin Record A_isB T of A T := { 
    b : forall x:T, a x x = x ;
    b2 : T
}.

HB.structure Definition B := {T of A T & A_isB T}.

*)



(* HB.structure Definition TS' := sigT (fun T => (prod (isT T) False)%type). *)







(* BASIC ALGEBRA *)

(* Interface should behave as a mixin *)
(* #[diff="iMagma"] *)
HB.interface Record Magma T := {
    op : T -> T -> T;
}. 

(* #[diff="Magma_isSemiGroup"] *)
HB.interface Record SemiGroup T := {
  opA : forall x y z:T, op x (op y z) = op (op x y) z
} & Magma T.

(* TODO when changing instance : in one line *)
HB.instance  Definition _ := Magma.Build Z Z.add.
HB.instance  Definition _ := SemiGroup.Build Z Z.add_assoc.

(* TODO : in instance, the constructor should be the name of the diff, not name of interface, because the constructors may in fine mean different things, like :

HB.interface Definition SemiGroup T := Magma T & Associative (op T).
*)

(* #[alternative, diff="Magma_isSemiGroup"]
HB.interface Record SemiGroup T := {
  opA : forall x y z:T, op x (op y z) = op (op x y) z
} & Magma T.
Proof. by []. Qed. *)


HB.about SemiGroup.
HB.about SemiGroupSTRUCT.
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