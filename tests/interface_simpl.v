From HB Require Import structures.
From Stdlib Require Import ZArith List.
Import ListNotations.


Declare Custom Entry assignment.
Record assignement {T1 T2} := Assign {lhs : T1 ; rhs : T2}.
Definition dfltassign := Assign unit unit tt tt.
Infix ":==" := Assign (at level 0).
(* Notation "x ':=' y" := (Assign x y) (x at level 100, y at level 100, in custom assignment at level 0). *)
(* Notation "'@{' a '}'" := a (at level 100, at level 0). *)
(* Notation "'_'" := dfltassign (at level 0). *)
(* Definition boolltassign := @{ tt :== tt }. *)

Inductive assignement_tele : list Type -> list Type -> Type :=
| NoAssign : assignement_tele [] []
| ConsAssign {N A Ns As} :
  @assignement N A -> assignement_tele Ns As ->
  assignement_tele (N :: Ns) (A :: As).
Notation "'{/' a1 ; .. ; an '/}'" := 
  (ConsAssign a1 .. (ConsAssign an NoAssign) ..).
  (* (a1 custom assignment, an custom assignment). *)


  
(* SMALL TESTS *)

HB.mixin Record A' T := {
    a' : T -> T -> T;
  }.

HB.structure Definition AS := {T of A' T &}. 


HB.mixin Record C' T := {
    c' : T ;
  }.

HB.structure Definition CS := {T of C' T &}. 

HB.instance Definition _ : C' bool := C'.Build bool true.

HB.mixin Record B' T of A' T:= { 
    b' : forall x:T, a' x x = x;
}.

HB.structure Definition BS := sigT (fun T => (prod (B' T) False)%type).

HB.mixin Record D' T of A' T & C' T := { 
  d' : forall x:T, a' x c' = x ;
}.


#[diff="isA"]
HB.interface Record A T := {
    a : T -> T -> T;
  }.



#[diff="isC"]
HB.interface Record C T := {
    c : T
  }.

(* Locate isC.Axioms_.
Print isC.
*)
(* HB.about C. 


Check isC.Axioms_.
Check C.axioms_.

  
 
About c.  *)
HB.howto C.type.
(* HB.howto isC. *)
HB.proof Definition _ : C bool := {/ c :== true /}.
(* HB.proof Definition _  := isC.Build bool true.
HB.howto bool C.type. *)

(* HB.proof C bool := {| c := true |}. *)

(* 
(* TODO should become B T := A T & {} *)
#[diff="B_isA"]
HB.interface Record B T := { 
    b : forall x:T, a x x = x ; 
} & A T.

#[diff="D_isAandC"]
HB.interface Record D T := { 
  d : forall x:T, a x c = x ;
} & A T & C T.







(* BASIC ALGEBRA *)

(* Interface should behave as a mixin *)
#[diff="isMagma"]
HB.interface Record Magma T := {
    op : T -> T -> T;
}. 

#[diff="Magma_isSemiGroup"]
HB.interface Record SemiGroup T := {
  opA : forall x y z:T, op x (op y z) = op (op x y) z
} & Magma T.

(* TODO when changing instance : in one line *)
HB.instance Definition _ : isMagma Z := isMagma.Build Z Z.add.
HB.instance Definition _ := Magma_isSemiGroup.Build Z Z.add_assoc.

(* TODO : in instance, the constructor should be the name of the diff, not name of interface, because the constructors may in fine mean different things, like :

HB.interface Definition SemiGroup T := Magma T & Associative (op T).
*)

Lemma lestfassoc (T : SemiGroup.type) (x y z : T) : op (op x y) z = op x (op y z).
  Proof. symmetry. apply opA. Qed.






#[diff="SemiGroup_isGroup"]
HB.interface Record Group T := { 
    e : T;
    idl : forall x, op e x = x;
    idr : forall x, op x e = x;
    invl : forall x, exists xinv, op x xinv = e;
    invr : forall x, exists xinv, op xinv x = e;
} & SemiGroup T.


#[diff="Group_isComGroup"]
HB.interface Record ComGroup T := { 
    opC : forall x y:T, op x y = op y x;
} & Group T.

#[alternative="ComGroupFromSemiGroup"] 
HB.interface Record ComGroup T := { (*of SemiGroup T*)
    opC : forall x0 y:T, op x0 y = op y x0;
    e : T;
    idr : forall x1, op x1 e = x1;
    invr : forall x2, exists xinv, op xinv x2 = e; 
} & SemiGroup T.

Lemma invl : forall x, exists xinv, op x xinv = e.
  intros. destruct (invr x). exists x0. rewrite opC. auto. Qed.
Lemma idl : forall x, op e x = x. 
    intros. rewrite opC. apply idr. Qed. 

HB.instance Definition _ := SemiGroup_isGroup.Build T e idl idr invl invr.
HB.instance Definition _ := Group_isComGroup.Build T opC.

HB.end. 


#[diff="Magma_isComMonoid"]
HB.interface Record ComMonoid T := {
  opC' : forall x y:T, op x y = op y x
} & Magma T.

#[alternative="ComGroupFromGroupAndComMonoid"] HB.interface Record ComGroup T := 
{ (*of SemiGroup T*)
} & Group T & ComMonoid T.
HB.instance Definition _ := Group_isComGroup.Build T opC'.
HB.end. 

Check 0.


(* 
#[arguments(raw)] Elpi Command check_arg.
Elpi Accumulate lp:{{

main [const-decl Name (some BodySkel) TyWPSkel] :-
  coq.say "type given:" TyWPSkel "\nBodySkel : " BodySkel "\nName" Name.
  
main A :- parse-fields A B, coq.say "A" A "\nB:" B.

pred parse-fields i:list argument, o:list argument.
parse-fields [] [].
parse-fields [str ":="| Q] PQ :- 
  parse-fields Q PQ.
parse-fields [str "{|"| Q] PQ :- 
  parse-fields Q PQ.
parse-fields [str "|", str "}"] [].
parse-fields [H|Q] [H|PQ] :- coq.say H, parse-fields Q PQ.
}}.


(* Import isC. *)
Elpi check_arg C nat := {| c := 0 |}.


#[arguments(raw)] Elpi Command parse.
Elpi Accumulate lp:{{

main [const-decl Name (some BodySkel) TyWPSkel] :-
  coq.say "type given:" TyWPSkel "\nBodySkel : " BodySkel "\nName" Name.
  
main A :- coq.say "lol" A.
}}.


(* Import isC. *)
Elpi check_arg C nat := {| c := 0 |}.


Elpi check_arg Definition _ : isC Z := isC.Build Z Z.add. *) *)