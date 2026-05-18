From HB Require Import structures.
From Stdlib Require Import ZArith.


(* #[verbose,alternative,local="this"] HB.interface hey.
#[alternative] HB.interface hey.
#[alternative="this"] HB.interface hey. *)
(* #[verbose] HB.interface only_verbose.
#[verbose,alternative] HB.interface verbose_alternative.
#[alternative] HB.interface only_alternative. *)
(* #[verbose,alternative,local="this"] HB.interface hey. *)


(* Interface should behave as a mixin *)
HB.interface Record isSemiGroup T := {
    op : T -> T -> T;
    opA : forall x y z, op x (op y z) = op (op x y) z
  }.

HB.structure Definition SemiGroup := {T of isSemiGroup T}.

HB.instance  Definition _ := isSemiGroup.Build Z Z.add Z.add_assoc.


(* Interface should behave as a factory *)
#[alternative] HB.interface Record isGroup T := {
    op : T -> T -> T;
    opA' : forall x y z, op (op x y) z = op x (op y z);
    e : T;
    idl' : forall x, op e x = x;
    idr : forall x, op x e = x;
    invl : forall x, exists xinv, op x xinv = e;
    invr : forall x, exists xinv, op xinv x = e; 
    default : T
}.

HB.builders Context T of isGroup T.
HB.instance Definition _ := isSemiGroup.Build T op (fun _ _ _ => eq_sym (opA' _ _ _)).
HB.end.