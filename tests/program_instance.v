From HB Require Import structures.

HB.mixin Record m1 T := { default1 : T }.
HB.structure Definition s1  := { T of m1 T }.

HB.mixin Record m2 T := { default2 : T }.
HB.structure Definition s2 := { T of m1 T & m2 T }.

HB.mixin Record m3 T := { default3 : T }.
HB.structure Definition s3 := { T of m3 T }.



HB.instance Program Definition _ : m1 nat := m1.Build nat 1.
(* #[verbose] HB.instance Program Definition _ : m3 nat := m3.Build nat 3. *)
(* #[verbose,program] HB.instance Definition _ : m1 nat := m1.Build nat 1. *)


#[verbose,interactive] HB.instance Definition _ : m2 nat := m2.Build nat _.
Show.
exact 2.
(* Defined. *)
HB.endinstance.

(* #[verbose,interactive] HB.instance Definition _ : m2 nat := m2.Build nat 2. *)


(* HB.about nat. *)
(* HB.instance Definition _ : m2 nat := m2.Build nat 2. *)

(* #[verbose,interactive] HB.instance Definition _ {a:nat} : m3 nat := m3.Build nat _. *)


(* HB.about nat.
(* here it works *)
HB.saturate.
HB.about nat. all there *)

(* Check @default1 nat.
Check @default2 nat.
Check @default3 nat. *)


