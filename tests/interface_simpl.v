From HB Require Import structures.


(* #[verbose,alternative,local="this"] HB.interface hey.
#[alternative] HB.interface hey.
#[alternative="this"] HB.interface hey. *)
#[verbose] HB.interface only_verbose.
#[verbose,alternative] HB.interface verbose_alternative.
#[alternative] HB.interface only_alternative.
(* #[verbose,alternative,local="this"] HB.interface hey. *)