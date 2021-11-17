theory tp89
imports Main "~~/src/HOL/Library/Code_Target_Nat" (* pour l'export Scala *)
begin

(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

type_synonym transaction= "transid * nat"

fun id :: "message \<Rightarrow> transid" where
"id (Cancel i) = i" |
"id (Pay i _) = i" |
"id (Ack i _) = i"


fun add :: "message \<Rightarrow> message list list \<Rightarrow> message list list" where
"add x [] = [[x]]" |
"add x ([] # yss) = add x yss" |
"add x ((y # ys) # yss) = (if (id x = id y) then ((x # (y # ys)) # yss) else ((y # ys) # (add x yss)))"

fun tri_message :: "message list \<Rightarrow> message list list" where
"tri_message (x # xs) = add x (tri_message xs)" |
"tri_message [] = []"


(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

