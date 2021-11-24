theory tp89
imports Main "~~/src/HOL/Library/Code_Target_Nat" table (* pour l'export Scala *)
begin

(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

type_synonym transid= "nat * nat * nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

type_synonym transaction= "transid * nat"

(* transid, (min amm, max amc, annulé, validé) *)
type_synonym transBdd = "(transid, (nat * nat * bool * bool)) table"

fun id :: "message \<Rightarrow> transid" where
"id (Cancel i) = i" |
"id (Pay i _) = i" |
"id (Ack i _) = i"

fun traiterMessage :: "message \<Rightarrow> transBdd \<Rightarrow> transBdd" where
"traiterMessage (Cancel i) bdd = modify i (0, 0, True, False) bdd" |
"traiterMessage (Pay i amc) bdd = (case (assoc i bdd) of None \<Rightarrow> (modify i (999999, amc, False, False) bdd)
                                    | Some(amm, amc2, ann, val) \<Rightarrow>
                                        (if (\<not>ann \<and> \<not>val \<and> (amc > amc2)) 
                                            then (modify i (amm, amc, ann, (amc \<ge> amm)) bdd) 
                                            else bdd))" |
"traiterMessage (Ack i amm) bdd = (case (assoc i bdd) of None \<Rightarrow> (modify i (amm, 0, False, False) bdd)
                                    | Some(amm2, amc, ann, val) \<Rightarrow>
                                        (if (\<not>ann \<and> \<not>val \<and> (amm < amm2)) 
                                            then (modify i (amm, amc, ann, (amc \<ge> amm)) bdd) 
                                            else bdd))"

fun traiterMessageList :: "message list \<Rightarrow> transBdd" where
"traiterMessageList [] = []" |
"traiterMessageList (m # ms) = traiterMessage m (traiterMessageList ms)"

fun export :: "transBdd \<Rightarrow> transaction list" where
"export [] = []" |
"export (v # va) = (case v of (tid, (amm, amc, False, True)) \<Rightarrow> (tid, amc) # (export va)
                                                         | _ \<Rightarrow> export va)"


(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

