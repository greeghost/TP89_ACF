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

(* Ecriture des lemmes*) 


(*Lemme 1 : toutes les transactions validées ont un montant strictement supérieur à 0*)

lemma "( assoc a (export(traiterMessageList(m_list)))) = Some(am) \<longrightarrow> (am > 0)"
  oops

(*Lemme 2 : Dans la liste des transactions validées, tout triplet (c,m,i) n'apparaît qu'une seule fois)*)

lemma "uniqueKey (export(traiterMessageList(m)))"
  oops

(*Lemme 3 : Toute transaction (même validée) peut être annulée *)


(*Lemme 4 : Toute transaction annulée l'est définitivement *)

lemma "List.member m_list (Cancel (c,m,i)) \<longrightarrow> (assoc (c,m,i) (export(traiterMessageList(m_list))) = None) "
  oops

(* Lemme 5 *)
lemma "(List.member m_list (Pay (c,m,i) amm)) \<and> (List.member m_list (Ack (c,m,i) amc)) 
\<and> (amm > 0) \<and> (amm \<ge> amc) \<and> \<not>(List.member m_list (Cancel (c,m,i)))   \<longrightarrow> (assoc (c,m,i) (export(traiterMessageList(m_list)))) = Some(am)"
  oops

(*Lemma 6*)
lemma "(assoc (c,m,i) (export(traiterMessageList(m_list)))) = Some(am) \<longrightarrow> (List.member m_list (Pay (c,m,i) amm)) \<and> (List.member m_list (Ack (c,m,i) amc)) \<and> (amm \<ge> amc)"
  oops

(*Lemma 7*)
lemma " assoc (c,m,i) (export(traiterMessageList(m_list))) = Some(am) \<and> (am \<ge> amm2) \<and> (am \<le> amc) \<longrightarrow>
export(traiterMessageList(m_list)) = export(traiterMessageList(m_list@[(Pay (c,m,i) amm2)]))
\<and> export(traiterMessageList(m_list)) = export(traiterMessageList(m_list@[(Ack (c,m,i) amc)]))"

(*Lemma 8*)
lemma ""


(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

