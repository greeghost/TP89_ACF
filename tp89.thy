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

datatype betterNat=
  N nat
| Undeclared
(* transid, (min amm, max amc, annulé, validé) *)
type_synonym transBdd = "(transid, (betterNat * betterNat * bool * bool)) table"

fun comparison :: "betterNat \<Rightarrow> betterNat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
"comparison Undeclared _ _ = False" |
"comparison _ Undeclared _ = False" |
"comparison (N i) (N j) f = f i j"

fun id :: "message \<Rightarrow> transid" where
"id (Cancel i) = i" |
"id (Pay i _) = i" |
"id (Ack i _) = i"

fun traiterMessage :: "message \<Rightarrow> transBdd \<Rightarrow> transBdd" where
"traiterMessage (Cancel i) bdd = modify i (Undeclared, Undeclared, True, False) bdd" |
"traiterMessage (Pay i amc) bdd = (case (assoc i bdd) of None \<Rightarrow> (if (amc > 0) then modify i (Undeclared, N amc, False, False) bdd else bdd)
                                    | Some(amm, amc2, ann, val) \<Rightarrow>
                                        (if (\<not>ann \<and> \<not>val \<and> (comparison (N amc) (amc2) greater) \<and> (comparison (N amc) (N 0) greater)) 
                                            then (modify i (amm, (N amc), False, ((comparison (N amc) amm greater_eq))) bdd)
                                         else bdd))" |
"traiterMessage (Ack i amm) bdd = (case (assoc i bdd) of None \<Rightarrow> (modify i ((N amm), (N 0), False, False) bdd)
                                    | Some(amm2, amc, ann, val) \<Rightarrow>
                                        (if (\<not>ann \<and> \<not>val \<and> ((amm2 = Undeclared) \<or> \<not>(comparison (N amm) amm2 greater_eq)) \<and> ((amc = Undeclared) \<or> (comparison amc (N 0) greater)) \<and> ((amm2 = Undeclared) \<or> (comparison amm2 (N 0) greater_eq))) 
                                            then (modify i ((N amm), amc, False, ((amc = Undeclared) \<or> (comparison amc (N amm) greater_eq))) bdd) 
                                         else bdd))"

fun traiterMessageList :: "message list \<Rightarrow> transBdd" where 
"traiterMessageList [] = []" |
"traiterMessageList (m # ms) = traiterMessage m (traiterMessageList ms)"

fun export :: "transBdd \<Rightarrow> transaction list" where
"export [] = []" |
"export (v # va) = (case v of (tid, (amm, amc, False, True)) \<Rightarrow> (case (amc) of (N amcnat) \<Rightarrow> (tid, amcnat) # (export va))
                                                         | _ \<Rightarrow> export va)"

value "export(traiterMessageList([Pay (0, 0, 0) 5,  Ack (0, 0, 0) 2, Pay (0, 0, 0) 10]))"

value "export(traiterMessageList([Ack (0, 0, 0) 0, Ack (0, 0, 0) 1])) = []"
value "export(traiterMessageList([Pay (0, 0, 0) 1, Ack (0, 0, 0) 0]))"

value "export(traiterMessageList([Pay (0, 0, 0) 0, Ack (0, 0, 0) 0])) = []"
value "export(traiterMessageList([Pay (0, 0, 0) 1, Ack (0, 0, 0) 1])) = [((0, 0, 0), 1)]"

value "export(traiterMessageList([Ack (0, 0, 0) 1, Pay (0, 0, 0) 1, Ack (0, 0, 0) 1, Pay (0, 0, 0) 2])) = [((0, 0, 0), 2)]"

value "export(traiterMessageList([Pay (0, 0, 0) 5, Ack (0, 0, 0) 2, Ack (0, 0, 0) 1])) = [((0, 0, 0), 5)]"
value "export(traiterMessageList([Pay (0, 0, 0) 5, Ack (0, 0, 0) 2, Ack (0, 0, 0) 1, Cancel (0, 0, 0)])) = []"

value "export(traiterMessageList([Pay (0, 0, 0) 5, Cancel (0, 0, 0), Ack (0, 0, 0) 2])) = []"

value "export(traiterMessageList([Pay (0, 0, 0) 5, Pay (1, 1, 1) 10, Ack (0, 0, 0) 3, Cancel (0, 0, 0), Ack (1, 1, 1) 5])) = [((1, 1, 1), 10)]"

(* Ecriture des lemmes*)

lemma liste_vide: "List.member [] x = False"
  using List.member_rec(2)
  by fast

(*
lemma "(List.member (traiterMessageList m_list) (i, amm, amc, ann, True)) \<longrightarrow> amm > 0"
  apply (induct m_list)
  apply simp
  using liste_vide 
   apply fast
     apply (case_tac "traiterMessageList (a # m_list) = traiterMessage a (traiterMessageList m_list)")
   apply (case_tac a)
     

  oops
*)

(*Lemme 1 : toutes les transactions validées ont un montant strictement supérieur à 0*)
lemma "( assoc a (export(traiterMessageList(m_list)))) = Some(am) \<longrightarrow> (am > 0)"
  apply (induct m_list)
   apply auto

  oops

(*Lemme 2 : Dans la liste des transactions validées, tout triplet (c,m,i) n'apparaît qu'une seule fois)*)

lemma "uniqueKey (export(traiterMessageList(m)))"
  oops

(*Lemme 3 : Toute transaction (même validée) peut être annulée *)
lemma "assoc (c,m,i) (export(traiterMessageList(m_list@[Cancel(c,m,i)]))) = None"
  oops

(*Lemme 4 : Toute transaction annulée l'est définitivement *)
lemma "List.member m_list (Cancel (c,m,i)) \<longrightarrow> (assoc (c,m,i) (export(traiterMessageList(m_list))) = None) "
  oops

(* Lemme 5 *)
lemma "(List.member m_list (Pay (c,m,i) amc)) \<and> (List.member m_list (Ack (c,m,i) amm)) 
\<and> (amc > 0) \<and> (amc \<ge> amm) \<and> \<not>(List.member m_list (Cancel (c,m,i)))   \<longrightarrow> (assoc (c,m,i) (export(traiterMessageList(m_list)))) = Some(am)"
  oops

value "export(traiterMessageList([Pay (0, 0, 0) 2, Ack (0, 0, 0) 0]))"

(*Lemma 6*)
lemma "(assoc (c,m,i) (export(traiterMessageList(m_list)))) = Some(am) \<longrightarrow> (List.member m_list (Pay (c,m,i) amm)) \<and> (List.member m_list (Ack (c,m,i) amc)) \<and> (amm \<ge> amc)"
  oops

(*Lemma 7*)
lemma " assoc (c,m,i) (export(traiterMessageList(m_list))) = Some(am) \<and> (am \<ge> amm2) \<and> (am \<le> amc) \<longrightarrow>
export(traiterMessageList(m_list)) = export(traiterMessageList(m_list@[(Pay (c,m,i) amm2)]))
\<and> export(traiterMessageList(m_list)) = export(traiterMessageList(m_list@[(Ack (c,m,i) amc)]))"
  oops

value "traiterMessageList([Pay (0, 0, 0) 1, Ack (0, 0, 0) 1])"
value "export(traiterMessageList([Pay (0, 0, 0) 1, Ack (0, 0, 0) 1]))" 

lemma bidule_aux: "List.member (traiterMessageList m_list) (i, amm, amc, False, True) \<longrightarrow> (traiterMessageList ((Pay i x) # m_list)) = (traiterMessageList m_list)"
  apply (case_tac "List.member (traiterMessageList m_list) (i, amm, amc, False, True)")
   prefer 2
   apply simp
  apply (case_tac "assoc i (traiterMessageList m_list) = Some(amm, amc, False, True)")
  apply simp
  oops

lemma bidule: "assoc (c, m, i) (export(traiterMessageList(m_list))) = Some(am) \<longrightarrow> (\<exists> amm amc. (List.member (traiterMessageList(m_list)) ((c, m, i), amm, amc, False, True)))"
  oops

(* Lemma 8 *)
lemma Lemme8: "(assoc (c,m,i) (export(traiterMessageList(m_list))) = Some(am)) \<longrightarrow> ((assoc (c,m,i) (export(traiterMessageList((Pay (c, m, i) x ) # m_list))) = Some(am)) \<and> (assoc (c,m,i) (export(traiterMessageList((Ack (c, m, i) x ) # m_list))) = Some(am)))"
  apply (case_tac m_list)
   apply simp
  oops

(*Lemme 9*)
lemma "(assoc (c,m,i) (export(traiterMessageList(m_list))) = Some(am)) \<longrightarrow> (List.member m_list(Pay (c,m,i) am))"
  oops

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

