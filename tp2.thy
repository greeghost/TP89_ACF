theory tp2
imports Main
begin

(* 1.1 : Construction des ensembles *)

fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "member _ [] = False" |
  "member x (t#q) = ((x = t) \<or> (member x q))"

fun isSet :: "'a list \<Rightarrow> bool" where
  "isSet [] = True"
| "isSet (t#q) = ((\<not>(member t q)) \<and> (isSet q))"

fun clean :: "'a list \<Rightarrow> 'a list" where
  "clean [] = []"
| "clean (t#q) = (if (member t q) then (clean q) else (t#(clean q)))"

lemma member_clean: "(member x l) = (member x (clean l))"
  apply (induct l)
   apply auto
  done

lemma isSet_clean: "isSet (clean l)"
  apply (induct l)
   apply simp
   using member_clean by fastforce

(* 1.2 : Suppression d'un élément *)

fun delete :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "delete x [] = []"
| "delete x (t#q) = (if (x=t) then (q) else (t#(delete x q)))"

lemma member_delete1: "(isSet l) \<longrightarrow> (\<not>(member x (delete x l)))"
  apply (induct l)
   apply auto
  done

lemma member_delete2: "(isSet l) \<longrightarrow> ((y \<noteq> x) \<longrightarrow> ((member y l) = (member y (delete x l))))"
  apply (induct l)
   apply auto
  done

(* 1.3 : Intersection *)
fun intersection :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersection [] _ = []"
| "intersection (t#q) l = (if (member t l) then (t#(intersection q l)) else (intersection q l))"

lemma member_intersection: "((member x l1) \<and> (member x l2)) = (member x (intersection l1 l2))"
  apply (induct l1)
  apply (induct l2)
  apply simp
  apply simp
  apply auto
  done

lemma isSet_intersection: "(isSet l1) \<and> (isSet l2) \<longrightarrow> (isSet (intersection l1 l2))"
  apply (induct l1)
   apply (induct l2)
    apply simp
   apply simp
  using member_intersection by force

(* 1.4 : Union *)

fun union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "union [] l = l"
| "union (t#q) l = (if (member t l) then (union q l) else (t#(union q l)))"

lemma member_union: "((member x l1) \<or> (member x l2)) = (member x (union l1 l2))"
  apply (induct l1)
   apply (induct l2)
    apply simp
   apply simp
  apply auto
  done

lemma isSet_union: "(isSet l1) \<and> (isSet l2) \<longrightarrow> (isSet (union l1 l2))"
  apply (induct l1)
   apply (induct l2)
    apply simp
   apply simp
  apply auto
  by (meson member_union)

(* 1.5 : Égalité *)

fun equal :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "equal [] l = (l = [])"
| "equal (t#q) l = ((member t l) \<and> (equal q (delete t l)))"

lemma "((isSet l1) \<and> (isSet l2)) \<longrightarrow> ((equal l1 l2) = (\<forall>x. (member x l1) = (member x l2)))"
  apply (induct l1 arbitrary: l2)
   apply (metis equal.simps(1) isSet.elims(2) tp2.member.simps(1) tp2.member.simps(2))
  apply simp
  apply (case_tac "member a l2")
   prefer 2
   apply auto[1]
  apply simp




  sorry

(* I could not prove this one so I made another one here below *)

fun cotains :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contains l [] = True"
| "contains l (t#q) = ((member t l) \<and> (contains l q))"

fun equal2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "equal2 l1 l2 = ((contains l1 l2) \<and> (contains l2 l1))"

lemma contains_member: "(contains l1 l2) = (\<forall>x. ((member x l2) \<longrightarrow> (member x l1)))"
  apply (induct l2)
  apply auto
  done

lemma "((isSet l1) \<and> (isSet l2)) \<longrightarrow> ((equal2 l1 l2) = (\<forall>x. (member x l1) = (member x l2)))"
  using contains_member by auto

end
