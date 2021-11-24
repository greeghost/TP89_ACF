theory table
imports Main
begin

(* Le type des tables d'associations (maps) *)
type_synonym ('a,'b) table= "('a * 'b) list"

datatype 'a option= Some 'a | None

(* Pour une clé k et une table t, (assoc k t) rend None si la clé k ne figure pas
   dans t et (Some v) si k est associée à v dans t *)
fun assoc:: "'a \<Rightarrow> ('a ,'b) table \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x, y) # xs)= (if x = x1 then Some(y) else (assoc x1 xs))"

(* Pour une clé k, une valeur v et une table t, (modify k v t) rend la table dans laquelle
   k est associée à v. Si l'association n'existait pas elle est crée. *)
fun modify:: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) table \<Rightarrow> ('a, 'b) table"
where
"modify x y [] = [(x, y)]" |
"modify x y ((z, u) # r) = (if x = z then (x, y) # r else ((z, u) # (modify x y r)))"

fun delete :: "'a \<Rightarrow> ('a, 'b) table \<Rightarrow> ('a, 'b) table" where
  "delete a [] = []"
| "delete a (t#q) = (if (a = fst t) then (q) else (t#(delete a q)))"

(* Toutes les clés sont uniques dans la table t *)
fun uniqueKey::"('a,'b) table \<Rightarrow> bool"
where
"uniqueKey [] = True" |
"uniqueKey ((x, _) # r) = ((assoc x r) = None \<and> uniqueKey r)"

(* pour tout prédicat p et toute liste l, (forAll p l) si tous les éléments de l satisfont p *)
fun forAll:: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where 
"forAll _ [] = True" |
"forAll p (x # r) = ((p x) \<and> (forAll p r))"

end
