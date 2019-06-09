theory seminarski
  imports Complex_Main
begin

datatype 'a Maybe = Just 'a | Nothing

definition testx :: "nat Maybe" where
"testx = Just 4"

definition testy :: "nat Maybe" where
"testy = Nothing"


primrec fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Maybe \<Rightarrow> 'b Maybe" where
"fmap f Nothing = Nothing"
| "fmap f (Just x) = Just (f x)" 

value "fmap (\<lambda>x. x+1) testx"
value "fmap (\<lambda>x. x+1) testy"

primrec safe_head :: "'a list \<Rightarrow> 'a Maybe" where
"safe_head [] = Nothing"
| "safe_head (x#xs) = Just x"

value "safe_head [1..<4]"
value "safe_head [1..<0]"

primrec from_maybe :: "'a \<Rightarrow> 'a Maybe \<Rightarrow> 'a" where
"from_maybe x Nothing = x"
| "from_maybe _ (Just x) = x"

value "from_maybe 3 testy"
value "from_maybe 3 testx"

lemma "from_maybe y (fmap f Nothing) = y"
  by auto

lemma "from_maybe y (fmap f (Just x)) = f x"
  by auto

datatype Pair = MkPair "nat list" nat

fun fst :: "Pair \<Rightarrow> nat list" where
"fst (MkPair l _) = l"

fun snd :: "Pair \<Rightarrow> nat" where
"snd (MkPair _ x) = x"

fun partition :: "nat list \<Rightarrow> Pair" where
"partition (x # xs) = (let x1 =  (filter (\<lambda> y. y \<le> x) xs) in
 MkPair (x1 @ [x] @ (filter (\<lambda> y. y > x) xs)) (length x1))"

(*
fun quick_select :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"quick_select l k = (if k \<ge> length l then 0 else (
  let p = partition l in
  if k = snd p 
    then (fst p ! k)
  else (
      if k < snd p
      then (quick_select (take (snd p) (fst p)) k)
    else
      (quick_select (drop (snd p + 1) (fst p)) (k - snd p - 1))
  )
))"

value "quick_select [1::nat, 2, 3,4] 3"
*)

end