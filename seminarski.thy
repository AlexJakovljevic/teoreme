theory seminarski
  imports Complex_Main
begin

primrec suma_prvih :: "nat \<Rightarrow> nat" where
"suma_prvih 0 = 0"
| "suma_prvih (Suc n) = suma_prvih n + (n+1)"

lemma prvi_stepen:
  shows "suma_prvih n = n*(n+1) div 2"
proof (induction n)
case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "suma_prvih (Suc n) = suma_prvih n + (n+1)"
      by simp
    also have "... = n*(n+1) div 2 + (n+1)"
      using Suc
      by auto
    also have "... = (n+1)*(n+2) div 2"
      by auto
    finally show ?thesis by auto
  qed
qed


primrec suma_prvih_2 :: "nat \<Rightarrow> nat" where
"suma_prvih_2 0 = 0"
| "suma_prvih_2 (Suc n) = suma_prvih_2 n + (n+1)^2"

lemma drugi_stepen:
  shows "suma_prvih_2 n = n*(n+1)*(2*n+1) div 6"
proof (induction n)
case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "suma_prvih_2 (Suc n) = suma_prvih_2 n + (n+1)^2"
      by simp
    also have "... = n*(n+1)*(2*n+1) div 6 + (n+1)^2"
      using Suc
      by auto
    also have "... = (n+1)*(n+2)*(2*n+3) div 6"
      by (auto simp add: power2_eq_square algebra_simps)
    also have "... = (n+1)*(n+2)*(2*(n+1)+1) div 6"
      by (auto simp add: algebra_simps)
    finally show ?thesis by auto
  qed
qed


primrec suma_prvih_3 :: "nat \<Rightarrow> nat" where
"suma_prvih_3 0 = 0"
| "suma_prvih_3 (Suc n) = suma_prvih_3 n + (n+1)^3"

lemma treci_stepen:
  shows "suma_prvih_3 n = n^2*(n+1)^2 div 4"
proof (induction n)
case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "suma_prvih_3 (Suc n) = suma_prvih_3 n + (n+1)^3"
      by simp
    also have "... = n^2*(n+1)^2 div 4 + (n+1)^3"
      using Suc
      by auto
    also have "... = n^2*(n+1)^2 div 4 + 4*(n+1)^3 div 4"
      by auto
    also have "... = (n+1)^2 *(n^2 + 4*(n+1)) div 4"
      by (auto simp add: algebra_simps power3_eq_cube power2_eq_square)
    also have "... = (n+1)^2 *(n+2)^2 div 4"
      by (auto simp add: algebra_simps power2_eq_square)
    finally show ?thesis by auto
  qed
qed

lemma *: "(n+1)^3 = 2*(n+1)*(suma_prvih n) + (n+1)^2" 
proof-
  have "2*(n+1)*(suma_prvih n) + (n+1)^2 = 2*(n+1)*(n*(n+1) div 2) + (n+1)^2"
    using prvi_stepen
    by auto
  also have "... = (n+1)*n*(n+1) + (n+1)^2"
    by auto
  also have "... = n*(n+1)^2 + (n+1)^2"
    by (auto simp add: algebra_simps power2_eq_square)
  also have "... = (n+1)^2*(n+1)"
    by auto
  also have "... = (n+1)^3"
    by (auto simp add: algebra_simps power2_eq_square power3_eq_cube)
  finally show ?thesis by auto
qed

lemma
  shows "(suma_prvih n)^2 = suma_prvih_3 n"
proof (induction n)
case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "(suma_prvih (Suc n))^2 = (suma_prvih n + (n+1))^2"
      by simp
    also have "... = (suma_prvih n)^2 + 2*(n+1)*(suma_prvih n) + (n+1)^2"
      by (auto simp add: algebra_simps power2_eq_square)
    also have "... =  suma_prvih_3 n +  2*(n+1)*(suma_prvih n) + (n+1)^2"
      using Suc
      by auto
    also have "... = suma_prvih_3 n + (n+1)^3"
      using *
      by auto
    also have "... = suma_prvih_3 (n+1)"
      by auto
    finally show ?thesis by auto
  qed
qed


end