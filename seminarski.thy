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

lemma[simp]: "2^(n+1) = 2*2^n"
proof(induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof-
    have "2^(Suc n + 1) = 2^(n + 2)"
      by auto
    also have "... = 2*2^(n+1)"
      using Suc
      by auto
    finally show ?case by auto
  qed
qed

lemma bernulli_inequality:
  fixes n::nat
  assumes "n >= 1" "a > -1"
  shows "(1 + a)^n \<ge> 1 + n*a"
  using assms
proof (induction n rule: nat_induct_at_least)
case base
  then show ?case
    by simp
next
case (Suc n)
  have "1 + (Suc n)*a \<le> 1 + (Suc n)*a + n*a^2"
    using `a >-1`
    by auto
  also have "... = 1 + n*a + a + n*a^2"
    by simp
  also have "... = (1+ n*a)*(1+a)"
    by (auto simp add: algebra_simps power2_eq_square)
  also have "... \<le> (1 + a)^(n) * (1 + a)"
    using Suc
    using mult_le_mono1 
    by blast
  also have "... = (1 + a)^(Suc n)"
    by auto
  finally show ?case .
qed

(* Dokazati da je broj f(n) = 2^(n+1) + 3^(2*n-1) 
 deljiv sa 7 za sve prirodne brojeve. *)
(* Zadatak je Primer 2. iz knjige Analiza sa algebrom 2 
 i u knjizi se javlja greska u dokazu.*)

lemma pomocna_deljivost_sa_7:
 assumes "n \<ge> 1"
 shows "(3::nat)^ (n * 2) = 3 * 3 ^ (n*2 - Suc 0)"
  using [[show_types]]
  using assms
  by (induction n rule: nat_induct_at_least) auto

lemma deljivost_sa_7:
  fixes n::nat
  assumes "n \<ge> 1" 
  shows "(7::nat) dvd 2^(n+1) + 3^(2*n - 1)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  thus ?case 
    by auto
next
  case (Suc n)
  have "(2::nat)^(Suc n + 1) + (3::nat)^(2*(Suc n) - 1) = 2 ^ (n + 2) + 3 ^ (2*n +1)"
    using [[show_types]]
    by auto
  also have "... = 2 * 2^(n + 1) + 3 * 3 * 3 ^(2*n - 1)"
    using [[show_types]]
    using pomocna_deljivost_sa_7
    by (smt Groups.add_ac(2) Groups.mult_ac(1) 
       One_nat_def Suc.hyps add_Suc_right mult.commute one_add_one plus_1_eq_Suc power_Suc)
  also have "... = 2 * (2^(n+1) + 3^(2*n - 1) - 3^(2*n-1)) + 9 * 3 ^ (2*n - 1)"
    by auto
  also have "... = 2 * (2^(n+1) + 3^(2*n - 1)) - 2 * 3 ^ (2*n-1) + 9 * 3 ^(2*n-1)"
    by auto
  also have "... = 2 * (2^(n+1) + 3^(2*n - 1)) + 7 * 3 ^(2*n-1)"
    by auto
  finally show ?case
    by (metis Suc.IH dvd_add dvd_add_times_triv_right_iff mult.commute mult_2)
qed

(* zadaci iz knjige *)
(* zadatak 3 *)
primrec razlomak_proizvoda_suseda :: "nat \<Rightarrow> real" where
  "razlomak_proizvoda_suseda 0 = 0"
| "razlomak_proizvoda_suseda (Suc n) = (1::real) / ( Suc n * ((Suc n) + 1)) + razlomak_proizvoda_suseda n"

value "razlomak_proizvoda_suseda 2"

lemma zbir_razlomka_proizvida_suseda: 
  fixes n::nat
  assumes "n \<ge> 1"
  shows "razlomak_proizvoda_suseda n = real(n) div (n+1)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc n)
  then show ?case 
  proof-
    have "razlomak_proizvoda_suseda (Suc n) = 
    razlomak_proizvoda_suseda n + 1/((n+1)*(n+2))"
      by auto
    also have "... = n/(n+1) + 1/((n+1)*(n+2))"
      using Suc
      by auto
    also have "... = (n^2 + 2*n + 1)/((n+1)*(n+2))"
      sorry
