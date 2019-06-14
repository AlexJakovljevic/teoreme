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

thm add_divide_distrib

lemma sabiranje_razlomaka:
  fixes a::real
  fixes b::real
  fixes c::real
  shows "a/b + c/b = (a+c)/b"
  by (simp add: add_divide_distrib)

lemma zbir_razlomka_proizvoda_suseda: 
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
    also have "... =(n+2)/(n+2)* n/((n+1)) + 1/((n+1)*(n+2))"
      by auto
    also have "... =((n+2)*n)/((n+2)*(n+1)) + 1/((n+1)*(n+2))"
      by (metis (no_types, lifting) divide_divide_eq_left of_nat_mult times_divide_eq_left)
    also have "... =((n+2)*n)/((n+2)*(n+1)) + 1/((n+2)*(n+1))"
      by auto
    also have "... =(n*n+2*n)/((n+2)*(n+1)) + 1/((n+2)*(n+1))"
      by auto  
    also have "... =(n*n+2*n+1)/((n+2)*(n+1))"
      using sabiranje_razlomaka
      by (auto simp add: algebra_simps)     
    also have "... = (n^2 + 2*n + 1)/((n+1)*(n+2))"
      by (auto simp add: algebra_simps power2_eq_square)
    also have "... = (n+1)^2/((n+1)*(n+2))"
      by (auto simp add: algebra_simps power2_eq_square)
    also have "... = (n+1)/(n+2)"
      by (smt Suc.hyps divide_divide_eq_right nonzero_mult_div_cancel_left of_nat_1 of_nat_add of_nat_mono of_nat_mult power2_eq_square)
    finally show ?thesis by auto
  qed
qed


(* zadatak 4. *)

lemma deljivost_sa_19: 
  "(19::nat) dvd 7 * 5^(2*n) + 12 * 6 ^ n"
proof(induction n)
  case 0
  thus ?case
    by auto
next
  case (Suc n)
  have "(7::nat) * 5 ^ (2 * Suc n) + 12 * 6 ^ (Suc n) = 7 * 25 * 5 ^ (2 * n) + 12 * 6 * 6 ^ n"
    using [[show_types]]
    by auto
  also have "... = 7 * 25 * 5 ^ (2 * n) + 6 * (7 * 5^(2*n) + 12 * 6 ^ n - 7 * 5 ^(2*n))"
    by auto
  also have "... = 7 * 25 * 5 ^ (2 * n) + 6 * (7 * 5^(2*n) + 12 * 6 ^ n) - 6 * 7 * 5 ^(2*n)"
    by auto
  also have "... = 19 * 7 * 5 ^ (2 * n) + 6 * (7 * 5^(2*n) + 12 * 6 ^ n)"
    by auto
  finally show ?case
    by (smt Suc.IH dvd_add_left_iff dvd_trans dvd_triv_right mult.commute)
qed

(* 5. zadatak *)

primrec cetiri_n_minus_1 :: "nat \<Rightarrow> nat" where
  "cetiri_n_minus_1 0 = 1"
| "cetiri_n_minus_1 (Suc n) = (4*(Suc n) - 1) * cetiri_n_minus_1 n"

value "cetiri_n_minus_1 2"

primrec cetiri_n_plus_1 :: "nat \<Rightarrow> nat" where
  "cetiri_n_plus_1 0 = 1"
| "cetiri_n_plus_1 (Suc n) = (4*(Suc n) + 1) * cetiri_n_plus_1 n"


lemma poredjenje_razlomaka:
  fixes a::real
  fixes b::real
  fixes c::real
  assumes "a > c" "a > 0" "b > 0"
  shows "sqrt(a/b) > sqrt(c/b)"
  using assms
  by (simp add: divide_strict_right_mono)

find_theorems "(_*_)^_ = _^_*_^_"

find_theorems "_ < _ \<Longrightarrow> _/_ < _/_"

find_theorems "_<_ \<Longrightarrow> _*_ < _*_"

find_theorems "_^2 \<ge> 0"

(*Opet slabo radi sa razlomcima. Ova lema iznad je iskoriscena i radi deo posla.*)
lemma
  fixes n::nat
  assumes "n \<ge> 1"
  shows "real(cetiri_n_minus_1 n)^2 < (3::real) * real(cetiri_n_plus_1 n)^2 / real(4*n + 3)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  thus ?case
    by auto
next
  case (Suc n)
  then show ?case
    sorry
(*
  proof-
 have "real(cetiri_n_minus_1 (Suc n))^2 / real(cetiri_n_plus_1 (Suc n))^2 =
       real((4*(Suc n) - 1) * cetiri_n_minus_1 n)^2 / real((4*(Suc n) + 1) * cetiri_n_plus_1 n)^2"
   by auto
  also have "... = real((4*(Suc n) - 1)^2 * (cetiri_n_minus_1 n)^2) / real((4*(Suc n) + 1) * cetiri_n_plus_1 n)^2"
    by (auto simp add:power_mult_distrib)
  also have "... = real((4*(Suc n) - 1)^2) * real((cetiri_n_minus_1 n))^2 / real((4*(Suc n) + 1) * cetiri_n_plus_1 n)^2"
    by auto
  also have "... < real((4*(Suc n) - 1)^2) * ((3::real) * real(cetiri_n_plus_1 n)^2 / real(4*n + 3)) / real((4*(Suc n) + 1) * cetiri_n_plus_1 n)^2"
    using Suc
     using  zero_le_power2
    using divide_strict_right_mono
    using mult_strict_left_mono
    sledgehammer
    by (smt One_nat_def Suc_pred add_is_0 divide_eq_0_iff mult_eq_0_iff of_nat_0_less_iff of_nat_le_0_iff one_eq_mult_iff one_less_numeral_iff power2_eq_square rel_simps(9) zero_less_Suc zero_less_diff)

 qed
*)
(*
  have "real(cetiri_n_minus_1 (Suc n))^2 / real(cetiri_n_plus_1 (Suc n))^2 =
       (real(cetiri_n_minus_1 n)^2 * ((4*(Suc n) - 1))^2) / (real(cetiri_n_plus_1 n)^2 * ((4*(Suc n) +1))^2)"
    by (auto simp add: algebra_simps power2_eq_square)
  also have "... < (3::real) / real(4 *n + 3) * (4*n + 3)^2/(4*n + 5)^2"
    using Suc
    using poredjenje_razlomaka
    by (auto simp add: algebra_simps power2_eq_square)
  *)
  (*
  have " (3::real) / (4*n + 7) > (1::real) / (4*n + 7)"
    using poredjenje_razlomaka
    by auto
  also have "... > (4 * n + 3) / (4*n + 5)^2"
  *)
  
qed

(* primer 5. *)

primrec faktorijel :: "nat \<Rightarrow> nat" where
  "faktorijel 0 = 1"
| "faktorijel (Suc n) = Suc n * faktorijel n"

lemma fact2_veci_2naN:
  fixes n::nat
  assumes "n \<ge> 4"
  shows "faktorijel n > (2::nat)^n"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  thus ?case
    by (simp add: numeral.simps(2))
next
  case (Suc n)
  have "2^(Suc n) = 2 * 2^n"
    by simp
  also have "... < (Suc n) * 2^n"
    using Suc 
    by auto
  also have "... \<le> (Suc n) * faktorijel n"
    using Suc less_imp_le_nat mult_le_mono2
    by blast
  also have "... = faktorijel (n + 1)"
    by auto
  finally show ?case by simp
qed

(* primer 6 *)
(* ovo je kao slozeniji primer gde se koristi cinjenica da 12 i 7 dele, 
otuda deli i 84. Ako hoces, mozes probati da ga uradis. 
Meni je islo dok nije poceo da baguje u drugom delu. *)
lemma deljivost_sa_84:
  assumes "n \<ge> 1"
  shows "(84::nat) dvd 4^(2*n) - 3^(2*n) - 7"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case
    by auto
next
  case (Suc n)
  thus ?case
 (* ovo prolazi  have "nat(4)^(2*Suc n) - 3 ^(2 * Suc n) - 7 = 4^2 * 4 ^(2*n) - 3^2 * 3 ^(2*n) - 7"
                  by auto*)
  sorry
qed

(* zadatak 6. *)
(* Dokazati da vazi 2^n > n^2 za n \<ge> 5*)

lemma pomocna_1_dva_na_stepen_n_na_kvadrat:
  fixes n::nat
  assumes "n \<ge> 5"
  shows "n^2 > 2*n + 1"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc n)
    have *:"(Suc n)^2 = n^2 + 2*n + 1"
      by (simp add: power2_eq_square)
    also have "... > 2*(n + 1) + 1 "
      using assms Suc 
      by auto
    finally show ?case
      by simp 
qed

lemma dva_na_stepen_n_na_kvadrat:
  fixes n::nat
  assumes "n\<ge>5"
  shows "2^n > n^2"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case
    by auto
next
  case (Suc n)
  have "(n + 1)^2 = n^2 + 2*n + 1"
    by (simp add: power2_eq_square)
  also have "... < 2*n^2"
    using pomocna_1_dva_na_stepen_n_na_kvadrat Suc
    by auto
  also have "... < 2*2^n"
    using Suc
    by auto
  also have "... = 2^(n+1)"
    by auto
  finally show ?case by simp
qed

lemma n_n_kvadrat:
  fixes n::nat
  assumes "n\<ge>2"
  shows "n < n^2"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "Suc n = n+1"
      by auto
    also have "... < n^2 + 1"
      using Suc
      by auto
    also have "... < n^2 + 1 + 2*n"
      using Suc.hyps by linarith
    also have "... = (n+1)^2"
      by (auto simp add: power2_eq_square)
    finally show ?thesis by auto
  qed
qed

lemma
  fixes n::nat
  assumes "n \<ge> 3"
  shows "4^(n-1) > n^2"
  using assms
proof (induction n rule: nat_induct_at_least)
case base
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "(Suc n)^2 = n^2 + 2*n + 1"
      by (auto simp add: power2_eq_square)
    also  have "... = n^2 + n + n + 1"
      by auto
    also have "... < n^2 + n^2 + n +1"
      using assms
      by (metis Suc.hyps Suc_le_mono add_less_mono1 eval_nat_numeral(3) le_SucI n_n_kvadrat nat_add_left_cancel_less)
    also have "... < n^2 + n^2 + n^2 +1"
      using assms
      by (metis Suc.hyps Suc_le_mono add_less_mono1 eval_nat_numeral(3) le_SucI n_n_kvadrat nat_add_left_cancel_less)
    also have "... < n^2 + n^2 + n^2 +n"
      using assms
      using Suc.hyps by linarith
    also have "... < n^2 + n^2 + n^2 +n^2"
      using assms
      by (metis Suc.hyps Suc_le_mono  eval_nat_numeral(3) le_SucI n_n_kvadrat nat_add_left_cancel_less)
    also have "... = 4*n^2"
      by auto
    also have "... <4*4^(n-1)"
      using Suc
      by auto
    also have "... = 4^n"
      by (metis One_nat_def Suc_pred \<open>n\<^sup>2 + n\<^sup>2 + n\<^sup>2 + 1 < n\<^sup>2 + n\<^sup>2 + n\<^sup>2 + n\<close> add_Suc add_Suc_shift less_SucI nat_add_left_cancel_less power_Suc)
    finally show ?thesis by auto
  qed
qed

primrec zbir_stepena :: "nat \<Rightarrow> real \<Rightarrow> real" where
"zbir_stepena 0 x = 1"
|"zbir_stepena (Suc n) x = zbir_stepena n x + x^(n+1)"

value "zbir_stepena 2 2"

lemma
  fixes x::real
  fixes n::nat
  assumes "x \<noteq> 1"
  shows "zbir_stepena n x = (x^(n+1)-1)/(x-1)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "zbir_stepena (Suc n) x = zbir_stepena n x + x^(n+1)"
      by simp
    also have "... =  (x^(n+1)-1)/(x-1) +  x^(n+1)"
      using Suc
      by auto
    also have "... =  (x^(n+1)-1)/(x-1) + (x-1)*x^(n+1)/(x-1)"
      using assms
      by simp
    also have "... = (x^(n+1)-1 +(x-1)*x^(n+1))/(x-1)"
      using sabiranje_razlomaka by blast
    also have "... = (x^(n+1)-1 + x*x^(n+1)-x^(n+1))/(x-1)"
      by (auto simp add : field_simps)
    also have "... = (-1 + x*x^(n+1))/(x-1)"
      by auto
    also have "... = (x^(n+2)-1)/(x-1)"
      by auto
    finally show ?thesis by auto
  qed
qed

(* zadatak 16. a) *)
(* (1 - 1/4) * (1-1/9)*...*(1 - 1/n^2) = (n + 1)/2*n za n \<ge> 2 *)

(* zadatak 18. a) *)

lemma deljivost_sa_3:
  fixes n::nat
  shows "(3::nat) dvd 5^n + 2^(n+1)"
proof(induction n)
  case 0
  thus ?case
    by (simp add: numeral_3_eq_3)
next
  case (Suc n)
  have "5^(Suc n) + 2^(Suc n + 1) = 5 * 5^n + 2*2^( n + 1)"
      by simp
    also have "... = (5::nat) * (5^n + 2^(n+1) - 2^(n+1)) + 2 * 2^(n + 1)"
      using Suc
      by simp
    also have "... = 5 * (5^n + 2^(n+1)) - 5*2^(n+1) + 2 * 2^(n+1)"
      by simp
    also have "... = 5 * (5^n + 2^(n+1)) - 3*2^(n+1)"
      by simp
    finally show ?case
      using Suc
      by (auto simp only: dvdI dvd_diff_nat dvd_trans dvd_triv_right)
qed
(* zadatak 18. b) *)
lemma deljivost_sa_59:
  fixes n::nat
  shows "(59::nat) dvd 5^(n+2) + 26 * 5^n + 8^(2*n+1)"
proof (induction n)
  case 0
  thus ?case
    by simp
next
  case (Suc n)
  have "(5::nat)^(Suc n+2) + 26 * 5^(Suc n) + 8^(2*(Suc n)+1) =
        5 * 5^(n + 2) + 26 * 5 * 5^n + 8^2 * 8^(2*n + 1)"
    by simp
  also have "... = 5 * 5^(n + 2) + 
            5 *(5^(n+2) + 26 * 5^n + 8^(2*n+1) - 5^(n+2)- 8^(2*n+1))
            + 8^2 * 8^(2*n + 1)"
    by simp
  also have "... = 5 * 5^(n + 2) + 5 *(5^(n+2) + 26 * 5^n + 8^(2*n+1)) -
             5*5^(n+2)- 5*8^(2*n+1)
            + 8^2 * 8^(2*n + 1)"
    by simp
  also have "... = 5 *(5^(n+2) + 26 * 5^n + 8^(2*n+1)) + 59* 8^(2*n+1)"
    by simp
  finally show ?case
    using Suc
    by (auto simp only: add_2_eq_Suc' dvd_add_left_iff dvd_triv_left dvd_triv_right gcd_nat.trans)
qed
(* zadatak 18. c) *)
lemma deljivost_sa_133: 
  fixes n::nat
  shows "(133::nat) dvd 11^(n+2)+ 12^(2*n+1)"
proof(induction n)
  case 0
  thus ?case
    by simp
next
  case (Suc n)
  have "(11::nat)^(Suc n + 2) + 12^(2*(Suc n) + 1) = 11 * 11^(n + 2) + 12^2 * 12^(2*n+1)"
    by simp
  also have "... = 11 * (11^(n+2)+ 12^(2*n+1) - 12^(2*n+1))+ 12^2 * 12^(2*n+1)"
    by simp
  also have "... = 11 * (11^(n+2)+ 12^(2*n+1)) + 133 * 12^(2*n+1)"
    by simp
  finally show ?case
    using Suc
    by (auto simp only: add_2_eq_Suc' dvd_add_left_iff dvd_triv_left dvd_triv_right gcd_nat.trans)
qed

(* zadatak 18. g) *)
(* 11 | 30^n + 4^n * (3^n - 2^n) - 1 *)

(* n! < n^(n-1) *)
thm Suc_mult_less_cancel1
thm power_eq_if

primrec n_na_m :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "n_na_m n 0 = n"
| "n_na_m n (Suc m) = n + n_na_m n m" 


thm power_decreasing
thm power_Suc
thm power_Suc2
thm power_Suc_le_self
thm power_add
thm power_Suc_less_one
thm power_add_numeral
thm power_dict
thm power_diff

find_theorems "_ < _ \<Longrightarrow> _^_ < _^_"
thm power_less_imp_less_base
thm power_strict_mono

lemma n_faktorijel_n_n_minus_jedan_pomocna:
  fixes n::nat
  assumes "n \<ge> 2"
  shows "(n+1)^(n-1) > n^(n-1)"
  using assms
  by (auto simp add:power_strict_mono)

lemma n_faktorijel_n_n_minus_jedan:
  fixes n::nat
  assumes "n \<ge> 3"
  shows "faktorijel n < n^(n-1)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case
    by (simp add: numeral_3_eq_3)
next
  case (Suc n)
  have "faktorijel (Suc n) = Suc n * faktorijel n"
    by (simp only: faktorijel.simps(2))
  also have "... < (n + 1) * n^(n - 1)"
    using Suc Suc_mult_less_cancel1
    by auto
  also have "... \<le> (n + 1)*(n + 1)^(n - 1)"  
    using Suc n_faktorijel_n_n_minus_jedan_pomocna
    by (metis Suc_eq_plus1 Suc_mult_less_cancel1 add.commute eval_nat_numeral(3) le_SucI less_imp_le_nat nat_add_left_cancel_le)
  also have "... = (n + 1)^n"
    by (metis Suc(1) add_leD1 not_one_le_zero numeral_3_eq_3 plus_1_eq_Suc power_eq_if)
  finally show ?case by simp
qed


(* Knjiga Nejednakosti DMS strana 43 *)
primrec suma_levo :: "nat \<Rightarrow> real" where
"suma_levo 0 = 0"
| "suma_levo (Suc n) = suma_levo n + 1/(1+2*n) + 1/(2+2*n) - 1/(1+n)"

value "suma_levo 2"

(* pomocna tvrdjenja *)
lemma pom:
  fixes n::nat
  shows "1/(2*n+1) - 1/(2*n+2) \<ge> 0"
  by (auto simp add : field_simps)

lemma pom2:
  fixes n::nat
  shows "1/real(2*n+2) - 1/real(n+1) = - 1/real(2*n+2)"
proof-
  have "1/real(2*n+2) - 1/real(n+1) = 1/real(2*n+2)/((n+1)/(n+1)) - 1/real(n+1)"
    by auto
  also have "1/real(2*n+2) - 1/real(n+1) = 1*real(n+1)/(real(2*n+2)*(n+1)) - 1/real(n+1)"
    by auto
  also have "... = real(n+1)/(real(2*n+2)*(n+1)) - 1/real(n+1)/(real(2*n+2)/(2*n+2))"
    by auto
  also have  "... = real(n+1)/(real(2*n+2)*(n+1)) - real(2*n+2)/(real(n+1)*(2*n+2))"
    by auto
  also have  "... = real(n+1)/(real(n+1)*(2*n+2)) - real(2*n+2)/(real(n+1)*(2*n+2))"
    by auto
  also have "... =  (real(n+1)-real(2*n+2))/(real(n+1)*(2*n+2))"
    by (smt sabiranje_razlomaka)
  also have "... = -real(n+1)/(real(1+n)*real(2+2*n))"
    by auto
  also have "... = -1/real(2+2*n)"
    using field_simps
    by (smt \<open>1 / real (2 * n + 2) - 1 / real (n + 1) = 1 * real (n + 1) / (real (2 * n + 2) * real (n + 1)) - 1 / real (n + 1)\<close> divide_minus_left)
  finally show ?thesis by auto
qed

(* tvrdjenje u zadatku *)
lemma 
  fixes n::nat
  assumes "n\<ge>1"
  shows "suma_levo n \<ge> 1/2"
  using assms
proof (induction n rule:nat_induct_at_least)
case base
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof-
    have "1/2 \<le> 1/2 + 1/(2*n+1) - 1/(2*n+2)"
      using pom
      by smt
    also have "... =1/2 + 1/(2*n+1) + 1/(2*n+2) - 1/(n+1)"
      using pom2
      by auto
    also have "... \<le> suma_levo n  + 1/(2*n+1) + 1/(2*n+2) - 1/(n+1)"
      using Suc
      by auto
    also have "... = suma_levo (Suc n)"
      by auto
    finally show ?thesis by auto
  qed
qed

(* Zadatak 16. b)*)
(*
primrec proizvod_zad16 :: "nat \<Rightarrow> real" where
  "proizvod_zad16 0 = 1"
| "proizvod_zad16 (Suc n) = proizvod_zad16 n * ( 1 - 4/(2*n + 1)^2) "

lemma prosirivanje_razlomka_zad16:
  fixes b::real
  fixes c::real
  assumes "b \<noteq> 0"
  shows "1 - c/b = b/b - c/b"
  using assms
  by (simp add: diff_divide_distrib)


lemma oduzimanje_razlomka:
  fixes a b c::nat
  assumes "b \<noteq> 0"
  shows "a/b - c/b = (real(a) - (c))/b"
  using assms
  by (simp add: diff_divide_distrib)

value "proizvod_zad16 2"
lemma proizvod_zad16_lm:
  fixes n::nat
  assumes "n \<ge> 1"
  shows "proizvod_zad16 n = (1 + 2*n)/(1 - 2*n)"
proof(induction n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have "proizvod_zad16 (Suc n) = proizvod_zad16 n * ( 1 - 4/(2*n + 1)^2)"
    by auto
  also have "... = proizvod_zad16 n * (1 - 4/(4*n^2 + 4*n +1))"
    by (auto simp add: power2_eq_square)
  also have "... = proizvod_zad16 n * ((4*n^2 + 4*n +1)/(4*n^2 + 4*n +1) - 4/(4*n^2 + 4*n +1))"
    by (metis Suc_eq_plus1 Suc_mult_cancel1 add_diff_cancel_left' diff_zero mult.commute
        mult_zero_right n_not_Suc_n nat_mult_1 of_nat_eq_0_iff  prosirivanje_razlomka_zad16)
  also have "... = proizvod_zad16 n * ((4*n^2 + 4*n + 1) - real(4))/(4*n^2 + 4*n +1)"
    using oduzimanje_razlomka Suc
    by (metis (mono_tags, hide_lams) Suc_1 Suc_eq_plus1
        diff_divide_distrib distrib_left of_nat_numeral 
        semiring_normalization_rules(24) times_divide_eq_right)
  also have "... =  proizvod_zad16 n * ((4*n^2 + 4*n - nat(3))/(4*n^2 + 4*n +1))"
    using Suc assms
    sledgehammer
    by auto
  qed
*)

(*
(* da se brojevi oblika 2^2^n + 1 (n = 2, 3 , . . . ) završavaju cifrom 7 *)
find_theorems "_ dvd _ \<longrightarrow> _ dvd _"
thm power2_eq_square

lemma a_mod_b_n:
  fixes a::nat
  assumes "a \<ge> 2" "2^2^a mod (10::nat) = (6::nat)"
  shows "2^2^a^2 mod 10 = (6::nat)"
  sorry

lemma mod_div_veza:
  fixes a b c::nat
  assumes "a mod b = c"
  shows "b dvd (a - c)"
  using assms
  using dvd_minus_mod by blast

lemma dva_na_dva_na_n_cifra:
  fixes n::nat
  assumes "n \<ge> 2"
  shows " (2^2^n + 1) mod (10::nat) = (7::nat)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc n)
  have "(2::nat)^2^(n+1) + 1 = 2^(2^n * 2) + 1"
    by simp
  also have*: "... = 2^2^n * 2^2^n + 1"
    by (simp add: power2_eq_square power_mult)
  also have "... = (2^2^n)^2 + 1"
    using *
    by (simp add: power_mult)
  finally show ?case
    using a_mod_b_n assms
    sledgehammer
  qed
*)
end
