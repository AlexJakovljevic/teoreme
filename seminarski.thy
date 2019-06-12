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
  thus ?case
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
  sorry
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

lemma pomocna_2_dva_na_stepen_n_na_kvadrat:
  fixes n::nat
  assumes "n \<ge> 5"
  shows "(n - 1)^2 > 2"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc n)
  have "(Suc n - 1)^2 = n^2"
    by simp
  also have "... > 2"
    using assms calculation Suc
    by (auto simp add: algebra_simps power2_eq_square)
  finally show ?case
    by auto
qed

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

end
