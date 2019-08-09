theory Submission
imports Defs
begin


definition "number_of_true_between' x y i = foldr (\<lambda>x n. if i x then Suc n else n) [x..<y] 0"


lemma pp: "foldr (\<lambda>x n. if i x then Suc n else n) [x..<n] (Suc y) = Suc (foldr (\<lambda>x n. if i x then Suc n else n) [x..<n] y)"
  apply(induct n arbitrary: y) by auto

lemma number_of_true_between_alt:
  "number_of_true_between x y i =  foldr (\<lambda>x n. if i x then Suc n else n) [x..<y] 0 "
  unfolding number_of_true_between'_def number_of_true_between_def 
  apply(cases "x\<le>y")
  subgoal apply(induct rule: nat_induct_at_least) 
    by (auto simp:   pp)  
  subgoal by auto
  done


section \<open>Part 1 - Stuff about XOR\<close>
 
(* a hint: *)

lemma xor_shuffle: "xor a b = c \<longleftrightarrow> xor a c = b"
  apply(cases a; cases b; cases c) by auto

lemma bubble_foldr_xor:
  "xor (foldr (\<lambda>x n. xor n (f x)) xs y) z
            = foldr (\<lambda>x n. xor n (f x)) xs (xor y z)" 
  apply (induct "xs" arbitrary: y z)
  subgoal by auto
  subgoal apply simp
    apply(subst xor_assoc[symmetric]) 
    apply(subst xor_assoc[symmetric]) 
    apply(subst (3) xor_com) by simp
  done 


lemma upt_append_continuous: "x\<le>y \<Longrightarrow> [0..<x] @ [x..<y] = [0..<y]"  
  by (metis le0 le_iff_add upt_add_eq_append)


(* a partial goal *)

lemma XOR_interval: "x\<le>y \<Longrightarrow> xor (XOR 0 x i) (XOR 0 y i) = (XOR x y i)"
 
  apply(subst xor_shuffle) 
  unfolding XOR_def
  apply(subst bubble_foldr_xor)
  apply(simp only: xor_False2)
  apply(subst foldr_append[symmetric]) 
  apply(simp only: upt_append_continuous) done  

section \<open>Part 2 - number_of_true_between reduction to XOR\<close>
 
lemma foldr_xor_odd_add: "(odd z) \<longleftrightarrow> Z \<Longrightarrow> foldr (\<lambda>x n. xor n (i x)) [x..<y] Z = odd (foldr (\<lambda>x n. if i x then Suc n else n) [x..<y] z)"
proof(induct "(y-x)" arbitrary: x y z Z)
  case 0
  then show ?case by simp   
next
case (Suc n)
  hence t: "n = (y - (Suc x))" and tt: "x < y" by linarith+
  then obtain y' where y': "y= Suc y'"  
    using less_imp_Suc_add by blast  
  have ff: "x < Suc y'" using tt y' by auto
  have A: "[x..<Suc y'] = [x..<y']@[y']" using tt y'  
    by simp  
  show ?case
    unfolding y' 
    unfolding A apply (simp only: foldr_append)
    apply(subst Suc(1)[where z="(foldr (\<lambda>x n. if i x then Suc n else n) [y'] z)"])
    subgoal using t y' by auto
    subgoal using Suc(3) by (auto simp add: xor_True)
    subgoal using y' tt  by auto
    done 
qed 

lemma XOR_odd_odd: "XOR x y i = odd (number_of_true_between x y i)"
 
  unfolding XOR_def number_of_true_between_alt
  apply(rule foldr_xor_odd_add) by simp 
  

lemma reduction:
  assumes "(\<forall>x<n. si x < ei x \<and> ei x < n)"
  shows
 "correct_solution_XOR i (si,ei,n) f
      \<Longrightarrow> correct_solution i (si,ei,n) f" 
  using assms by(auto simp: correct_solution_def correct_solution_XOR_def XOR_odd_odd) 


section \<open>Solution: ALGORITHM\<close>
 
subsection \<open>my solution\<close>

definition phase0 where "phase0 = [LoadIA 0, LoadIB 0, Xor, StoreTmp 0]"  

fun phase1 :: "nat \<Rightarrow> Com list" where
  "phase1 0 = []"
| "phase1 (Suc n) = phase1 n @ [LoadIB n, Xor, StoreTmp (Suc n)]"

fun inv' where
  "inv' i (t,a,b,f) n = ( (\<forall>x\<le>n. t x = XOR 0 x i)  )"

fun inv where
  "inv i (t,a,b,f) n = ( (\<forall>x\<le>n. t x = XOR 0 x i) \<and> a= XOR 0 n i)"

lemma "inv i (t(0:=False),False,b,f) 0" 
  by auto

lemma inv_phase0: "inv i (execs i (tmp,a,b,f) phase0) 0"
  by (simp add: phase0_def)

 

lemma inv_preserve: "inv i (t,a,b,f) n
   \<Longrightarrow> inv i (execs i (t,a,b,f) [LoadIB n, Xor, StoreTmp (Suc n)]) (Suc n)"
  apply (simp only: inv.simps  execs.simps exec.simps)
  apply(simp only: XOR_Suc) by (auto simp:  XOR_Suc) 

lemma inv_preserve': "inv i s n
   \<Longrightarrow> inv i (execs i s [LoadIB n, Xor, StoreTmp (Suc n)]) (Suc n)"
  apply(cases s)
  by (simp add: XOR_Suc)

term fun_upd

lemma inv_phase1: "inv i (execs i (t(0:=False),False,b,f) (phase1 n)) n"
proof (induct n  )
  case 0
  then show ?case by simp
next
  case (Suc n)    
  show ?case
    apply(simp add: execs_append del: execs.simps fun_upd_apply) 
    apply(rule inv_preserve') using Suc . 
qed 

lemma inv_phase1': "s = (execs i (t(0:=False),False,b,f) (phase1 n)) 
  \<Longrightarrow> inv i s n" using inv_phase1 by auto

definition calc where "calc a b = [LoadTA a, LoadTB b, Xor]"

fun inv3 where "inv3 i (t,a,b,f) x y = ( a = XOR  x y i )"

 


lemma calc_correct: 
    "inv' i (t,a,b,f) n \<Longrightarrow> x < y \<Longrightarrow> y < n 
      \<Longrightarrow> inv' i (execs i (t,a,b,f) (calc x y)) n
         \<and> inv3 i (execs i (t,a,b,f) (calc x y)) x y
      "
  apply safe
  subgoal apply (simp add: calc_def) done
  apply(simp only: calc_def execs.simps exec.simps)
  apply(simp only: inv'.simps)
  apply(subst XOR_interval) apply simp
  by (simp only: inv3.simps)

lemma calc_inv': "inv' i s n \<Longrightarrow> x < y \<Longrightarrow> y < n 
      \<Longrightarrow> inv' i (execs i s (calc x y)) n"
  apply(cases s) using calc_correct  
  by simp



fun process where 
  "process _ 0 = []"
| "process (si,ei,N) (Suc n) =  process (si,ei,N) n @ calc (si n) (ei n) @ [StoreFinal n]"

fun inv4 where "inv4 i (si,ei,N) (tmp,a,b,f) (n::nat)
        = ( \<forall>x<n. f x = XOR (si x) (ei x) i )"

lemma inv4_alt: "inv4 i (si,ei,N) s n = ( \<forall>x<n. (snd (snd (snd s))) x = XOR (si x) (ei x) i )"
  by(cases s; auto)
lemma "inv4 i (si,ei,N) s 0" apply(cases s) by(simp)

lemma inv'_StoreFinal:
  "inv' i  (t,a,b,f) n  
      \<Longrightarrow> inv' i (execs i (t,a,b,f) [StoreFinal X]) n"
  by(auto)

lemma inv'_StoreFinal':
  "inv' i s n \<Longrightarrow> inv' i (execs i s [StoreFinal X]) n"
  by(  cases s; auto)



lemma assumes "\<And>n. n<N \<Longrightarrow> si n < ei n \<and> ei n < N"  "m<N"
  shows process_step:
    "inv' i (t,a,b,f) N \<Longrightarrow> inv4 i (si,ei,N) (t,a,b,f) m
      \<Longrightarrow> inv' i (execs i (t,a,b,f) (calc (si m) (ei m) @ [StoreFinal m])) N
           \<and> inv4 i (si,ei,N) (execs i (t,a,b,f) (calc (si m) (ei m) @ [StoreFinal m])) (Suc m)"
  apply(rule)
  subgoal
   apply(subst execs_append)  apply(rule inv'_StoreFinal') 
   apply(rule calc_inv')  
    subgoal by simp
    subgoal using assms by auto
    subgoal using assms by auto
    done
  apply(subst execs_append)
  apply (simp del: fun_upd_apply )
  apply(subst inv4_alt) apply(simp only: calc_def execs.simps exec.simps)
  apply(simp  )
  using assms(1)[of m] assms(2) apply(simp ) 
  apply(subst XOR_interval) apply simp apply simp done

lemma assumes "\<And>n. n<N \<Longrightarrow> si n < ei n \<and> ei n < N"  "m<N"
  shows process_step':
    "inv' i s N \<Longrightarrow> inv4 i (si,ei,N) s m
      \<Longrightarrow> inv' i (execs i s (calc (si m) (ei m) @ [StoreFinal m])) N
           \<and> inv4 i (si,ei,N) (execs i s (calc (si m) (ei m) @ [StoreFinal m])) (Suc m)"
  apply(cases s)
  apply(rule) apply safe
    subgoal apply(rule process_step[THEN conjunct1]) using assms by auto 
    subgoal apply(rule process_step[THEN conjunct2]) using assms by auto 
    done
 
lemma assumes "\<And>n. n<N \<Longrightarrow> si n < ei n \<and> ei n < N" 
  shows process_correct:
    "inv' i (t,a,b,f) N  \<Longrightarrow> m\<le>N
      \<Longrightarrow> inv' i (execs i (t,a,b,f) (process (si,ei,N) m)) N
           \<and> inv4 i (si,ei,N) (execs i (t,a,b,f) (process (si,ei,N) m)) m"
proof (induct m arbitrary: t a b f) 
  case (Suc m)
  note A= Suc(1)[THEN conjunct1]
  note B= Suc(1)[THEN conjunct2]
  show ?case 
    apply(rule)
    subgoal apply simp apply(subst execs_append) 
      apply(rule process_step'[THEN conjunct1])  
      subgoal using assms by simp
      subgoal using assms Suc by simp      
      using   A[OF  Suc(2)]  B[OF  Suc(2)] Suc(3) by auto 
    subgoal apply simp apply(subst execs_append) 
      apply(rule process_step'[THEN conjunct2]) 
      subgoal using assms by simp
      subgoal using assms Suc by simp      
      using   A[OF  Suc(2)]  B[OF  Suc(2)] Suc(3) by auto 
    done      
qed simp
    
lemma assumes "\<And>n. n<N \<Longrightarrow> si n < ei n \<and> ei n < N" 
  shows process_correct':
    "inv' i (t,a,b,f) N 
      \<Longrightarrow> inv4 i (si,ei,N) (execs i (t,a,b,f) (process (si,ei,N) N)) N"
  apply(rule process_correct[THEN conjunct2])
  using assms by auto


lemma inv_inv': "inv i s N \<Longrightarrow> inv' i s N" 
  apply (cases s) by simp 

lemma 
  plan_correct':
  assumes "\<And>n. n<N \<Longrightarrow> si n < ei n \<and> ei n < N"
  shows "inv4 i (si,ei,N) (execs i (t,a,b,f) ( (phase0 @ phase1 N) @ (process (si,ei,N) N))) N"
  apply(subst execs_append)
  apply(cases "(execs i (t, a, b, f) (phase0 @ phase1 N))")
  apply simp
  apply(rule process_correct')
  subgoal using assms by auto
  apply(rule inv_inv')
  subgoal  for t' a' b' f'
    apply(subst (asm) execs_append)   
    apply(rule inv_phase1'[where t=t and b="i 0" and f=f]) 
  unfolding phase0_def by simp  
  done

lemma length_phase1: "length (phase1 n) = 3 * n"
  apply(induct n) by simp_all

lemma length_process: "length (process I n) = 4 * n"
  apply(cases I) apply (induct n) by (auto simp: calc_def) 

lemma length_plan: "length ((phase0 @ phase1 N) @ (process i N)) = 4 + 7 * N"
  unfolding phase0_def  
  by(auto simp del: process.simps simp: length_process length_phase1)

lemma Olinear: "(\<exists>n0 c:: nat. \<forall>n\<ge>n0. 4 + 7 * n \<le> c * n)"
  apply(rule exI[where x=10])
  apply(rule exI[where x=8]) by auto

lemma Olinear2: "\<exists>n0 c. \<forall>b\<ge>n0. Suc (Suc (Suc (Suc (7 * b)))) \<le> c * b"
  apply(rule exI[where x=10])
  apply(rule exI[where x=8]) by auto



lemma inv4_correct_solution: "inv4 i (si,ei,N) s N \<Longrightarrow> correct_solution_XOR i (si,ei,N) (output s)"
  apply(cases s)
  by (simp add: output_def correct_solution_XOR_def)

lemma 
  plan_correct:
  assumes "\<And>n. n<N \<Longrightarrow> si n < ei n \<and> ei n < N"
  shows "correct_solution_XOR i (si,ei,N) (output (execs i (t,a,b,f) ( (phase0 @ phase1 N) @ (process (si,ei,N) N))))" 
  apply(rule inv4_correct_solution)
  apply(rule plan_correct') by (fact assms)

 

lemma GOAL:  
  shows "\<exists>f:: task \<Rightarrow> Com list.
      \<forall>i si ei N s. 
      (\<forall>x<N. si x < ei x \<and> ei x < N) \<longrightarrow> 
            \<comment> \<open>functional correctness\<close>
             correct_solution i (si,ei,N) (output (execs i s (f (si,ei,N))))
         \<and>
            \<comment> \<open>complexity: linear in the size of the task\<close>
             (\<exists>n0 c:: nat. \<forall>t. n0 \<le> tasksize t \<longrightarrow> length (f t) \<le> c * (tasksize t))"
   apply(rule exI[where x="\<lambda>(si,ei,N). (phase0 @ phase1 N) @ (process (si,ei,N) N)"]) 
  apply safe
  subgoal   apply simp 
    apply(rule reduction)
    subgoal by simp     
    apply(rule plan_correct[simplified] ) by blast
  subgoal  
    apply(simp add: tasksize_def phase0_def length_phase1 length_process)
      using Olinear2 by auto 
  done 




end