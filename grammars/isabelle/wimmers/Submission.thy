theory Submission
  imports Defs
begin

lemma count_append[simp]:
  "count (u @ v) c = count u c + count v c"
  by (induction u) auto

lemma L_alphabet:
  "set w \<subseteq> {a, b}" if "w \<in> L"
  using that by induction auto

lemma L_count:
  "#w\<^bsub>a\<^esub> = 2 * #w\<^bsub>b\<^esub>" if "w \<in> L"
  using that by induction auto

text \<open>First task\<close>
theorem L_sub: "L \<subseteq> M"
  using L_alphabet L_count unfolding M_def by auto

lemma L_len:
  "w = [] \<or> length w \<ge> 3" if "w \<in> L"
  using that by induction auto

lemma [simp]:
  "h (x @ y) = h x + h y"
  unfolding h_def by auto

lemma [simp]:
  "h (b # x) = h x + 2"
  unfolding h_def by auto

lemma [simp]:
  "h (a # x) = h x - 1"
  unfolding h_def by auto

lemma [simp]:
  "h (c # x) = h x" if "c \<noteq> a" "c \<noteq> b"
  using that unfolding h_def by auto

lemma [simp]:
  "h [] = 0"
  unfolding h_def by auto

text \<open>Second task\<close>
lemma h_first_zero:
  assumes "h (xs @ ys) < 0" "h xs \<ge> 0"
  shows "\<exists> as bs. ys = as @ bs \<and> h (xs @ as) = 0"
  using assms
proof (induction ys arbitrary: xs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x ys xs)
  consider "x = a" | "x = b" | "x \<noteq> a" "x \<noteq> b"
    by auto
  then show ?case
    using snoc by (cases; simp; smt append.assoc)
qed


text \<open>Essential properties of prefixes\<close>
lemma [simp]:
  "v \<prec> [] \<longleftrightarrow> False"
  unfolding prefix_def by auto

lemma prefix_Cons_conv:
  "u \<prec> x # w \<longleftrightarrow> u = [] \<or> (u = [x] \<and> w \<noteq> []) \<or> (\<exists>v. u = x # v \<and> v \<prec> w)"
  unfolding prefix_def
  apply auto
     apply (metis hd_Cons_tl hd_append2 list.sel(1) list.sel(3) tl_append2)
  apply (simp add: Cons_eq_append_conv; fail)
  done

lemma prefix_empty[simp]:
  "u \<prec> [] \<longleftrightarrow> False"
  unfolding prefix_def by auto

lemma prefix_append_conv:
  "w \<prec> u @ v \<longleftrightarrow> w \<prec> u \<or> w = u \<and> u \<noteq> [] \<and> v \<noteq> [] \<or> (\<exists> w'. w = u @ w' \<and> w' \<prec> v)"
  unfolding prefix_def by (safe, subst (asm) append_eq_append_conv2, fastforce) auto

text \<open>Third task\<close>
lemma h_2_split:
  assumes "h w = 2" "\<forall>v. v \<prec> w \<longrightarrow> h v \<noteq> 1"
  obtains x y where "h x = 0" "h y = 0" "w = x @ b # y"
proof -
  define v where "v \<equiv> ARG_MIN length v. \<exists>x. w = v @ x \<and> h v > 0"
  have "\<exists> x. w = v @ x \<and> h v > 0"
    unfolding v_def by (rule arg_min_natI[where k = w]) (auto simp: \<open>h w = 2\<close>)
  then obtain u where [simp]: "w = v @ u" and "h v > 0"
    by auto
  then have "v \<noteq> []"
    by auto
  then obtain x c where [simp]: "v = x @ [c]"
    using rev_exhaust by blast
  have *: False if "h x > 0"
  proof -
    have "length x < length v"
      by auto
    with \<open>h x > 0\<close> show False
      unfolding v_def by (simp add: arg_min_nat_le leD)
  qed
  consider "c = a" | "c = b" | "c \<noteq> a" "c \<noteq> b"
    by auto
  then have "h x = 0 \<and> c = b \<and> h u = 0"
  proof cases
    case 1
    with \<open>h v > 0\<close> show ?thesis
      using * by force
  next
    case [simp]: 2
    consider (0) "h x = 0" | (neg) "h x < 0" | (pos) "h x > 0"
      by force
    then have "h x = 0"
    proof cases
      case 0
      then show ?thesis .
    next
      case neg
      with \<open>h w = 2\<close> have "u \<noteq> []"
        by auto
      from \<open>h x < 0\<close> \<open>h v > 0\<close> have "h v = 1"
        by simp
      moreover from \<open>u \<noteq> []\<close> have "v \<prec> w"
        by (auto simp: prefix_append_conv prefix_Cons_conv)
      ultimately show ?thesis
        using assms(2) by auto
    next
      case pos
      then show ?thesis
        using * by force
    qed
    with \<open>h w = 2\<close> show ?thesis
      by auto
  next
    case 3
    with \<open>h v > 0\<close> show ?thesis
      using * by force
  qed
  then show ?thesis
    by - (rule that, auto)
qed

lemma L_rev:
  assumes "w \<in> L"
  shows "rev w \<in> L"
  using assms by induction (auto intro: L.intros)

lemma count_rev[simp]:
  "count (rev xs) x = count xs x"
  by (induction xs) auto

lemma h_rev[simp]:
  "h (rev v) = h v"
  unfolding h_def by auto

text \<open>Task 4\<close>
theorem L_sup:
  assumes h_first_zero:
    "\<And>xs ys. h (xs @ ys) < 0 \<Longrightarrow> 0 \<le> h xs \<Longrightarrow> \<exists>as bs. ys = as @ bs \<and> h (xs @ as) = 0"
  assumes h_2_split:
    "\<And>t w. h w = 2 \<Longrightarrow> \<forall>v. v \<prec> w \<longrightarrow> h v \<noteq> 1 \<Longrightarrow> (\<And>x y. h x = 0 \<Longrightarrow> h y = 0 \<Longrightarrow> w = x @ b # y \<Longrightarrow> t)
      \<Longrightarrow> t"
  assumes "h w = 0" "set w \<subseteq> {a, b}"
  shows "w \<in> L"
  using assms(3-)
proof (induction "length w" arbitrary: w rule: less_induct)
  case less
  show ?case
  proof (cases "\<exists> x y. w = x @ y \<and> x \<noteq> [] \<and> y \<noteq> [] \<and> h x = 0 \<and> h y = 0")
    case True
    then obtain x y where "w = x @ y" "x \<noteq> []" "y \<noteq> []" "h x = 0" "h y = 0"
      by auto
    with less have "x \<in> L" "y \<in> L"
      by auto
    then show ?thesis
      unfolding \<open>w = _\<close> by (rule L.intros)
  next
    case F: False
    have 1: "w \<in> L" if
      "w = b # w'" "3 \<le> length w" "h w = 0" "set w \<subseteq> {a, b}"
      and F: "\<nexists> x y. w = x @ y \<and> x \<noteq> [] \<and> y \<noteq> [] \<and> h x = 0 \<and> h y = 0"
      and IH: "\<And>w'. length w' < length w \<Longrightarrow> h w' = 0 \<Longrightarrow> set w' \<subseteq> {a, b} \<Longrightarrow> w' \<in> L"
    for w w'
    proof -
      from \<open>h w = 0\<close> have "h w' = -2"
        unfolding \<open>w = _\<close> by simp
      obtain w'' c1 c2 where "w' = w'' @ [c1, c2]"
        using \<open>length w \<ge> 3\<close> unfolding \<open>w = _\<close>
        by clarsimp
          (metis One_nat_def add.commute add.right_neutral antisym_conv
            append.assoc append_Cons append_Nil impossible_Cons
            list.size(3) list.size(4) numeral_One numeral_le_iff
            order_trans rev_exhaust semiring_norm(68) semiring_norm(83))
      note [simp] = \<open>w = _\<close> \<open>w' = _\<close>
      consider "c1 = a" "c2 = a" | "c1 = a" "c2 = b" | "c1 = b" "c2 = a" | "c1 = b" "c2 = b"
        using \<open>set w \<subseteq> _\<close> unfolding \<open>w = _\<close> \<open>w' = _\<close> by auto
      then have "c1 = a \<and> c2 = a"
      proof cases
        case 1
        then show ?thesis ..
      next
        case 2
        with h_first_zero[of "[b]" w''] obtain as bs where "w'' = as @ bs" "h ([b] @ as) = 0"
          using \<open>h w' = -2\<close> by auto
        then show ?thesis
          using F \<open>h w = 0\<close> by (auto elim: allE[of _ "b # as"])
      next
        case 3
        with h_first_zero[of "[b]" w''] obtain as bs where "w'' = as @ bs" "h ([b] @ as) = 0"
          using \<open>h w' = -2\<close> by auto
        then show ?thesis
          using F \<open>h w = 0\<close> by (auto elim: allE[of _ "b # as"])
      next
        case 4
        with h_first_zero[of "[b]" w''] obtain as bs where "w'' = as @ bs" "h ([b] @ as) = 0"
          using \<open>h w' = -2\<close> by auto
        then show ?thesis
          using F \<open>h w = 0\<close> by (auto elim: allE[of _ "b # as"])
      qed
      with \<open>h w = 0\<close> have "h w'' = 0"
        unfolding \<open>w = _\<close> \<open>w' = _\<close> by simp
      moreover have "set w'' \<subseteq> {a, b}"
        using \<open>set w \<subseteq> _\<close> unfolding \<open>w = _\<close> \<open>w' = _\<close> by simp
      ultimately have "w'' \<in> L"
        using IH unfolding \<open>w = _\<close> \<open>w' = _\<close> by simp
      then show "w \<in> L"
        unfolding \<open>w = _\<close> \<open>w' = _\<close>
        by (simp only: \<open>c1 = a \<and> c2 = a\<close>, intro L.intros(5)[of w'' "[]", simplified] L.intros(1))
    qed
    show ?thesis
    proof (cases "w = []")
      case True
      then show ?thesis
        by simp (rule L.intros)
    next
      case False
      with \<open>h w = 0\<close> \<open>set w \<subseteq> _\<close> have "3 \<le> length w"
        unfolding h_def
        apply auto
        apply (cases w, simp)
        apply (case_tac list)
         apply (auto split: if_split_asm)
           apply (case_tac lista, auto)+
        done
      then obtain c w' where "w = c # w'"
        by (cases w) auto
      with \<open>set w \<subseteq> _\<close> have "c = a \<or> c = b"
        by auto
      then show ?thesis
      proof
        assume "c = b"
        with less \<open>length w \<ge> 3\<close> F show ?thesis
          unfolding \<open>w = _\<close> by - (rule 1[of _ w'], auto)
      next
        assume "c = a"
        from \<open>h w = 0\<close> have "h w' = 1"
          unfolding \<open>w = _\<close> \<open>c = _\<close> by simp
        obtain v c1 where "w' = v @ [c1]"
          using \<open>length w \<ge> 3\<close> unfolding \<open>w = _\<close>
          by simp (metis length_0_conv not_numeral_le_zero rev_exhaust)
        note [simp] = \<open>w = _\<close> \<open>w' = _\<close> \<open>c = _\<close>
        consider (a) "c1 = a" | (b) "c1 = b"
          using \<open>set w \<subseteq> _\<close> by auto
        then show "w \<in> L"
        proof cases
          case [simp]: a
          have *: False if "h u = 1" "u \<prec> v" for u
          proof -
            from \<open>u \<prec> v\<close> obtain xs where "w = a # u @ xs @ [a]"
              unfolding prefix_def by auto
            with \<open>h u = 1\<close> F \<open>h w = 0\<close> show ?thesis
              by (auto elim: allE[of _ "a # u"])
          qed
          from \<open>h w' = 1\<close> have "h v = 2"
            by simp
          then obtain x y where "h x = 0" "h y = 0" "v = x @ b # y"
            by (rule h_2_split) (auto intro: *)
          with less have "x \<in> L" "y \<in> L"
            by auto
          then show ?thesis
            by (simp add: \<open>v = _\<close>; intro L.intros)
        next
          case b
          with less \<open>length w \<ge> 3\<close> F have "rev w \<in> L"
            apply simp
            apply (rule 1, rule HOL.refl)
                apply clarsimp+
             apply (metis append_Cons h_rev rev.simps(2) rev_append rev_eq_Cons_iff rev_is_Nil_conv)
            apply clarsimp
            done
          then show ?thesis
            by - (drule L_rev, auto)
        qed
      qed
    qed
  qed
qed

text \<open>The final theorem\<close>
corollary
  "L = M"
  using L_sub L_sup[OF h_first_zero h_2_split] unfolding h_def M_def by auto

end