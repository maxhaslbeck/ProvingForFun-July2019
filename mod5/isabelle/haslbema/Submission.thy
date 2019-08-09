 theory Submission
  imports Defs
begin

lemma modpower5: fixes n :: nat
  shows "n mod 10 = (n ^ 5) mod 10"
proof -
  have *: "m ^ 5 mod 10 = m" if "m < 10" for m :: nat
  proof -
    have "m \<in> {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}"
      using that by auto
    thus ?thesis by auto
  qed
  have "(n mod 10) ^ 5 mod 10 = n mod 10"
    by (intro *) auto
  thus ?thesis by (subst (asm) power_mod) auto
qed

end
