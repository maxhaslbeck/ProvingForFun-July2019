-- Solution by Chris Hughes https://github.com/ChrisHughes24
import data.zmod.basic tactic.fin_cases

theorem mod_power_five (n : ℕ) : n % 10 = (n ^ 5) % 10 :=
have h : ∀ (n : zmod 10), n = n ^ 5, from dec_trivial,
(zmod.eq_iff_modeq_nat' (show 0 < 10, from dec_trivial)).1 $
  by rw [h n, nat.cast_pow]
