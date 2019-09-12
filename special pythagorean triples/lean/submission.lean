-- solution by Kevin Kappelmann https://github.com/kappelmann
import .defs
import tactic.norm_num

theorem pythagorean_sum_one_thousand :
  ∃ (a b c : ℕ), pythagorean_triple a b c ∧ a + b + c = 1000 :=
by { existsi [200, 375, 425], unfold pythagorean_triple, norm_num }
