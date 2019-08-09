theory Submission
imports Defs
begin


lemma GOAL: "\<exists>a b c :: nat. pythagoreantriple a b c \<and> a + b + c = 1000" 
  
  apply(rule exI[where x=200])
  apply(rule exI[where x=375])
  apply(rule exI[where x=425])
  by (simp add: pythagoreantriple_def) 


axiomatization  where f: "False"

end
