theory Submitted

imports Definitions

begin

lemma lemma0 [simp] : "reverse (append xs (cons x nil)) = cons x (reverse xs)"
  apply (induct xs)
   apply auto
  done

theorem goal : "reverse (reverse xs) = xs"
  apply (induct xs)
   apply auto
  done

end