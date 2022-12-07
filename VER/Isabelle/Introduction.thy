theory Introduction
  imports Main

begin

term "True"

term "False"

term "0::int"

term "(+)::nat \<Rightarrow> (nat \<Rightarrow> nat)"

term "fst::(nat * int) \<Rightarrow> nat"

term "snd::(nat * int) \<Rightarrow> int"

term "[a,b,c]"


term "append::nat list \<Rightarrow> nat list \<Rightarrow> nat list"

term "[a,b] @ [c]"

term "hd [a,b]"

term "tl [a,b]"

term "{}"

term "{a::nat}"

term "union"

term "s \<union> t"

term "0::nat"

term "Suc 0"

term "Suc (Suc 0)"

term "[]"
term "Cons a []"
term "a # []"

term " a # b # c #[]"

term "a \<noteq> b"

term "a \<or> b"

term "a \<and> b"

term "a \<longrightarrow> b" (*Hol implication*)



end