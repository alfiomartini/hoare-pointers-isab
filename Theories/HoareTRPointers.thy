theory HoareTRPointers 

imports Main "HOL-Hoare.HeapSyntax"

begin

section \<open>Preliminary Example : List Reversal\<close>

lemma hd_tl:"xs \<noteq> [] \<Longrightarrow> xs = hd xs # tl xs"
  by simp 


fun tail_rev::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"tail_rev [] acc = acc" |
"tail_rev (x#xs) acc = tail_rev xs (x # acc)"

lemma tail_rev:"\<forall>ys. tail_rev xs ys = rev xs @ ys"
apply (induction xs)
apply (auto)
done

lemma "tail_rev xs [] = rev xs" by (simp add:tail_rev)


lemma hd_tl_app:"xs \<noteq> [] \<Longrightarrow> xs = [hd xs] @ tl xs"
  by simp
 
lemma impRev: "VARS (acc::'a list) (xs::'a list)
 {xs=X}
 acc:=[];
 WHILE xs \<noteq> []
 INV {rev(xs)@acc = rev(X)}
 DO acc := (hd xs # acc); xs := tl xs OD
 {acc=rev(X)}"
apply (vcg) 
  apply (simp)
  using hd_tl_app apply (force)
  apply (auto)
done

lemma impRev_isar: "VARS acc x
 {x=X}  acc:=[];
 WHILE x \<noteq> []  INV {rev(x)@acc = rev(X)}
 DO acc := (hd x # acc); x := tl x OD
 {acc=rev(X)}"
proof (vcg)
  fix acc x
  assume ass:"rev x @ acc = rev X \<and> x \<noteq> []"
  show "rev (tl x) @ hd x # acc = rev X"
    proof - 
      from ass obtain 1:"rev x @ acc = rev X" 
        and 2:" x\<noteq>[]" by blast
      from 2 have "x = hd x # tl x"  by simp
      from 1 and this  have 3:"rev x = rev (hd x # tl x)" by simp
      have "rev (hd x # tl x) = rev (tl x) @ [hd x]" by simp
      from 3 and this have "rev x =  rev (tl x) @ [hd x]" by simp
      from this and 1 show ?thesis by simp
    qed 
qed (auto)



section \<open>Pointers and Linked Lists in Isabelle \<close>

\<comment>\<open> example:  0 \<mapsto> 1 \<mapsto> 2  \<mapsto> Null \<close>
definition next_n::"nat \<Rightarrow>nat ref" where
   "next_n\<equiv>(\<lambda>n. Null)(0:=Ref 1,1:=Ref(2),2:=Null)"
definition name::"nat \<Rightarrow> string"  where 
   "name \<equiv> (\<lambda>n .'''')(0:=''Anne'',1:=''Paul'',2:=''July'')"
definition age::"nat \<Rightarrow> int"  where 
   "age \<equiv> (\<lambda>n . 0)(0:=19,1:=21,2:=17)"
definition p::"nat ref" where "p\<equiv> Ref 0"
definition tmp::"nat ref" where "tmp\<equiv>p"

lemma "p^.name = ''Anne''" by (simp add:p_def name_def)
lemma "p^.next_n^.next_n=Ref 2" by (simp add:p_def next_n_def) 
lemma "p^.next_n^.name = ''Paul''" 
    by (simp add:p_def name_def next_n_def)
lemma "p^.next_n^.age = 21" by (simp add:p_def next_n_def age_def)
lemma "tmp^.age = 19" unfolding  p_def tmp_def age_def by simp

lemma "VARS (next_n::nat \<Rightarrow> nat ref) 
        (age::nat \<Rightarrow> int) (p::nat ref)
        (tmp::nat ref)
{p= Ref 0 \<and> x=Ref 0 \<and> y= Ref 1 \<and> z = Ref 2}
x^.age := 19;x^.next_n := y;
y^.age := 21;y^.next_n := z;
z^.age := 17;z^.next_n := Null;tmp := x
{p^.next_n^.age = 21 \<and> tmp^.age = 19}"
  apply (vcg)
  apply (simp)
done 

lemma "next_n 1 = Ref 2" by (simp add:next_n_def) 
lemma "Ref 1^. next_n = Ref 2" by (simp add:next_n_def)
lemma "(next_n (Ref 2 \<rightarrow> Ref 4)) 2 = Ref 4" by (simp add:next_n_def)
lemma "(next_n (Ref 2 \<rightarrow> Ref 4)) 0 = Ref 1" by (simp add:next_n_def)
lemma "(next_n (2 := Ref 4)) 0  = Ref 1" by (simp add:next_n_def)
lemma "(next_n 4 = next_n 7) =  True" by (simp add:next_n_def)
lemma "(Ref 4^.next_n = Ref 7^.next_n) = True" by (simp add:next_n_def)
  
section \<open>Aliasing\<close>

text "An example due to Suzuki:"
\<comment> \<open>w0 \<rightarrow> x0 \<rightarrow> y0 \<rightarrow> z0\<close>
\<comment> \<open> function update solves the problem 
    of aliasing using the tricks for arrays \<close>

lemma "VARS (v::'a \<Rightarrow> int) (next::'a \<Rightarrow> 'a ref)
  {w = Ref w0 & x = Ref x0 & y = Ref y0 & z = Ref z0 &
   distinct[w0,x0,y0,z0]}
  w^.v := 1; w^.next := x;
  x^.v := 2; x^.next := y;
  y^.v := 3; y^.next := z;
  z^.v := 4; x^.next := z
\<comment> \<open>w0 \<rightarrow> x0 \<rightarrow>  z0 \<and> y0 \<rightarrow> z0 \<close>
  {w^.next^.next^.v = 4 \<and> y^.next^.v=4}"
apply (vcg)
apply (auto)
done

\<comment> \<open>w0 \<rightarrow> x0 \<rightarrow> y0\<close>
lemma "VARS (v::'a \<Rightarrow> int) 
       (next::'a \<Rightarrow> 'a ref) (tmp::'a ref)
  {w = Ref w0 & x = Ref x0 & y = Ref y0 \<and>
   distinct[w0,x0,y0]}
  w^.v := 1; w^.next := x;
  x^.v := 2; x^.next := y;
  y^.v := 3; tmp := y
\<comment> \<open>w0 \<rightarrow> x0 \<rightarrow>  z0 \<and> y0 \<rightarrow> z0 \<close>
  {w^.next^.next^.v = 3 \<and> tmp^.v=3}"
apply (vcg)
apply (simp)
done


\<comment> \<open>{i=j \<and> a[i] = 3} a[i] = 4 {a[j] = 4}\<close>

lemma "VARS (a::nat \<Rightarrow> int)
{i=j \<and> a(i) = 3} 
a := a(i:=4)
{a(j) = 4}" 
apply (vcg)
apply (simp)
done 


section \<open> Simple Examples of Pointer Programs \<close>

\<comment> \<open>deletion at the front of a linked list without ghost variables\<close>

lemma "VARS (next::'a \<Rightarrow> 'a ref) (p::'a ref) (q::'a ref)
{List next p Ps \<and> p \<noteq> Null}
  q := p;p := p^.next
{\<exists> a as. List next p as \<and> q = Ref a \<and> a # as = Ps}"
apply (vcg)
apply (auto)
done

lemma "VARS (next::'a \<Rightarrow> 'a ref) (p::'a ref) (q::'a ref) 
{List next p Ps \<and> p \<noteq> Null}
  q := p;p := p^.next
{\<exists> a as. List next p as \<and> q = Ref a \<and> a # as = Ps}"
proof (vcg)
  fix "next" p q val 
  assume ass:"List next p Ps \<and> p \<noteq> Null " 
  from this obtain a as where "Ps = a # as" and 
   "p = Ref a" and "List next (next a) as" by auto
  from this show "\<exists>a as. List next (next (addr p)) as 
      \<and>  p = Ref a \<and> a # as = Ps" by simp
qed

 
\<comment> \<open>deletion at the front of a linked list
      with ghost variables\<close>
lemma "VARS (next::'a \<Rightarrow> 'a ref) (p::'a ref)
      (ps::'a list) (q::'a ref) (val::'a)
{List next p Ps \<and> p \<noteq> Null}
  ps := Ps;q := p; p := p^.next;  
  ps := tl ps; val := addr q
{List next p ps  \<and> val # ps = Ps}"
  apply (vcg)
  apply (auto)
done

 

\<comment> \<open>deletion at the front - example\<close>
lemma "VARS next p ps  q val
{ p \<noteq> Null \<and> List next p Ps \<and> Ps = [0,1,2]}
  ps := Ps; q:= p; p := p^.next; 
  ps:= tl ps ;val := addr q
{List next p ps \<and> val#ps =[0,1,2]}"
apply (vcg) 
apply (auto)
done

 
\<comment> \<open>number of nodes in a linked list - 
     without ghost variables\<close>
lemma "VARS (next::'a \<Rightarrow> 'a ref) (p::'a ref)
         (ps::'a list) (k::nat) j
{List next p Ps \<and> j = length Ps}
k:=0;
WHILE p \<noteq> Null
INV {\<exists> as. List next p as \<and> length as + k = j}
DO p := p^.next; k := k+1 OD 
{j = k \<and> List next p []}"
apply (vcg)
  apply (fastforce)
  apply (fastforce)
  apply (fastforce)
done


section \<open>Case Study : In-Place List Reversal\<close>

lemma in_place_rev: "VARS p q tmp next
{List next p Ps}
q := Null;
WHILE p \<noteq> Null
  INV {\<exists> ps qs. List next p ps \<and> List next q qs 
       \<and> set ps \<inter> set qs = {}
       \<and>  rev ps @ qs = rev Ps}
DO
  tmp := p; p:= p^.next;
  tmp^.next := q; q:=tmp
OD
{List next q (rev Ps)}"
apply (vcg)
  \<comment> \<open>List is a function ; [] is neutral\<close>
  apply (simp)
  apply (clarsimp)
     apply (smt  List_hd_not_in_tl 
            disjoint_iff_not_equal notin_List_update 
            set_ConsD)
  apply (auto)
done
 
value "(next(u\<rightarrow>v)) (addr u)"

\<comment> \<open> Yes!\<close>
lemma "List next q qs \<Longrightarrow> u = Ref a \<Longrightarrow> a \<notin> set qs \<Longrightarrow> 
        List (next(u\<rightarrow>q)) u (a # qs)" by simp

lemma in_place_rev_draft: "VARS p q tmp next
{List next p Ps}
q := Null;
WHILE p \<noteq> Null
  INV {\<exists> ps qs. List next p ps \<and> List next q qs 
       \<and> set ps \<inter> set qs = {}
       \<and>  rev ps @ qs = rev Ps}
DO
  tmp := p; p:= p^.next;
  tmp^.next := q; q:=tmp
OD
{List next q (rev Ps)}"
proof (vcg)
  fix p q tmp "next" 
  assume  ass:
          "(\<exists>ps qs. List next p ps \<and>
           List next q qs \<and>
           set ps \<inter> set qs = {} \<and>
           rev ps @ qs = rev Ps) \<and> p \<noteq> Null" 
  show "\<exists>ps qs.
          List (next(p \<rightarrow> q)) (next (addr p)) ps \<and>
          List (next(p \<rightarrow> q)) p qs \<and>
          set ps \<inter> set qs = {} \<and>
          rev ps @ qs = rev Ps" sorry
qed (auto)

lemma in_place_rev_isar: "VARS p q tmp next
{List next p Ps}
q := Null;
WHILE p \<noteq> Null
  INV {\<exists> ps qs. List next p ps \<and> List next q qs 
       \<and> set ps \<inter> set qs = {}
       \<and>  rev ps @ qs = rev Ps}
DO
  tmp := p; p:= p^.next;
  tmp^.next := q; q:=tmp
OD
{List next q (rev Ps)}"
proof (vcg)
  fix p q tmp "next" 
  assume  ass:
          "(\<exists>ps qs. List next p ps \<and>
           List next q qs \<and>
           set ps \<inter> set qs = {} \<and>
           rev ps @ qs = rev Ps) \<and> p \<noteq> Null" 
  show "\<exists>ps qs.
          List (next(p \<rightarrow> q)) (next (addr p)) ps \<and>
          List (next(p \<rightarrow> q)) p qs \<and>
          set ps \<inter> set qs = {} \<and>
          rev ps @ qs = rev Ps" 
      proof -
        from ass obtain ps qs where 
          a1:"List next p ps" and a2 :"List next q qs" 
          and a3: "set ps \<inter> set qs = {}" and 
          a4: "rev ps @ qs = rev Ps" and a5:"p \<noteq> Null" 
              by blast
         from a5 and a1 obtain a as where a6:"p=Ref a" 
          and a7:"ps = a # as"  and 
          a8:"List next (next a) as" and a9:"a = addr p"  by auto
        from a8 a6 have "a \<notin> set as" by simp
        from this and  a8 
          have "List (next(a :=  q)) (next a) as" by simp
        from this and  a9 
          have c1:"List (next(p \<rightarrow> q)) (next (addr p)) as" by simp
        from a7 and a3 have a10:"a \<notin> set qs" by simp
        from this and a2 and a6 have 
           c2:"List (next(p \<rightarrow> q)) p (a#qs)" by simp
        from a7 and a3 and a10 and \<open>a\<notin> set as\<close>
            have c3: "set as \<inter> set (a#qs) = {}" by simp
        from a4 and a7 
          have "rev as @ (a # qs) = rev Ps" by simp
        from this and c1 and c2 and c3 show ?thesis by blast
      qed
qed (auto)

lemma in_place_rev_isar2: "VARS p q tmp next
{List next p Ps}
q := Null;
WHILE p \<noteq> Null
  INV {\<exists> ps qs. List next p ps \<and> List next q qs 
       \<and> set ps \<inter> set qs = {}
       \<and>  rev ps @ qs = rev Ps}
DO
  tmp := p; p:= p^.next;
  tmp^.next := q; q:=tmp
OD
{List next q (rev Ps)}"
proof (vcg)
  fix p q tmp "next" 
  assume  ass:
          "(\<exists>ps qs. List next p ps \<and>
           List next q qs \<and>
           set ps \<inter> set qs = {} \<and>
           rev ps @ qs = rev Ps) \<and> p \<noteq> Null" 
  show "\<exists>ps qs.
          List (next(p \<rightarrow> q)) (next (addr p)) ps \<and>
          List (next(p \<rightarrow> q)) p qs \<and>
          set ps \<inter> set qs = {} \<and>
          rev ps @ qs = rev Ps" 
      proof -
        \<comment> \<open> breaking assumptions into pieces \<close>
        from ass obtain ps qs where 
          a1:"List next p ps" and a2 :"List next q qs" 
          and a3: "set ps \<inter> set qs = {}" and 
          a4: "rev ps @ qs = rev Ps" and a5:"p \<noteq> Null" 
              by blast
         from a5 and a1 obtain a as where "p=Ref a" 
          and "ps = a # as"  and 
          "List next (next a) as" and "a = addr p"  by auto
        from \<open>List next (next a) as\<close>  
              have "a \<notin> set as" by simp
        from this and  \<open>List next (next a) as\<close>
          have "List (next(a :=  q)) (next a) as" by simp
        from this and  \<open>a = addr p\<close>
          have c1:"List (next(p \<rightarrow> q)) (next (addr p)) as" by simp
        from \<open>ps = a # as\<close> and a3 have "a \<notin> set qs" by simp
        from this and a2 and \<open>p=Ref a\<close> have 
           c2:"List (next(p \<rightarrow> q)) p (a#qs)" by simp
        from \<open>ps = a # as\<close> and a3 and \<open>a \<notin> set qs\<close> and \<open>a\<notin> set as\<close>
            have c3: "set as \<inter> set (a#qs) = {}" by simp
        from a4 and \<open>ps = a # as\<close> 
          have "rev as @ (a # qs) = rev Ps" by simp
        from this and c1 and c2 and c3 show ?thesis by blast
      qed

qed (auto)

lemma in_place_rev_ghost: "VARS p ps qs q tmp next
{List next p Ps \<and> ps = Ps}
q := Null; qs := [];
WHILE p \<noteq> Null
  INV {List next p ps \<and> List next q qs 
       \<and> set ps \<inter> set qs = {}
       \<and>  rev ps @ qs = rev Ps}
DO
  tmp := p; p:= p^.next;
  tmp^.next := q; q:=tmp;
  qs := hd ps # qs;ps := tl ps 
OD
{List next q (rev Ps)}"
apply (vcg)
  apply (simp)
  apply (clarsimp)
  apply (auto)
done

section \<open> Case Study: In-Place Cyclic Lists Reversal \<close>

\<comment>\<open> 1 \<mapsto> 2 \<mapsto> 3 \<mapsto> 1 \<mapsto> 2 \<mapsto> 3 \<dots> \<close>

definition  nciclic::"nat \<Rightarrow> nat ref" where
   "nciclic\<equiv>(\<lambda>n. Null)(1:=Ref 2,2:=Ref(3),3:=Ref(1))"

lemma "Path nciclic (Ref 1) [] (Ref 1)" 
     by (simp add:nciclic_def)

lemma "Path nciclic (Ref 1) [1] (Ref 2)" 
     by (simp add:nciclic_def)
lemma "Path nciclic (Ref 1) [1,2,3] (Ref 1)" by 
          (simp add:nciclic_def)
lemma "Path nciclic (Ref 1) [1,2,3,1,2] (Ref 3)" by 
       (simp add:nciclic_def)

\<comment> \<open>Why nciclic is not needed?\<close>
lemma "\<not>(distPath nciclic (Ref 1) [1,2,3,1,2] (Ref 3))"
  by (simp add: distPath_def) 
   
definition cyclic2 where 
  "cyclic2 \<equiv> (\<lambda>n. Null) (1:= Ref 1)" 

lemma "Path cyclic2 (Ref 1) [1] (Ref 1)" by (simp add:cyclic2_def)
lemma "distPath cyclic2 (Ref 1) [1] (Ref 1)" 
   by (simp add:cyclic2_def distPath_def)
lemma "Path cyclic2 (Ref 1) [1,1,1,1] (Ref 1)" 
    by (simp add:cyclic2_def)

lemma circular_list_rev_I:
  "VARS next root p q tmp
  {root = Ref r \<and> distPath next root (r#Ps) root}
  p := root; q := root^.next;
  WHILE q \<noteq> root
  INV {\<exists> ps qs. distPath next p ps root 
               \<and> distPath next q qs root \<and> 
                root = Ref r \<and> r \<notin> set Ps  \<and> 
                set ps \<inter> set qs = {} \<and> 
                 Ps = (rev ps) @ qs  }
  DO tmp := q; q := q^.next; tmp^.next := p; p:=tmp OD;
  root^.next := p
  { root = Ref r \<and> distPath next root (r#rev Ps) root}"
apply (simp only:distPath_def)
apply vcg
  apply (fastforce)
  prefer 2 
  apply (fastforce)
  apply (clarsimp)
    apply (drule (2) neq_dP)
    apply clarsimp
    apply(rule_tac x="a # ps" in exI)
    apply clarsimp
done

lemma circular_rev_draft:
  "VARS next root p q tmp
  {root = Ref r \<and> distPath next root (r#Ps) root}
  p := root; q := root^.next;
  WHILE q \<noteq> root
  INV {\<exists> ps qs. distPath next p ps root 
               \<and> distPath next q qs root \<and> 
                root = Ref r \<and> r \<notin> set Ps  \<and> 
                set ps \<inter> set qs = {} \<and> 
                 Ps = (rev ps) @ qs  }
  DO tmp := q; q := q^.next; tmp^.next := p; p:=tmp OD;
  root^.next := p
  { root = Ref r \<and> distPath next root (r#rev Ps) root}"
unfolding distPath_def
proof (vcg)
  fix "next" and  root and p q tmp 
  assume ass:
   "(\<exists>ps qs.(Path next p ps root \<and> distinct ps) \<and>
     (Path next q qs root \<and> distinct qs) \<and>
     root = Ref r \<and> r \<notin> set Ps \<and>
     set ps \<inter> set qs = {} \<and> Ps = rev ps @ qs) \<and>
       q \<noteq> root"
  show "\<exists>ps qs. (Path (next(q \<rightarrow> p)) q ps root
        \<and> distinct ps)
        \<and> (Path (next(q \<rightarrow> p)) (next (addr q)) qs root 
        \<and> distinct qs) \<and> root = Ref r \<and>  r \<notin> set Ps 
        \<and>  set ps \<inter> set qs = {} \<and> Ps = rev ps @ qs" sorry
qed (force)+

lemma cyclic_list_rev_I':
"VARS next root p q tmp
{root = Ref r \<and> distPath next root (r#Ps) root}
p := root; q := root^.next;
WHILE q \<noteq> root
INV {\<exists> ps qs. distPath next p ps root 
             \<and> distPath next q qs root \<and> 
              root = Ref r \<and> r \<notin> set Ps  \<and> 
              set ps \<inter> set qs = {} \<and> 
               Ps = (rev ps) @ qs  }
DO tmp := q; q := q^.next; tmp^.next := p; p:=tmp OD;
root^.next := p
{ root = Ref r \<and> distPath next root (r#rev Ps) root}"
unfolding distPath_def
proof (vcg)
fix "next" root p q tmp
assume "root = Ref r \<and>
       Path next root (r # Ps) root \<and>
         distinct (r # Ps)"
  from this have "Path next (next r) Ps root" 
   and "distinct Ps" and "r\<notin> set Ps" 
   and "Path next root [] root" and "root = Ref r" by auto
  from this show  
    "\<exists>ps qs. (Path next root ps root \<and> distinct ps) 
     \<and> (Path next (next (addr root)) qs root \<and>
     distinct qs) \<and> root = Ref r \<and>  r \<notin> set Ps \<and>
      set ps \<inter> set qs = {} \<and> Ps = rev ps @ qs" by force
next 
  fix "next" root p q tmp
  assume "(\<exists>ps qs. (Path next p ps root \<and> distinct ps) \<and>
           (Path next q qs root \<and> distinct qs) \<and>
           root = Ref r \<and> r \<notin> set Ps \<and>
           set ps \<inter> set qs = {} \<and>
           Ps = rev ps @ qs) \<and> \<not> q \<noteq> root" 
  from this obtain ps1 qs1 where  "q = root"  and  
    "Path next q qs1 root" and "qs1 = []"  and  
    "Ps = rev ps1"  and pr:"Path next p ps1 root" 
    and "distinct ps1"  and "r \<notin> set Ps" and 
    "root = Ref r"  by auto
  from \<open>Ps = rev ps1\<close> and \<open>r \<notin> set Ps\<close> 
    have "rev Ps = ps1" and "r \<notin> set (rev Ps)"  by auto
  from this and pr and \<open>root = Ref r\<close> and \<open>q = root\<close>
    and \<open>distinct ps1\<close> 
  show "root = Ref r 
          \<and> Path (next(root \<rightarrow> p)) root (r# rev Ps) root
          \<and> distinct (r# rev Ps) " by simp
  
next  
  fix "next" and  root and p q tmp 
  assume ass:
   "(\<exists>ps qs.(Path next p ps root \<and> distinct ps) \<and>
     (Path next q qs root \<and> distinct qs) \<and>
     root = Ref r \<and> r \<notin> set Ps \<and>
     set ps \<inter> set qs = {} \<and> Ps = rev ps @ qs) \<and>
       q \<noteq> root"
  show "\<exists>ps qs. (Path (next(q \<rightarrow> p)) q ps root
        \<and> distinct ps)
        \<and> (Path (next(q \<rightarrow> p)) (next (addr q)) qs root 
        \<and> distinct qs) \<and> root = Ref r \<and>  r \<notin> set Ps 
        \<and>  set ps \<inter> set qs = {} \<and> Ps = rev ps @ qs"
  proof - 
    from ass have "root = Ref r" and "r \<notin> set Ps" 
      and "q \<noteq> root" by auto
    from ass obtain ps1 qs1 where 
      pr:"Path next p ps1 root" and dps:"distinct ps1" and
      qr:"Path next q qs1 root" and dqs:"distinct qs1" and 
      setI:"set ps1 \<inter> set qs1 = {}" and 
        psr: "Ps = rev ps1 @ qs1"  by blast 
    from qr and \<open>q\<noteq>root\<close> and dqs  obtain x bs where 
     "q=Ref x" and "qs1= x#bs" 
     "Path next (next x) bs root"
      by (metis Path.simps(2) neq_dP) 
    from setI and \<open>qs1 = x#bs\<close> have "x \<notin> set ps1" by simp
    from this and pr and \<open>q=Ref x\<close> and dps have 
      c1:"Path (next(q\<rightarrow>p)) q (x#ps1) root \<and> distinct (x#ps1)" 
        by simp
    from dqs and \<open>qs1 = x#bs\<close> have "x \<notin> set bs" by simp
    from this and  qr and \<open>qs1 = x#bs\<close> and dqs and \<open>q=Ref x\<close> 
      have c2:"Path (next(q \<rightarrow> p)) (next (addr q)) bs root \<and>
             distinct bs" by simp
    from setI and \<open>qs1 = x#bs\<close> and dps and dqs 
      have c3:"set (x#ps1) \<inter> set bs = {}" by simp
    from psr and \<open>qs1 = x#bs\<close> 
      have c4:"rev (x#ps1) @ bs = rev ps1 @ qs1" by simp
    from this c1 and c2 and c3 and c4 and psr
      and \<open>root = Ref r\<close> and \<open>r \<notin> set Ps\<close> 
    show ?thesis  by metis
   qed
qed

section \<open> Other Examples \<close>
 
\<comment> \<open> reverses a list Ps onto a list Qs \<close>
\<comment> \<open> uses ghost variables \<close>
lemma lrev_ghost:"VARS next p ps q qs r
  {List next p Ps \<and> List next q Qs \<and> set Ps \<inter> set Qs = {} \<and>
   ps = Ps \<and> qs = Qs}
  WHILE p \<noteq> Null
  INV {List next p ps \<and> List next q qs \<and> set ps \<inter> set qs = {} \<and>
       rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := p^.next; r^.next := q; q := r;
     qs := (hd ps) # qs; ps := tl ps OD
  {List next q (rev Ps @ Qs)}"
apply (vcg)
apply (simp)
apply (fastforce)
apply (auto)
done

\<comment> \<open> an concrete example \<close>
lemma "VARS (next::int \<Rightarrow> int ref) (p::int ref) 
              (ps::int list) (q::int ref) (qs::int list) 
               (r::int ref)
{List next p Ps \<and> List next q Qs
  \<and> set Ps \<inter> set Qs = {} \<and>
   ps = Ps \<and> qs = Qs  
   \<and> Ps =[1,2,3] \<and> Qs=[]}
  WHILE p \<noteq> Null
  INV {List next p ps \<and> List next q qs 
        \<and> set ps \<inter> set qs = {} \<and>
       rev ps @ qs = rev Ps @ Qs \<and> 
       rev ps @ qs = [3,2,1]}
  DO  r := p; p := p^.next; 
      r^.next := q; q := r;
      qs := (hd ps) # qs; ps := tl ps OD
{List next q (rev Ps@ Qs) \<and> qs = [3,2,1]}"
apply (vcg)
apply auto[1]
apply (fastforce)
apply (fastforce)
done

 \<comment> \<open> Allocation of nodes \<close>

definition new :: "'a set \<Rightarrow> 'a"
  where "new A = (SOME a. a \<notin> A)"


lemma new_notin:
 "\<lbrakk> ~finite(UNIV::'a set); finite(A::'a set); B \<subseteq> A \<rbrakk> \<Longrightarrow> new (A) \<notin> B"
apply(unfold new_def)
apply(rule someI2_ex)
apply (fast intro:ex_new_if_finite)
apply (fast)
done

lemma "~finite(UNIV::'a set) \<Longrightarrow>
  VARS (xs::'a list) (elem::'a \<Rightarrow> 'a) (next::'a \<Rightarrow>'a ref) 
      (alloc::'a list) (p::'a ref) (q::'a ref)
  {Xs = xs \<and> p = (Null::'a ref)}
  WHILE xs \<noteq> []
  INV {islist next p \<and> set(list next p) \<subseteq> set alloc \<and>
       map elem (rev(list next p)) @ xs = Xs}
  DO q := Ref(new(set alloc)); alloc := (addr q)#alloc;
     q^.next := p; q^.elem := hd xs; xs := tl xs; p := q
  OD
  {islist next p \<and> map elem (rev(list next p)) = Xs}"
apply vcg_simp
 apply (clarsimp simp: subset_insert_iff neq_Nil_conv fun_upd_apply
        new_notin)
apply fastforce
done

 \<comment> \<open> Exercises \<close>
lemma len_butlast:"xs\<noteq> [] \<Longrightarrow> 
   length (butlast xs) + 1 = length xs" by simp

lemma list_ptr: 
  "List next pt1 xs \<Longrightarrow> List next pt2 xs \<Longrightarrow> pt1 = pt2"
by (metis List_def List_distinct List_unique Path.simps(1)
       last_snoc neq_dP rotate1.simps(2))

lemma "List next ptr ps \<Longrightarrow> ptr\<noteq>Null \<Longrightarrow> ps \<noteq> []" by auto

lemma "List next ptr ps \<Longrightarrow> distinct ps" by simp

\<comment> \<open>insertion at the beginning of the list\<close>

\<comment> \<open>deletion at the end of a linked list\<close>

lemma "List (next(h:=Null)) (Ref h) [h]" by simp
lemma "Path next Null [] Null" by simp
lemma "ps \<noteq> [] \<and> distinct ps  \<Longrightarrow> 
  List (next(last ps:=Null)) (Ref (hd ps)) ps" oops
lemma "distPath next Null [] Null" by (simp add:distPath_def)
lemma "distPath next ptr [] ptr  \<Longrightarrow> ptr = Null \<Longrightarrow>
       List next ptr []" by simp 
lemma "distPath next ptr [1,2] q \<Longrightarrow> next 2 = q" by (simp add:distPath_def)
lemma "distPath next ptr [1,2] q  \<Longrightarrow>
   List (next(2:=Null)) ptr [1,2]" by (simp add:distPath_def)
lemma "distPath next ptr [1,2] q \<Longrightarrow> ptr = Ref 1 \<and> next 1 = Ref 2
 \<and> next 2 = q"  by (simp add:distPath_def)
lemma "distPath next ptr [1,2] q \<Longrightarrow> heap = next(2:=Null) 
\<Longrightarrow> heap 2 = Null"  by (simp add:distPath_def)
lemma "distPath next ptr [1,2] q \<Longrightarrow> heap = next(2:=Null) \<Longrightarrow> Path heap ptr 
[1,2] Null"  by (simp add:distPath_def)
lemma "distPath next ptr [1,2] Null \<Longrightarrow> List next ptr [1,2]" 
by (simp add:distPath_def)
lemma "butlast [1,2,3] = [1,2]" by simp
lemma "butlast [1] = []" by simp

lemma "VARS p next q tmp  ps qs
{List next p Ps  \<and> p \<noteq> Null}
IF p^.next = Null
  \<comment> \<open>Ps has exactly one element\<close>
  THEN p:= Null;ps:=[];qs:=Ps
ELSE
  \<comment> \<open>Ps has at least two elements \<close>
  tmp := p; q:= p^.next;
  ps :=[hd Ps]; qs := tl Ps;
  WHILE q^.next \<noteq> Null 
  INV  {p \<noteq> Null \<and> List next p Ps 
        \<and> List next q qs 
        \<and> List (next(last ps := Null)) p ps
        \<and> ps @ qs = Ps 
        \<and> set ps \<inter> set qs = {}
        \<and> next (last ps) = q
        \<and> last ps = addr tmp
       \<comment> \<open> \<and> next (addr tmp) = q\<close>
        \<and> ps \<noteq> [] \<and> qs \<noteq> []
       }
  DO
     tmp := q; 
     ps := ps @ [hd qs];
     q:= q^.next;
     qs := tl qs
  OD;
  tmp^.next := Null
FI
{
 (List next p ps \<and> Ps = ps @ [last Ps])}"
apply (vcg)
    apply (clarsimp)
      using List_def apply fastforce
    apply (intro conjI)
      apply (simp_all)
      apply (metis List_def Path.simps(2) addr.simps 
            list.collapse)
      apply (metis List_app List_def Path.simps(2) 
             Path_is_List disjoint_iff_not_equal 
             hd_in_set list.collapse)
      apply (metis List_distinct disjoint_iff_not_equal 
           distinct.simps(2) hd_Cons_tl list.set_sel(2))
      apply (metis List_def Path.simps(2) addr.simps 
             list.collapse)
      apply (metis List_def Path.simps(2) addr.simps 
              list.collapse)
      apply (metis List_def Path.simps(1) Path.simps(2) 
           addr.simps list.collapse ref.distinct(1))
   apply (intro conjI)
      apply auto[1]
      apply (metis List_def Path.simps(2) addr.simps 
       last_snoc list.exhaust ref.distinct(1)) 
done
      

lemma "VARS p next q tmp  ps qs
{List next p Ps  \<and> p \<noteq> Null}
IF p^.next = Null
  \<comment> \<open>Ps has exactly one element\<close>
  THEN p:= Null;ps:=[];qs:=Ps
ELSE
  \<comment> \<open>Ps has at least two elements \<close>
  tmp := p; q:= p^.next;
  ps :=[hd Ps]; qs := tl Ps;
  WHILE q^.next \<noteq> Null 
  INV  {p \<noteq> Null \<and> List next p Ps 
        \<and> List next q qs 
        \<and> List (next(last ps := Null)) p ps
        \<and> ps @ qs = Ps 
        \<and> set ps \<inter> set qs = {}
        \<and> next (last ps) = q
        \<and> last ps = addr tmp
       \<comment> \<open> \<and> next (addr tmp) = q\<close>
        \<and> ps \<noteq> [] \<and> qs \<noteq> []
       }
  DO
     tmp := q; 
     ps := ps @ [hd qs];
     q:= q^.next;
     qs := tl qs
  OD;
  tmp^.next := Null
FI
{
 (List next p ps \<and> Ps = ps @ [last Ps])}"
apply (vcg_simp)
   apply (clarify)
     apply (metis List_Ref List_def List_hd_not_in_tl 
         List_unique Path.simps(1) addr.simps last.simps 
         list.distinct(1) list.sel(1) list.sel(3))
     apply (intro conjI)
       apply (metis List_def Path.simps(2) addr.simps 
          list.collapse)
       apply (metis List_app List_def Path.simps(2) 
         Path_is_List disjoint_iff_not_equal hd_in_set 
         list.collapse)
       apply (metis List_distinct distinct.simps(2) 
          hd_Cons_tl)
       apply (simp add: disjoint_iff_not_equal list.set_sel(2))
       apply (metis List_def Path.simps(2) addr.simps 
         list.collapse)
       apply (metis List_def Path.simps(2) addr.simps 
         list.collapse)
       apply  (metis List_def Path.simps(1) Path.simps(2) 
          addr.simps list.collapse ref.distinct(1))
     apply (metis (no_types, hide_lams) List_unique 
         Path.simps(1) Path_is_List addr.simps 
         append.left_neutral empty_iff empty_set 
         fun_upd_triv last_appendR last_in_set 
         not_Ref_eq self_append_conv set_ConsD)
done
  
lemma "VARS p next q tmp  ps qs
{List next p Ps  \<and> p \<noteq> Null}
IF p^.next = Null
  \<comment> \<open>Ps has exactly one element\<close>
  THEN p:= Null;ps:=[];qs:=Ps
ELSE
  \<comment> \<open>Ps has at least two elements \<close>
  tmp := p; q:= p^.next;
  ps :=[hd Ps]; qs := tl Ps;
  WHILE q^.next \<noteq> Null 
  INV  {p \<noteq> Null \<and> List next p Ps 
        \<and> List next q qs 
        \<and> List (next(last ps := Null)) p ps
        \<and> ps @ qs = Ps 
        \<and> set ps \<inter> set qs = {}
        \<and> next (last ps) = q
        \<and> last ps = addr tmp
       \<comment> \<open> \<and> next (addr tmp) = q\<close>
        \<and> ps \<noteq> [] \<and> qs \<noteq> []
       }
  DO
     tmp := q; 
     ps := ps @ [hd qs];
     q:= q^.next;
     qs := tl qs
  OD;
  tmp^.next := Null
FI
{\<exists> a as. List next p as \<and> as @ [a] = Ps}"
apply (vcg)
   apply (intro conjI)
      apply auto[1]
      apply (clarsimp)
          apply (metis List_Ref List_hd_not_in_tl 
             list.set_intros(1) list.set_intros(2))
   apply (intro conjI)
      apply (simp_all)
      apply (metis List_def Path.simps(2) addr.simps 
         list.collapse)
      apply (metis List_app List_def Path.simps(2) 
         Path_is_List disjoint_iff_not_equal hd_in_set 
         list.collapse)
      apply (metis List_distinct disjoint_iff_not_equal 
         distinct.simps(2) hd_Cons_tl list.set_sel(2))
      apply (metis List_def Path.simps(2) addr.simps 
         list.collapse)
      apply (metis List_def Path.simps(2) addr.simps 
         list.collapse)
      apply (metis List_Ref List_def Path.simps(2) 
         addr.simps list.collapse list.distinct(1))
  by (metis List_unique Path.simps(1) Path_is_List 
      addr.simps append.left_neutral empty_iff empty_set 
       fun_upd_triv not_Ref_eq self_append_conv) 
 
lemma "VARS p next q tmp  ps qs
{List next p Ps  \<and> p \<noteq> Null}
IF p^.next = Null
  \<comment> \<open>Ps has exactly one element\<close>
  THEN p:= Null;ps:=[];qs:=Ps
ELSE
  \<comment> \<open>Ps has at least two elements \<close>
  tmp := p; q:= p^.next;
  ps :=[hd Ps]; qs := tl Ps;
  WHILE q^.next \<noteq> Null 
  INV  {p \<noteq> Null \<and> List next p Ps 
        \<and> List next q qs 
        \<and> List (next(last ps := Null)) p ps
        \<and> ps @ qs = Ps 
        \<and> set ps \<inter> set qs = {}
        \<and> next (last ps) = q
        \<and> last ps = addr tmp
       \<comment> \<open> \<and> next (addr tmp) = q\<close>
        \<and> ps \<noteq> [] \<and> qs \<noteq> []
       }
  DO
     tmp := q; 
     ps := ps @ [hd qs];
     q:= q^.next;
     qs := tl qs
  OD;
  tmp^.next := Null
FI
{\<exists> a as. List next p as \<and> as @ [a] = Ps}"
apply (vcg_simp) 
apply (intro conjI)
    apply (metis List_def List_unique Path.simps(1) 
         Path.simps(2) addr.simps)
    apply (metis List_Ref List_hd_not_in_tl addr.simps 
       hd_Cons_tl list.discI list.inject)
apply (intro conjI)
      apply (metis List_def Path.simps(2) addr.simps 
      list.collapse)
      apply (metis List_app List_def Path.simps(2) 
           Path_is_List disjoint_iff_not_equal hd_in_set 
          list.collapse)
      apply (metis List_distinct distinct.simps(2) hd_Cons_tl)
      apply (simp add: disjoint_iff_not_equal list.set_sel(2))
      apply (metis List_def Path.simps(2) addr.simps 
          list.collapse)
      apply (metis List_def Path.simps(2) addr.simps 
        list.collapse)
      apply (metis List_def Path.simps(1) Path.simps(2) 
        addr.simps list.collapse ref.distinct(1))   
apply  (metis List_unique Path.simps(1) Path_is_List 
       addr.simps append.left_neutral empty_iff empty_set 
       fun_upd_triv not_Ref_eq self_append_conv)
done

abbreviation inv_del where 
"inv_del heap head q tp ps qs xs \<equiv>
  p \<noteq> Null \<and> List heap head xs 
        \<and> List heap q qs 
        \<and> List (heap(last ps := Null)) head ps
        \<and> ps @ qs =xs 
        \<and> set ps \<inter> set qs = {}
        \<and> heap (last ps) = q
        \<and> last ps = addr tp
        \<and> ps \<noteq> [] \<and> qs \<noteq> []"

abbreviation inv_del_end where 
"inv_del_end \<equiv> True"

    lemma "VARS p next q tmp  ps qs
    {List next p Ps  \<and> p \<noteq> Null}
    IF p^.next = Null
      \<comment> \<open>Ps has exactly one element\<close>
      THEN p:= Null;ps:=[];qs:=Ps
    ELSE
      \<comment> \<open>Ps has at least two elements \<close>
      tmp := p; q:= p^.next;
      ps :=[hd Ps]; qs := tl Ps;
      WHILE q^.next \<noteq> Null 
      INV  {inv_del_end}
      DO
         tmp := q; ps := ps @ [hd qs];
         q:= q^.next;qs := tl qs
      OD;
      tmp^.next := Null
    FI
    {\<exists> a as. List next p as \<and> as @ [a] = Ps}"
oops

lemma "VARS p next q tmp  ps qs
{List next p Ps  \<and> p \<noteq> Null}
IF p^.next = Null
  \<comment> \<open>Ps has exactly one element\<close>
  THEN p:= Null;ps:=[];qs:=Ps
ELSE
  \<comment> \<open>Ps has at least two elements \<close>
  tmp := p; q:= p^.next;
  ps :=[hd Ps]; qs := tl Ps;
  WHILE q^.next \<noteq> Null 
  INV  {p \<noteq> Null \<and> List next p Ps 
        \<and> List next q qs 
        \<and> List (next(last ps := Null)) p ps
        \<and> ps @ qs = Ps 
        \<and> set ps \<inter> set qs = {}
        \<and> next (last ps) = q
        \<and> last ps = addr tmp
        \<and> ps \<noteq> [] \<and> qs \<noteq> []
       }
  DO
     tmp := q;  ps := ps @ [hd qs];
     q:= q^.next; qs := tl qs
  OD;
  tmp^.next := Null
FI
{\<exists> a as. List next p as \<and> as @ [a] = Ps}"
proof (vcg_simp)
  fix p "next" 
  assume ass:"List next p Ps \<and> (\<exists>y. p = Ref y)" 
  show "(next (addr p) = Null \<longrightarrow> (\<exists>a. [a] = Ps)) \<and>
        ((\<exists>y. next (addr p) = Ref y) \<longrightarrow>
        List next (next (addr p)) (tl Ps) \<and>
        p = Ref (hd Ps) \<and> hd Ps # tl Ps = Ps \<and>
        hd Ps \<notin> set (tl Ps) \<and> next (hd Ps) = next (addr p) \<and>
        hd Ps = addr p \<and> tl Ps \<noteq> [])" (is "(?C1 \<longrightarrow> ?D1) 
         \<and> (?C2 \<longrightarrow> ?D2)")
   proof (intro conjI) 
      show "?C1 \<longrightarrow> ?D1"
        proof (rule impI)
          assume h:"next (addr p) = Null" 
          from ass obtain a and as::"'a list"  where 
           "p = Ref a"  and "List next (next a) as" and 
           "a#as=Ps"  by auto
          from this and h have "as =[]" by simp
          from this and \<open>a#as=Ps\<close> show ?D1 
           by auto
        qed
   next 
      show "?C2 \<longrightarrow> ?D2" 
        proof 
          assume h:" \<exists>y. next (addr p) = Ref y" 
          from this obtain a where 
           nap:"next (addr p) = Ref a" by auto
          from ass obtain y where pr:"p = Ref y" and 
              "Ps \<noteq> []" and "y = hd Ps"  by auto
          from this have ht:"Ps = hd Ps # tl Ps" by simp
          from this and ass have 
           c1: "List next (next (addr p)) (tl Ps)" and
            hs: "hd Ps \<notin> set (tl Ps)" by auto
          from  this and nap have "tl Ps \<noteq> []" and
           "hd (tl Ps) = a" by auto
          from c1 and pr and  \<open>tl Ps \<noteq> []\<close> and ht and hs
           \<open>y=hd Ps\<close> and h show ?D2 by simp
        qed
   qed
next 
  fix p "next" q tmp ps qs
  assume ass:"(\<exists>y. p = Ref y) \<and> List next p Ps \<and>
     List next q qs \<and> List (next(last ps := Null)) p ps \<and>
     ps @ qs = Ps \<and> set ps \<inter> set qs = {} \<and>
     next (last ps) = q \<and> last ps = addr tmp \<and>
     ps \<noteq> [] \<and> qs \<noteq> [] \<and> (\<exists>y. next (addr q) = Ref y)" 
  show "List next (next (addr q)) (tl qs) \<and>
        List (next(hd qs := Null)) p (ps @ [hd qs]) \<and>
        hd qs \<notin> set (tl qs) \<and> set ps \<inter> set (tl qs) = {} 
        \<and> next (hd qs) = next (addr q) \<and>
        hd qs = addr q \<and> tl qs \<noteq> []" (is "?Goal")
  proof -
    from ass have lqs:"List next q qs" "qs \<noteq> []"
      "(\<exists>y. next (addr q) = Ref y)" by auto
    from this obtain a where go:"next (addr q) = Ref a" 
      "hd qs = addr q" "qs = hd qs # tl qs" 
      "List next (next (addr q)) (tl qs)" 
       by (metis List_def Path.simps(2) addr.simps hd_tl) 
    from this(1) this(4) have "tl qs \<noteq> []" by auto
    from  go(2) go(4) have "hd qs \<notin> set (tl qs)" by simp
    from ass have spq:"set ps \<inter> set qs = {}"  by auto
    from this  \<open>qs\<noteq>[]\<close>  have spt:"set ps \<inter> set (tl qs) ={}"
         using list.set_sel(2) by fastforce  
    from ass have lps:"List (next(last ps := Null)) p ps" 
      "next (last ps) = q" by auto 
    from spq go(3) \<open>qs\<noteq>[]\<close> have "hd qs \<notin> set ps" by auto
    from this go(3) lps have
     "List (next(hd qs := Null)) p (ps @ [hd qs])"
      by (metis List_app List_def Path.simps(2) 
           Path_is_List ass)    
    from this spt go \<open>tl qs \<noteq> []\<close> \<open>hd qs \<notin> set (tl qs)\<close>
      show ?Goal by simp
  qed
next 
  fix p "next" q tmp ps qs 
  assume ass:"(\<exists>y. p = Ref y) \<and> List next p Ps \<and>
    List next q qs \<and> List (next(last ps := Null)) p ps
    \<and> ps @ qs = Ps \<and> set ps \<inter> set qs = {} 
    \<and> next (last ps) = q \<and> last ps = addr tmp 
    \<and> ps \<noteq> [] \<and> qs \<noteq> [] \<and> next (addr q) = Null" 
  show "\<exists>a as.
          List (next(tmp \<rightarrow> Null)) p as \<and> as @ [a] = Ps"
   proof - 
     from ass have lqs:"List next q qs" and "qs \<noteq> []"
       and nq:"next (addr q) = Null" and 
      lps: "List (next(last ps := Null)) p ps" 
     and pq: "ps @ qs = Ps" and 
        tmp:"last ps = addr tmp" by auto
     from this(1-2) obtain a as where "q=Ref a" and 
       qs:"qs = a # as" and "List next (next a) as" 
       by (induction qs) simp_all
     from this(3) and nq and \<open>q=Ref a\<close> 
        have "as = []" by simp
     from pq and this and qs have "ps @ [a] = Ps" by simp
     from lps and this and tmp  show ?thesis
       by auto
   qed
qed

lemma "VARS p next q tmp  ps qs
{List next p Ps  \<and> p \<noteq> Null}
IF p^.next = Null
  \<comment> \<open>Ps has exactly one element\<close>
  THEN p:= Null;ps:=[];qs:=Ps
ELSE
  \<comment> \<open>Ps has at least two elements \<close>
  tmp := p; q:= p^.next;
  ps :=[hd Ps]; qs := tl Ps;
  WHILE q^.next \<noteq> Null 
  INV  {p \<noteq> Null \<and> List next p Ps 
        \<and> List next q qs 
        \<and> List (next(last ps := Null)) p ps
        \<and> ps @ qs = Ps 
        \<and> set ps \<inter> set qs = {}
        \<and> next (last ps) = q
        \<and> last ps = addr tmp
        \<and> ps \<noteq> [] \<and> qs \<noteq> []
       }
  DO
     tmp := q;  ps := ps @ [hd qs];
     q:= q^.next; qs := tl qs
  OD;
  tmp^.next := Null
FI
{\<exists> a. List next p ps \<and> ps @ [a]  = Ps}"
apply (vcg_simp)
apply (intro conjI) 
   apply auto[1]
   apply (metis List_Ref List_hd_not_in_tl addr.simps list.discI 
    list.sel(1) list.sel(3))
apply (intro conjI)
   apply (metis List_def Path.simps(2) addr.simps list.collapse) 
   apply (metis List_app List_def Path.simps(2) Path_is_List 
         disjoint_iff_not_equal hd_Cons_tl hd_in_set)
   apply (metis List_distinct distinct.simps(2) list.collapse)
   apply (simp add: disjoint_iff_not_equal list.set_sel(2))
   apply (metis List_def Path.simps(2) addr.simps list.collapse)
   apply (metis List_def Path.simps(2) addr.simps list.collapse)
   apply (metis List_def Path.simps(1) Path.simps(2) addr.simps 
          list.collapse ref.distinct(1))
apply (metis List_unique Path.simps(1) Path_is_List
       addr.simps append.left_neutral empty_iff empty_set 
       fun_upd_triv not_Ref_eq self_append_conv)
done
 
lemma "VARS p next q tmp  ps qs
{List next p Ps  \<and> p \<noteq> Null}
IF p^.next = Null
  \<comment> \<open>Ps has exactly one element\<close>
  THEN p:= Null;ps:=[];qs:=Ps
ELSE
  \<comment> \<open>Ps has at least two elements \<close>
  tmp := p; q:= p^.next;
  ps :=[hd Ps]; qs := tl Ps;
  WHILE q^.next \<noteq> Null 
  INV  {p \<noteq> Null \<and> List next p Ps 
        \<and> List next q qs 
        \<and> List (next(last ps := Null)) p ps
        \<and> ps @ qs = Ps 
        \<and> set ps \<inter> set qs = {}
        \<and> next (last ps) = q
        \<and> last ps = addr tmp
        \<and> ps \<noteq> [] \<and> qs \<noteq> []
       }
  DO
     tmp := q;  ps := ps @ [hd qs];
     q:= q^.next; qs := tl qs
  OD;
  tmp^.next := Null
FI
{List next p ps \<and> ps @ qs  = Ps \<and> length qs = 1}" 
apply (vcg_simp)
apply (intro conjI)
  using Suc_length_conv apply auto[1]
  apply (metis List_Ref List_hd_not_in_tl addr.simps list.discI 
    list.sel(1) list.sel(3))
apply (intro conjI)
  apply (metis List_def Path.simps(2) addr.simps list.collapse)
  apply (metis List_app List_def Path.simps(2) Path_is_List 
     disjoint_iff_not_equal hd_Cons_tl hd_in_set)
  apply (metis List_distinct distinct.simps(2) list.collapse)
  apply (simp add: disjoint_iff_not_equal list.set_sel(2))
  apply (metis List_def Path.simps(2) addr.simps list.collapse)
  apply (metis List_def Path.simps(2) addr.simps list.collapse)
  apply (metis List_def Path.simps(1) Path.simps(2) addr.simps 
   list.collapse ref.distinct(1))
apply (metis List_Ref List_def Path.simps(1) Path.simps(2) 
     addr.simps length_Cons list.size(3) neq_Nil_conv)
done
   
\<comment> \<open>double-linked lists\<close>

end   
   