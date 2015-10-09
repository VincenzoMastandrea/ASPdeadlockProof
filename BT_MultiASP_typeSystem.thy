(*  Title:      BT_MultiASP_typeSystem.thy
    Author:     Vincenzo Mastandrea
                2015

    Note:       Behavioral Type for SimpleMulti-active object  formalisation

*)
(*Conventions:
  x,y=varname
  locs = local variables
  Stl = statement list
  EContext is an execution context, ie a thread 
  EcL = EContext list*)

header {* Syntax and Semantics *}
theory BT_MultiASP_typeSystem imports Main SimpleMultiASP AuxiliaryFunctions begin

subsection {*Behavioral Type Syntax *}
datatype ExtendedType =  Bottom        ("\<bottom>\<^sub>E") 
                      | BasType BasicType (* TODO find a better name*)
                      | Future StaticFuture

datatype BehavioralType =  BTNull  ("0\<^sub>B\<^sub>T")
                          | MethodCall MethodName BasicType "ExtendedType list" BasicType ("_'(_,_')\<rightarrow>_") 
                          | SyncPoint  BehavioralType DepPair ("_.\<^sub>s_")
                          | Par        "BehavioralType list"   
                          | Seq        "BehavioralType list"

datatype FutureRecord =  Bottom ("\<bottom>\<^sub>F")
                      | Unchecked  BasicType BehavioralType ("'(_,_')\<^sub>F")
                      | Checked    BasicType ("'(_,0\<^sub>B\<^sub>T')\<^sup>\<diamond>\<^sub>F")

abbreviation get_rec_UncheckedFutureRec::"FutureRecord \<Rightarrow> BasicType"
where
 "get_rec_UncheckedFutureRec futRec \<equiv> case futRec of Unchecked  BasicType BehavioralType \<Rightarrow> BasicType"

abbreviation get_rec_CheckedFutureRec::"FutureRecord \<Rightarrow> BasicType"
where
 "get_rec_CheckedFutureRec futRec \<equiv> case futRec of Checked  BasicType \<Rightarrow> BasicType"


abbreviation get_bt_UncheckedFutureRec::"FutureRecord \<Rightarrow> BehavioralType"
where
 "get_bt_UncheckedFutureRec futRec \<equiv> case futRec of Unchecked  BasicType BehavioralType \<Rightarrow> BehavioralType"

abbreviation get_bt_CheckedFutureRec::"FutureRecord \<Rightarrow> BehavioralType"
where
 "get_bt_CheckedFutureRec futRec \<equiv> 0\<^sub>B\<^sub>T"


datatype BTMethod = Bottom ("\<bottom>\<^sub>M")
                  | BTMet ObjectRecord "(VarName*ExtendedType) list" BehavioralType BehavioralType BasicType   ("'(_,_')'{\<langle>_,_'\<rangle>}_")
                  (* BTMet "type of this""parameters" "BT of the body (synchronous)" "BT of the body (asynchronous)" "return type"*)

datatype BTClass = BTCl "MethodName => BehavioralType"

datatype BTProgram = BTProg BTClass BehavioralType BehavioralType
(* program BT of the unique class, BT of the main (synch), BT of the main (asynch)*)

subsection {*Typing Rules *}

type_synonym Env_var = "VarOrThis => ExtendedType"
type_synonym Env_fut = "StaticFuture => FutureRecord"
type_synonym Env_met = "MethodName => BTMethod"
datatype Env = Gamma Env_var Env_fut Env_met

abbreviation gamma_var::"Env \<Rightarrow> Env_var"  ("_\<^sup>V")
 where "\<Gamma>\<^sup>V \<equiv> case \<Gamma> of (Gamma \<Gamma>_v \<Gamma>_f \<Gamma>_m) \<Rightarrow> \<Gamma>_v"

abbreviation upd_gamma_var::"Env \<Rightarrow> VarOrThis \<Rightarrow> ExtendedType \<Rightarrow> Env"  ("_[_\<rightarrow>_]\<^sub>V")
 where "(\<Gamma>[x\<rightarrow>ET]\<^sub>V) \<equiv> case \<Gamma> of (Gamma \<Gamma>_v \<Gamma>_f \<Gamma>_m) \<Rightarrow> (Gamma (\<Gamma>_v(x:=ET)) \<Gamma>_f \<Gamma>_m)"

abbreviation gamma_fut::"Env \<Rightarrow> Env_fut"  ("_\<^sup>F")
 where "\<Gamma>\<^sup>F \<equiv> case \<Gamma> of (Gamma \<Gamma>_v \<Gamma>_f \<Gamma>_m) \<Rightarrow> \<Gamma>_f"

abbreviation upd_gamma_fut::"Env \<Rightarrow> StaticFuture \<Rightarrow> FutureRecord \<Rightarrow> Env"  ("_[_\<rightarrow>_]\<^sub>F")
 where "(\<Gamma>[f\<rightarrow>FR]\<^sub>F) \<equiv> case \<Gamma> of (Gamma \<Gamma>_v \<Gamma>_f \<Gamma>_m) \<Rightarrow> (Gamma \<Gamma>_v (\<Gamma>_f(f:=FR)) \<Gamma>_m)"

abbreviation gamma_met::"Env \<Rightarrow> Env_met"  ("_\<^sup>M" )
 where "\<Gamma>\<^sup>M \<equiv> case \<Gamma> of (Gamma \<Gamma>_v \<Gamma>_f \<Gamma>_m) \<Rightarrow> \<Gamma>_m"

definition fresh_act
 where
  "fresh_act \<Gamma> \<alpha> \<equiv> (\<forall> x \<gamma>. (\<Gamma>\<^sup>V) x = BasType(Obj [\<gamma>]\<^sub>O) \<longrightarrow> \<gamma> \<noteq> \<alpha> )"   

definition fresh_fut
 where
  "fresh_fut \<Gamma> f \<equiv> (\<forall> x f'. (\<Gamma>\<^sup>V) x = (Future f') \<longrightarrow> f' \<noteq> f )"  

definition compare_Env_var::"Env_var \<Rightarrow> Env_var \<Rightarrow> Env_var \<Rightarrow> bool"
(* for each variable in the domain of the first gamma, the two other gammas coincide*)
 where 
  "compare_Env_var \<Gamma>_v \<Gamma>_v\<^sub>1 \<Gamma>_v\<^sub>2 \<equiv> \<forall> x. (\<Gamma>_v x \<noteq> \<bottom>\<^sub>E) \<longrightarrow>  \<Gamma>_v\<^sub>1 x =  \<Gamma>_v\<^sub>2 x"

definition compare_Env_fut::"Env_fut \<Rightarrow> Env_fut \<Rightarrow> Env_fut \<Rightarrow> bool"
(* idem for fut environment *)
 where 
  "compare_Env_fut \<Gamma>_f \<Gamma>_f\<^sub>1 \<Gamma>_f\<^sub>2 \<equiv> \<forall> f. (\<Gamma>_f f \<noteq> \<bottom>\<^sub>F ) \<longrightarrow> \<Gamma>_f\<^sub>1 f =  \<Gamma>_f\<^sub>2 f"

definition compare_Env_met::"Env_met \<Rightarrow> Env_met \<Rightarrow> Env_met \<Rightarrow> bool"
(* idem for met environment*)
 where 
  "compare_Env_met \<Gamma>_m \<Gamma>_m\<^sub>1 \<Gamma>_m\<^sub>2 \<equiv> \<forall> m. (\<Gamma>_m m \<noteq> \<bottom>\<^sub>M) \<longrightarrow>  \<Gamma>_m\<^sub>1 m =  \<Gamma>_m\<^sub>2 m"

definition compare_Env::"Env \<Rightarrow> Env \<Rightarrow> Env \<Rightarrow> bool"
(* idem for the whole gamma*)
 where
  "compare_Env \<Gamma> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<equiv> compare_Env_var (\<Gamma>\<^sup>V) (\<Gamma>\<^sub>1\<^sup>V) (\<Gamma>\<^sub>2\<^sup>V) \<and>
                         compare_Env_fut (\<Gamma>\<^sup>F) (\<Gamma>\<^sub>1\<^sup>F) (\<Gamma>\<^sub>2\<^sup>F) \<and>
                         compare_Env_met (\<Gamma>\<^sup>M) (\<Gamma>\<^sub>1\<^sup>M) (\<Gamma>\<^sub>2\<^sup>M)"


definition empty_intersection::"Env \<Rightarrow> Env \<Rightarrow> bool" ("_ \<inter> _ = \<emptyset>")
 where "empty_intersection \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<equiv> ((\<forall> x. ((\<Gamma>\<^sub>1\<^sup>V) x \<noteq> \<bottom>\<^sub>E) \<longrightarrow> ((\<Gamma>\<^sub>2\<^sup>V) x = \<bottom>\<^sub>E)) \<and>
                                        (\<forall> y. ((\<Gamma>\<^sub>2\<^sup>V) y \<noteq> \<bottom>\<^sub>E \<longrightarrow> (\<Gamma>\<^sub>1\<^sup>V) y = \<bottom>\<^sub>E))) \<and>
                                    ((\<forall> f. ((\<Gamma>\<^sub>1\<^sup>F) f \<noteq> \<bottom>\<^sub>F) \<longrightarrow> ((\<Gamma>\<^sub>2\<^sup>F) f = \<bottom>\<^sub>F)) \<and>
                                        (\<forall> f'. ((\<Gamma>\<^sub>2\<^sup>F) f' \<noteq> \<bottom>\<^sub>F \<longrightarrow> (\<Gamma>\<^sub>1\<^sup>F) f' = \<bottom>\<^sub>F))) \<and>
                                    ((\<forall> m. ((\<Gamma>\<^sub>1\<^sup>M) m \<noteq> \<bottom>\<^sub>M) \<longrightarrow> ((\<Gamma>\<^sub>2\<^sup>M) m = \<bottom>\<^sub>M)) \<and>
                                        (\<forall> m'. ((\<Gamma>\<^sub>2\<^sup>M) m' \<noteq> \<bottom>\<^sub>M \<longrightarrow> (\<Gamma>\<^sub>1\<^sup>M) m' = \<bottom>\<^sub>M)))"

definition domain_union::"Env \<Rightarrow> Env \<Rightarrow> Env \<Rightarrow> bool" ("dom(_) = dom(_) \<union> dom(_)")
 where "domain_union \<Gamma> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<equiv> (\<forall> x. ((\<Gamma>\<^sup>V) x \<noteq> \<bottom>\<^sub>E) \<longrightarrow> ((\<Gamma>\<^sub>1\<^sup>V) x \<noteq> \<bottom>\<^sub>E \<or> (\<Gamma>\<^sub>2\<^sup>V) x \<noteq> \<bottom>\<^sub>E)) \<and>
                               (\<forall> f. ((\<Gamma>\<^sup>F) f \<noteq> \<bottom>\<^sub>F) \<longrightarrow> ((\<Gamma>\<^sub>1\<^sup>F) f \<noteq> \<bottom>\<^sub>F \<or> (\<Gamma>\<^sub>2\<^sup>F) f \<noteq> \<bottom>\<^sub>F)) \<and> 
                               (\<forall> m. ((\<Gamma>\<^sup>M) m \<noteq> \<bottom>\<^sub>M) \<longrightarrow> ((\<Gamma>\<^sub>1\<^sup>M) m \<noteq> \<bottom>\<^sub>M \<or> (\<Gamma>\<^sub>2\<^sup>M) m \<noteq> \<bottom>\<^sub>M))"

(*check if \<Gamma>' is equal to \<Gamma>\<^sup>F*)
definition sub_env_fut:: "Env \<Rightarrow> Env \<Rightarrow> bool" ("_ = _|\<^sub>F")
 where
   "sub_env_fut \<Gamma>' \<Gamma> \<equiv> (\<forall> x m. ( (\<Gamma>'\<^sup>V) x = \<bottom>\<^sub>E \<and> (\<Gamma>'\<^sup>M) m = \<bottom>\<^sub>M )) \<and>
                        (\<forall> f. (\<Gamma>\<^sup>F) f = (\<Gamma>\<^sup>F) f )"

(*\<Gamma> = \<Gamma>\<^sub>1 + \<Gamma>\<^sub>2*)
definition sum_Env::"Env \<Rightarrow> Env \<Rightarrow> Env \<Rightarrow> bool" ("_ = _ +\<^sub>\<Gamma> _")
 where
  "sum_Env \<Gamma> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<equiv> (\<Gamma>\<^sub>1 \<inter> \<Gamma>\<^sub>2 = \<emptyset>) \<and> 
                     (dom(\<Gamma>) = dom(\<Gamma>\<^sub>1) \<union> dom(\<Gamma>\<^sub>2)) \<and>
                     (\<forall> x. ((\<Gamma>\<^sup>V) x \<noteq> \<bottom>\<^sub>E \<and> (\<Gamma>\<^sub>1\<^sup>V) x \<noteq> \<bottom>\<^sub>E)  \<longrightarrow> ((\<Gamma>\<^sup>V) x = (\<Gamma>\<^sub>1\<^sup>V) x) ) \<and>
                     (\<forall> x. ((\<Gamma>\<^sup>V) x \<noteq> \<bottom>\<^sub>E \<and> (\<Gamma>\<^sub>2\<^sup>V) x \<noteq> \<bottom>\<^sub>E)  \<longrightarrow> ((\<Gamma>\<^sup>V) x = (\<Gamma>\<^sub>2\<^sup>V) x) ) \<and>
                     (\<forall> f. ((\<Gamma>\<^sup>F) f \<noteq> \<bottom>\<^sub>F \<and> (\<Gamma>\<^sub>1\<^sup>F) f \<noteq> \<bottom>\<^sub>F)  \<longrightarrow> ((\<Gamma>\<^sup>F) f = (\<Gamma>\<^sub>1\<^sup>F) f) ) \<and>
                     (\<forall> f. ((\<Gamma>\<^sup>F) f \<noteq> \<bottom>\<^sub>F \<and> (\<Gamma>\<^sub>2\<^sup>F) f \<noteq> \<bottom>\<^sub>F)  \<longrightarrow> ((\<Gamma>\<^sup>F) f = (\<Gamma>\<^sub>2\<^sup>F) f) ) \<and>
                     (\<forall> m. ((\<Gamma>\<^sup>M) m \<noteq> \<bottom>\<^sub>M \<and> (\<Gamma>\<^sub>1\<^sup>M) m \<noteq> \<bottom>\<^sub>M)  \<longrightarrow> ((\<Gamma>\<^sup>M) m = (\<Gamma>\<^sub>1\<^sup>M) m) ) \<and>
                     (\<forall> m. ((\<Gamma>\<^sup>M) m \<noteq> \<bottom>\<^sub>M \<and> (\<Gamma>\<^sub>2\<^sup>M) m \<noteq> \<bottom>\<^sub>M)  \<longrightarrow> ((\<Gamma>\<^sup>M) m = (\<Gamma>\<^sub>2\<^sup>M) m) )" 

definition getFutListfromFutEnv::"Env_fut \<Rightarrow> StaticFuture list"
where
 "getFutListfromFutEnv \<Gamma>\<^sub>f \<equiv> sorted_list_of_set {f. \<exists> r b. (\<Gamma>\<^sub>f) f = (r,b)\<^sub>F} "

primrec getBTfromFutList:: "Env \<Rightarrow> StaticFuture list \<Rightarrow> BehavioralType list"
where
 "getBTfromFutList \<Gamma> [] = []" |
 "getBTfromFutList \<Gamma> (f#futList) = get_bt_UncheckedFutureRec((\<Gamma>\<^sup>F) f)#(getBTfromFutList \<Gamma> futList)" 

abbreviation unsync:: "Env \<Rightarrow> BehavioralType" ("unsync(_)")
where
 "unsync \<Gamma> \<equiv> Par(getBTfromFutList \<Gamma> (getFutListfromFutEnv (\<Gamma>\<^sup>F)))"


(*T-Val*)
inductive judge_prim_jud:: "Env \<Rightarrow> Primitive \<Rightarrow> BasicType \<Rightarrow> bool" ("_ \<turnstile>\<^sub>P _:_")
where "\<Gamma> \<turnstile>\<^sub>P e : _\<^sub>T"

(*T-Var*)
inductive judge_var_jud:: "Env \<Rightarrow> VarOrThis \<Rightarrow> BasicType \<Rightarrow> bool" ("_ \<turnstile>\<^sub>V _:_")
where "\<lbrakk>(\<Gamma>\<^sup>V) v = (BasType r)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>V v : r"

(*T-Fut*)
inductive judge_fut_jud:: "Env \<Rightarrow> StaticFuture \<Rightarrow> FutureRecord \<Rightarrow> bool" ("_ \<turnstile>\<^sub>F _:_")
where "\<lbrakk>(\<Gamma>\<^sup>F) v = r\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>F v : r"

(*Expression with side effects *)
inductive judge_exp_jud:: "Env \<Rightarrow> MethodName \<Rightarrow> Expression \<Rightarrow> ExtendedType \<Rightarrow> BehavioralType \<Rightarrow> Env \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>E\<^sup>_ _:_,_|_") 
 where
    (*T-Exp*)
    T_Pure [simp, intro!]: 
      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>P e : r\<rbrakk>
      \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E\<^sup>m (Val (Prim e)): (BasType r),0\<^sub>B\<^sub>T | \<Gamma> " |
    T_Exp_Plus [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>E\<^sup>m e: (BasType r), b | \<Gamma>' ;
        \<Gamma>'\<turnstile>\<^sub>E\<^sup>m e': (BasType r), b' | \<Gamma>''\<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E\<^sup>m (e +\<^sub>A e'): (BasType r), Seq(b;\<^sub>sb') | \<Gamma>'' " |
    T_Exp_And [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>E\<^sup>m e: (BasType r), b | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>E\<^sup>m e': (BasType r), b' | \<Gamma>''\<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E\<^sup>m (e &\<^sub>A e') : (BasType r), Seq(b;\<^sub>sb') | \<Gamma>'' " |
     T_Exp_Test [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>E\<^sup>m e: (BasType r), b | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>E\<^sup>m e': (BasType r), b' | \<Gamma>''\<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E\<^sup>m (e ==\<^sub>A e'): (BasType r), Seq(b;\<^sub>sb') | \<Gamma>'' " |
    
     (*T-Sync*)
     T_Sync [simp, intro!]: 
      "\<lbrakk>\<Gamma>\<^sup>V x = (Future f); 
        \<Gamma> \<turnstile>\<^sub>F f : fut_rec ;
        fut_rec = (r, b)\<^sub>F;
        r = (\<alpha>'..m'\<leadsto>r');
        \<Gamma> \<turnstile>\<^sub>V this : (Obj [\<alpha>]\<^sub>O);
        fut_rec_checked = (r,0\<^sub>B\<^sub>T)\<^sup>\<diamond>\<^sub>F;
        \<Gamma>'= (\<Gamma>[f\<rightarrow>fut_rec_checked]\<^sub>F)\<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E\<^sup>m (Var x) : (BasType r'), Par((b.\<^sub>s(\<alpha>..m,\<alpha>'..m')) \<parallel> unsync(\<Gamma>)) | (\<Gamma>') " |   
    
     (*T-Value-Tick*)
     T_Value_Tick [simp, intro!]: 
      "\<lbrakk>\<Gamma>\<^sup>V x = (Future f);
        \<Gamma> \<turnstile>\<^sub>F f : fut_rec;
        fut_rec = (Checked r);
        r = (\<alpha>..m\<leadsto>r')\<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E\<^sup>m (Var x) : (BasType r'), 0\<^sub>B\<^sub>T | \<Gamma> "      

(*Statements*)
inductive judge_stmt_jud:: "Env \<Rightarrow> MethodName \<Rightarrow> Statement \<Rightarrow> BehavioralType \<Rightarrow> Env \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>S\<^sup>_ _:_|_") 
and judge_stmtlist_jud:: "Env \<Rightarrow> MethodName \<Rightarrow> Statement list \<Rightarrow> BehavioralType \<Rightarrow> Env \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>S\<^sub>l\<^sup>_ _:_|_") 
 where

    (*T-Alias*)
    T_Alias  [simp, intro!]: 
      "\<lbrakk>(\<Gamma>\<^sup>V) y = (Future f);
        \<Gamma>'= (\<Gamma>[(Variable x) \<rightarrow> (Future f)]\<^sub>V)\<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>S\<^sup>m x =\<^sub>A (Expr (Var y)) : 0\<^sub>B\<^sub>T | \<Gamma>' " |
  
     (*T-Expression*)
     T_Expression [simp, intro!]:
      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>E\<^sup>m e : (BasType r), b | \<Gamma>'; 
         \<Gamma>'= (\<Gamma>[(Variable x) \<rightarrow> (BasType r)]\<^sub>V)\<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>S\<^sup>m x =\<^sub>A (Expr e) : b | \<Gamma>' " |
     
     (*T-NewActive*)
     T_NewActive [simp, intro!]:
      "\<lbrakk>fresh_act \<Gamma> \<alpha>;
        \<Gamma>'= (\<Gamma>[(Variable x) \<rightarrow> (BasType (Obj [\<alpha>]\<^sub>O))]\<^sub>V)\<rbrakk>
      \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>S\<^sup>m x =\<^sub>A newActive() : 0\<^sub>B\<^sub>T | \<Gamma>'" |    
 
     (*T-Invk*)
     T_Invk [simp, intro!]:
      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>V (This) : (Obj [\<alpha>]\<^sub>O);
        \<Gamma> \<turnstile>\<^sub>E\<^sup>m e : (BasType (Obj [\<alpha>']\<^sub>O)), b | \<Gamma>' ;
        (* apply sobstitution
        (\<Gamma>'\<^sup>M) m' = ([\<alpha>'']\<^sub>O,parType){\<langle>b\<^sub>1,b\<^sub>2\<rangle>} r'; *)
        (\<Gamma>'\<^sup>M) m' = ([\<alpha>']\<^sub>O,parType){\<langle>b\<^sub>1,b\<^sub>2\<rangle>} r'; 
        fresh_fut \<Gamma>' f ;
        r = (\<alpha>'..m'\<leadsto>r');
        (*typing parameters*)
        length parType = length el ; 
        \<forall> i<length el. \<exists> bt \<Gamma>t. (\<Gamma>' \<turnstile>\<^sub>E\<^sup>m (el!i) : (snd (parType!i)), bt | \<Gamma>t );
        (*                  *)
        b\<^sub>3 = (m'((Obj [\<alpha>']\<^sub>O) , map snd parType)\<rightarrow>r');
        \<Gamma>''= (\<Gamma>'[f \<rightarrow> (r, b\<^sub>3)\<^sub>F]\<^sub>F)\<rbrakk>
       \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>S\<^sup>m (x=\<^sub>Ae.\<^sub>Am'(el)) : Seq(b ;\<^sub>s Par(b\<^sub>3 \<parallel> unsync(\<Gamma>'))) | \<Gamma>' " |
   
     (*T-Return*)
     T_Return [simp, intro!]:
      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>E\<^sup>m e : (BasType r) , b | \<Gamma>'\<rbrakk>
      \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>S\<^sup>m (return e) : 0\<^sub>B\<^sub>T | \<Gamma> "  |
   
     (*T-If*) 
     T_If [simp, intro!]:
     "\<lbrakk> \<Gamma> \<turnstile>\<^sub>E\<^sup>m cond : BasType _\<^sub>T , b | \<Gamma>' ;
       \<Gamma>' \<turnstile>\<^sub>S\<^sub>l\<^sup>m sl\<^sub>1 : b\<^sub>1 | \<Gamma>\<^sub>1 ;
       \<Gamma>' \<turnstile>\<^sub>S\<^sub>l\<^sup>m sl\<^sub>2 : b\<^sub>2 | \<Gamma>\<^sub>2 ;
       compare_Env \<Gamma>' \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 ;  (*\<And>\<^sub>x\<^sub>\<in>\<^sub>d\<^sub>o\<^sub>m\<^sub>(\<^sub>\<Gamma>\<^sub>) \<Gamma>\<^sub>1(x) = \<Gamma>\<^sub>2(x)*)
       (\<forall>x f' f''. (\<exists> f .(((\<Gamma>\<^sup>V) x) = (Future f)) \<longrightarrow> ((\<Gamma>\<^sub>1\<^sup>V) x = (Future f') \<and> (\<Gamma>\<^sub>2\<^sup>V) x = (Future f''))) 
                           \<longrightarrow> (\<Gamma>\<^sub>1\<^sup>F) f' = (\<Gamma>\<^sub>2\<^sup>F) f''); (*f = f' because of compare_\<Gamma>*)
                           (*\<up> \<And>\<^sub>x\<^sub>\<in>\<^sub>F\<^sub>u\<^sub>t\<^sub>(\<^sub>\<Gamma>\<^sub>) \<Gamma>\<^sub>1(\<Gamma>\<^sub>1(x)) = \<Gamma>\<^sub>2(\<Gamma>\<^sub>2(x)) *)
       \<Gamma>\<^sub>2\<^sub>F = \<Gamma>\<^sub>2|\<^sub>F ; 
       \<Gamma>' =  \<Gamma>\<^sub>1 +\<^sub>\<Gamma> \<Gamma>\<^sub>2\<^sub>F\<rbrakk>
      \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>S\<^sup>m IF cond THEN sl\<^sub>1 ELSE sl\<^sub>2 : Par(b\<^sub>1\<parallel>b\<^sub>2) | \<Gamma>'" | 
 
    (*T-Seq*)
    T_Seq [simp, intro!]:
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>S\<^sup>m s : b | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>S\<^sub>l\<^sup>m sl' : b' | \<Gamma>'' \<rbrakk>
      \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>S\<^sub>l\<^sup>m s;;sl' : Seq(b;\<^sub>sb') | \<Gamma>'' " |       
    T_EmptyList [simp, intro!]:
      " \<Gamma> \<turnstile>\<^sub>S\<^sub>l\<^sup>m [] : 0\<^sub>B\<^sub>T | \<Gamma> " 
   
end
