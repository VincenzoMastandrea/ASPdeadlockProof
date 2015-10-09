(*  Title:      BT_MultiASP_typeRuntime.thy
    Author:     Vincenzo Mastandrea
                2015

    Note:       Behavioral Type at Runtime for SimpleMulti-active object  formalisation

*)

header {* Syntax and Semantics *}
theory BT_MultiASP_typeRuntime imports  BT_MultiASP_typeSystem Main SimpleMultiASP AuxiliaryFunctions begin

subsection {*Behavioral Type Syntax *}

datatype ExtendedType_R =  Bottom        ("\<^sup>R\<bottom>\<^sub>E") 
                        | BasType BasicType (* TODO find a better name*)
                        | Future Future 

datatype BehavioralType_R =  BTNull  ("\<^sup>R0\<^sub>B\<^sub>T")
                          | MethodCall    MethodName BasicType "ExtendedType_R list" BasicType ("_'(_,_')\<rightarrow>\<^sub>R_") 
                          | SyncPoint     BehavioralType_R DepPair ("_.\<^sub>s\<^sub>R_")
                          | Par           "BehavioralType_R list"   
                          | Seq           "BehavioralType_R list"
                          | RunFuture     RuntimeFuture
                          | RunFutPair    RuntimeFuture DepPair ("_.\<^sub>f_")
                          | PairBehavior  BehavioralType_R BehavioralType_R ActName Request ("\<langle>_,_\<rangle>\<^sup>_\<^sup>.\<^sup>_") 

datatype BehavioralType_Config = BTNull  ("0\<^sub>B\<^sub>T\<^sub>C")
                               | PairBehavior_Conf  RuntimeFuture BehavioralType_R BehavioralType_R ActName Request ("\<^sup>_\<langle>_,_\<rangle>\<^sub>_.\<^sub>_") 
                               | MethodCall_Conf    MethodName BasicType "ExtendedType_R list" BasicType RuntimeFuture ("'[_'(_,_')\<rightarrow>_']\<^sub>_")
                               | Par_Conf           "BehavioralType_Config list"

datatype FutureRecord_R =  Bottom ("\<^sup>R\<bottom>\<^sub>F")
                        | Unchecked  BasicType BehavioralType_R ("\<^sup>R'(_,_')\<^sub>F")
                        | Checked    BasicType ("\<^sup>R'(_,0\<^sub>B\<^sub>T')\<^sup>\<diamond>\<^sub>F")

abbreviation get_rec_UncheckedFutureRec_R::"FutureRecord_R \<Rightarrow> BasicType"
where
 "get_rec_UncheckedFutureRec_R futRec \<equiv> case futRec of Unchecked  BasicType BehavioralType_R \<Rightarrow> BasicType"

abbreviation get_rec_CheckedFutureRec_R::"FutureRecord_R \<Rightarrow> BasicType"
where
 "get_rec_CheckedFutureRec_R futRec \<equiv> case futRec of Checked  BasicType \<Rightarrow> BasicType"

abbreviation get_bt_UncheckedFutureRec_R::"FutureRecord_R \<Rightarrow> BehavioralType_R"
where
 "get_bt_UncheckedFutureRec_R futRec \<equiv> case futRec of Unchecked  BasicType BehavioralType_R \<Rightarrow> BehavioralType_R"

abbreviation get_bt_CheckedFutureRec_R::"FutureRecord_R \<Rightarrow> BehavioralType_R"
where
 "get_bt_CheckedFutureRec_R futRec \<equiv> \<^sup>R0\<^sub>B\<^sub>T"
          
datatype BTMethod_R = Bottom ("\<^sup>R\<bottom>\<^sub>M")
                  | BTMet ObjectRecord "(VarName*ExtendedType_R) list" BehavioralType_R BehavioralType_R BasicType   ("'(_,_')'{\<langle>_,_'\<rangle>}\<^sub>R_")
                  (* BTMet "type of this""parameters" "BT of the body (synchronous)" "BT of the body (asynchronous)" "return type"*)

datatype BTClass_R = BTCl "MethodName => BehavioralType_R"

datatype BTProgram_R = BTProg BTClass_R BehavioralType_R BehavioralType_R
(* program BT of the unique class, BT of the main (synch), BT of the main (asynch)*)

subsection {*Typing Rules *}

type_synonym Env_R_var = "VarOrThis => ExtendedType_R"
type_synonym Env_R_fut = "Future => FutureRecord_R"
type_synonym Env_R_met = "MethodName => BTMethod_R"
datatype Env_R = Delta Env_R_var Env_R_fut Env_R_met

abbreviation delta_var::"Env_R \<Rightarrow> Env_R_var"  ("_\<^sup>V\<^sup>-\<^sup>R")
 where "\<Delta>\<^sup>V\<^sup>-\<^sup>R \<equiv> case \<Delta> of (Delta \<Delta>_v \<Delta>_f \<Delta>_m) \<Rightarrow> \<Delta>_v"

abbreviation upd_delta_var::"Env_R \<Rightarrow> VarOrThis \<Rightarrow> ExtendedType_R \<Rightarrow> Env_R"  ("_[_\<rightarrow>\<^sub>R_]\<^sub>V")
 where "\<Delta>[x\<rightarrow>\<^sub>RET]\<^sub>V \<equiv> case \<Delta> of (Delta \<Delta>_v \<Delta>_f \<Delta>_m) \<Rightarrow> (Delta (\<Delta>_v(x:=ET)) \<Delta>_f \<Delta>_m)"

abbreviation delta_fut::"Env_R \<Rightarrow> Env_R_fut"  ("_\<^sup>F\<^sup>-\<^sup>R")
 where "\<Delta>\<^sup>F\<^sup>-\<^sup>R \<equiv> case \<Delta> of (Delta \<Delta>_v \<Delta>_f \<Delta>_m) \<Rightarrow> \<Delta>_f"

abbreviation upd_delta_fut::"Env_R \<Rightarrow> Future \<Rightarrow> FutureRecord_R \<Rightarrow> Env_R"  ("_[_\<rightarrow>\<^sub>R_]\<^sub>F")
 where "\<Delta>[f\<rightarrow>\<^sub>RFR]\<^sub>F \<equiv> case \<Delta> of (Delta \<Delta>_v \<Delta>_f \<Delta>_m) \<Rightarrow> (Delta \<Delta>_v (\<Delta>_f(f:=FR)) \<Delta>_m)"

abbreviation delta_met::"Env_R \<Rightarrow> Env_R_met"  ("_\<^sup>M\<^sup>-\<^sup>R" )
 where "\<Delta>\<^sup>M\<^sup>-\<^sup>R \<equiv> case \<Delta> of (Delta \<Delta>_v \<Delta>_f \<Delta>_m) \<Rightarrow> \<Delta>_m"

definition fresh_act_R
 where
  "fresh_act_R \<Delta> \<alpha> \<equiv> (\<forall> x \<gamma>. (\<Delta>\<^sup>V\<^sup>-\<^sup>R) x = BasType(Obj [\<gamma>]\<^sub>O) \<longrightarrow> \<gamma> \<noteq> \<alpha> )"   

definition fresh_StatFut_R
 where
  "fresh_StatFut_R \<Delta> f \<equiv> (\<forall> x f'. (\<Delta>\<^sup>V\<^sup>-\<^sup>R) x = (Future (StatFut f')) \<longrightarrow> f' \<noteq> f )"  

definition fresh_RunFut_R
 where
  "fresh_RunFut_R \<Delta> f \<equiv> (\<forall> x f'. (\<Delta>\<^sup>V\<^sup>-\<^sup>R) x = (Future (RunFut f')) \<longrightarrow> f' \<noteq> f )"  



definition compare_Env_R_var::"Env_R_var \<Rightarrow> Env_R_var \<Rightarrow> Env_R_var \<Rightarrow> bool"
(* for each variable in the domain of the first gamma, the two other gammas coincide*)
 where 
  "compare_Env_R_var \<Delta>_v \<Delta>_v\<^sub>1 \<Delta>_v\<^sub>2 \<equiv> \<forall> x. (\<Delta>_v x \<noteq> \<^sup>R\<bottom>\<^sub>E) \<longrightarrow>  \<Delta>_v\<^sub>1 x =  \<Delta>_v\<^sub>2 x"

definition compare_Env_R_fut::"Env_R_fut \<Rightarrow> Env_R_fut \<Rightarrow> Env_R_fut \<Rightarrow> bool"
(* idem for fut environment *)
 where 
  "compare_Env_R_fut \<Delta>_f \<Delta>_f\<^sub>1 \<Delta>_f\<^sub>2 \<equiv> \<forall> f. (\<Delta>_f f \<noteq> \<^sup>R\<bottom>\<^sub>F ) \<longrightarrow> \<Delta>_f\<^sub>1 f =  \<Delta>_f\<^sub>2 f"

definition compare_Env_R_met::"Env_R_met \<Rightarrow> Env_R_met \<Rightarrow> Env_R_met \<Rightarrow> bool"
(* idem for met environment*)
 where 
  "compare_Env_R_met \<Delta>_m \<Delta>_m\<^sub>1 \<Delta>_m\<^sub>2 \<equiv> \<forall> m. (\<Delta>_m m \<noteq> \<^sup>R\<bottom>\<^sub>M) \<longrightarrow>  \<Delta>_m\<^sub>1 m =  \<Delta>_m\<^sub>2 m"

definition compare_Env_R::"Env_R \<Rightarrow> Env_R \<Rightarrow> Env_R \<Rightarrow> bool"
(* idem for the whole gamma*)
 where
  "compare_Env_R \<Delta> \<Delta>\<^sub>1 \<Delta>\<^sub>2 \<equiv> compare_Env_R_var (\<Delta>\<^sup>V\<^sup>-\<^sup>R) (\<Delta>\<^sub>1\<^sup>V\<^sup>-\<^sup>R) (\<Delta>\<^sub>2\<^sup>V\<^sup>-\<^sup>R) \<and>
                            compare_Env_R_fut (\<Delta>\<^sup>F\<^sup>-\<^sup>R) (\<Delta>\<^sub>1\<^sup>F\<^sup>-\<^sup>R) (\<Delta>\<^sub>2\<^sup>F\<^sup>-\<^sup>R) \<and>
                            compare_Env_R_met (\<Delta>\<^sup>M\<^sup>-\<^sup>R) (\<Delta>\<^sub>1\<^sup>M\<^sup>-\<^sup>R) (\<Delta>\<^sub>2\<^sup>M\<^sup>-\<^sup>R)"

definition empty_intersection_R::"Env_R \<Rightarrow> Env_R \<Rightarrow> bool" ("_ \<inter>\<^sub>R _ = \<emptyset>")
 where "empty_intersection_R \<Delta>\<^sub>1 \<Delta>\<^sub>2 \<equiv> ((\<forall> x. ((\<Delta>\<^sub>1\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E) \<longrightarrow> ((\<Delta>\<^sub>2\<^sup>V\<^sup>-\<^sup>R) x = \<^sup>R\<bottom>\<^sub>E)) \<and>
                                        (\<forall> y. ((\<Delta>\<^sub>2\<^sup>V\<^sup>-\<^sup>R) y \<noteq> \<^sup>R\<bottom>\<^sub>E \<longrightarrow> (\<Delta>\<^sub>1\<^sup>V\<^sup>-\<^sup>R) y = \<^sup>R\<bottom>\<^sub>E))) \<and>
                                    ((\<forall> f. ((\<Delta>\<^sub>1\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F) \<longrightarrow> ((\<Delta>\<^sub>2\<^sup>F\<^sup>-\<^sup>R) f = \<^sup>R\<bottom>\<^sub>F)) \<and>
                                        (\<forall> f'. ((\<Delta>\<^sub>2\<^sup>F\<^sup>-\<^sup>R) f' \<noteq> \<^sup>R\<bottom>\<^sub>F \<longrightarrow> (\<Delta>\<^sub>1\<^sup>F\<^sup>-\<^sup>R) f' = \<^sup>R\<bottom>\<^sub>F))) \<and>
                                    ((\<forall> m. ((\<Delta>\<^sub>1\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M) \<longrightarrow> ((\<Delta>\<^sub>2\<^sup>M\<^sup>-\<^sup>R) m = \<^sup>R\<bottom>\<^sub>M)) \<and>
                                        (\<forall> m'. ((\<Delta>\<^sub>2\<^sup>M\<^sup>-\<^sup>R) m' \<noteq> \<^sup>R\<bottom>\<^sub>M \<longrightarrow> (\<Delta>\<^sub>1\<^sup>M\<^sup>-\<^sup>R) m' = \<^sup>R\<bottom>\<^sub>M)))"

definition domain_union_R::"Env_R \<Rightarrow> Env_R \<Rightarrow> Env_R \<Rightarrow> bool" ("dom(_) = dom(_) \<union>\<^sub>R dom(_)")
 where "dom(\<Delta>) = dom(\<Delta>\<^sub>1) \<union>\<^sub>R dom(\<Delta>\<^sub>2) \<equiv> (\<forall> x. ((\<Delta>\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E) \<longrightarrow> ((\<Delta>\<^sub>1\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E \<or> (\<Delta>\<^sub>2\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E)) \<and>
                                       (\<forall> f. ((\<Delta>\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F) \<longrightarrow> ((\<Delta>\<^sub>1\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F \<or> (\<Delta>\<^sub>2\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F)) \<and> 
                                       (\<forall> m. ((\<Delta>\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M) \<longrightarrow> ((\<Delta>\<^sub>1\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M \<or> (\<Delta>\<^sub>2\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M))"

definition sub_env_fut_R:: "Env_R \<Rightarrow> Env_R \<Rightarrow> bool" ("_ = _|\<^sub>F\<^sub>R")
 where
   "\<Delta>' = \<Delta>|\<^sub>F\<^sub>R \<equiv> (\<forall> x m. ( (\<Delta>'\<^sup>V\<^sup>-\<^sup>R) x = \<^sup>R\<bottom>\<^sub>E \<and> (\<Delta>'\<^sup>M\<^sup>-\<^sup>R) m = \<^sup>R\<bottom>\<^sub>M )) \<and>
                        (\<forall> f. (\<Delta>'\<^sup>F\<^sup>-\<^sup>R) f = (\<Delta>\<^sup>F\<^sup>-\<^sup>R) f )"

definition sum_Env_R::"Env_R \<Rightarrow> Env_R \<Rightarrow> Env_R \<Rightarrow> bool" ("_ = _ +\<^sub>\<Delta> _")
 where
  "\<Delta> = \<Delta>\<^sub>1 +\<^sub>\<Delta> \<Delta>\<^sub>2  \<equiv> (\<Delta>\<^sub>1 \<inter>\<^sub>R \<Delta>\<^sub>2 = \<emptyset>) \<and> 
                     (dom(\<Delta>) = dom(\<Delta>\<^sub>1) \<union>\<^sub>R dom(\<Delta>\<^sub>2)) \<and>
                     (\<forall> x. ((\<Delta>\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E \<and> (\<Delta>\<^sub>1\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E)  \<longrightarrow> ((\<Delta>\<^sup>V\<^sup>-\<^sup>R) x = (\<Delta>\<^sub>1\<^sup>V\<^sup>-\<^sup>R) x) ) \<and>
                     (\<forall> x. ((\<Delta>\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E \<and> (\<Delta>\<^sub>2\<^sup>V\<^sup>-\<^sup>R) x \<noteq> \<^sup>R\<bottom>\<^sub>E)  \<longrightarrow> ((\<Delta>\<^sup>V\<^sup>-\<^sup>R) x = (\<Delta>\<^sub>2\<^sup>V\<^sup>-\<^sup>R) x) ) \<and>
                     (\<forall> f. ((\<Delta>\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F \<and> (\<Delta>\<^sub>1\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F)  \<longrightarrow> ((\<Delta>\<^sup>F\<^sup>-\<^sup>R) f = (\<Delta>\<^sub>1\<^sup>F\<^sup>-\<^sup>R) f) ) \<and>
                     (\<forall> f. ((\<Delta>\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F \<and> (\<Delta>\<^sub>2\<^sup>F\<^sup>-\<^sup>R) f \<noteq> \<^sup>R\<bottom>\<^sub>F)  \<longrightarrow> ((\<Delta>\<^sup>F\<^sup>-\<^sup>R) f = (\<Delta>\<^sub>2\<^sup>F\<^sup>-\<^sup>R) f) ) \<and>
                     (\<forall> m. ((\<Delta>\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M \<and> (\<Delta>\<^sub>1\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M)  \<longrightarrow> ((\<Delta>\<^sup>M\<^sup>-\<^sup>R) m = (\<Delta>\<^sub>1\<^sup>M\<^sup>-\<^sup>R) m) ) \<and>
                     (\<forall> m. ((\<Delta>\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M \<and> (\<Delta>\<^sub>2\<^sup>M\<^sup>-\<^sup>R) m \<noteq> \<^sup>R\<bottom>\<^sub>M)  \<longrightarrow> ((\<Delta>\<^sup>M\<^sup>-\<^sup>R) m = (\<Delta>\<^sub>2\<^sup>M\<^sup>-\<^sup>R) m) )" 

definition getStatFutListfromRunFutEnv::"Env_R_fut \<Rightarrow> StaticFuture list"
where
 "getStatFutListfromRunFutEnv \<Delta>\<^sub>f \<equiv> sorted_list_of_set {i\<^sub>f. \<exists> r b. (\<Delta>\<^sub>f) (i\<^sub>f\<^sup>S\<^sup>F) = \<^sup>R(r,b)\<^sub>F} "

primrec getBTfromStatFutList_R:: "Env_R \<Rightarrow> StaticFuture list \<Rightarrow> BehavioralType_R list"
where
 "getBTfromStatFutList_R \<Delta> [] = []" |
 "getBTfromStatFutList_R \<Delta> (f#futList) = get_bt_UncheckedFutureRec_R((\<Delta>\<^sup>F\<^sup>-\<^sup>R) (f\<^sup>S\<^sup>F))#(getBTfromStatFutList_R \<Delta> futList)" 

definition getRunFutListfromRunFutEnv::"Env_R_fut \<Rightarrow> RuntimeFuture \<Rightarrow> StaticFuture list"
where
 "getRunFutListfromRunFutEnv \<Delta>\<^sub>f f \<equiv> sorted_list_of_set {f'. \<exists> r. (\<Delta>\<^sub>f) (f'\<^sup>R\<^sup>F) = \<^sup>R(r,(RunFuture f))\<^sub>F}"

abbreviation unsync_R:: "Env_R \<Rightarrow> BehavioralType_R" ("unsync(_)")
where
 "unsync_R \<Delta> \<equiv> Par(getBTfromStatFutList_R \<Delta> (getStatFutListfromRunFutEnv (\<Delta>\<^sup>F\<^sup>-\<^sup>R)))"

primrec fromRunFutToBTR:: "RuntimeFuture list \<Rightarrow> BehavioralType_R list"
where
 "fromRunFutToBTR [] = []" |
 "fromRunFutToBTR (f#futList) = (RunFuture f) #(fromRunFutToBTR futList)" 
(*
abbreviation getFutBTList:: "Env_R \<Rightarrow> RuntimeFuture \<Rightarrow>  BehavioralType_R list"
where
 "getFutBTList \<Delta> f \<equiv> fromRunFutToBTR (getRunFutListfromRunFutEnv (\<Delta>\<^sup>F\<^sup>-\<^sup>R) f)"

definition rt_unsync:: "Env_R \<Rightarrow> RuntimeFuture \<Rightarrow> BehavioralType_R" ("rt'_unsync'(_, _')")
where
 "rt_unsync(\<Delta>,f) \<equiv> Par((unsync_R \<Delta>) \<parallel>\<parallel> (getFutBTList \<Delta> f))"
*)

abbreviation rt_unsync:: "Env_R \<Rightarrow> BehavioralType_R" ("rt'_unsync'(_')")
where
 "rt_unsync(\<Delta>) \<equiv> Par(getBTfromStatFutList_R \<Delta> (getStatFutListfromRunFutEnv (\<Delta>\<^sup>F\<^sup>-\<^sup>R)))"


(*TR-Val *)
inductive judge_prim_jud_R:: "Env_R \<Rightarrow> Primitive \<Rightarrow> BasicType \<Rightarrow> bool" ("_ \<^sup>R\<turnstile>\<^sub>P _:_")
where "\<Delta> \<^sup>R\<turnstile>\<^sub>P e : _\<^sub>T"

(*TR-Var *)
inductive judge_var_jud:: "Env_R \<Rightarrow> VarOrThis \<Rightarrow> BasicType \<Rightarrow> bool" ("_ \<^sup>R\<turnstile>\<^sub>V _:_")
where "\<lbrakk>(\<Delta>\<^sup>V\<^sup>-\<^sup>R) x = (BasType \<R>)\<rbrakk> \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>V x :\<R>"

(*TR-Fut*)
inductive judge_fut_jud_R:: "Env_R \<Rightarrow> Future \<Rightarrow> FutureRecord_R \<Rightarrow> bool" ("_ \<^sup>R\<turnstile>\<^sub>F _:_")
where "\<lbrakk>(\<Delta>\<^sup>F\<^sup>-\<^sup>R) F = \<Z>\<rbrakk> \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>F F : \<Z>"


inductive judge_config_fut_jud_R::"Env_R \<Rightarrow> (StaticFuture~=>FutValue) \<Rightarrow> BehavioralType_Config \<Rightarrow> bool"  ("_ \<^sup>R\<turnstile>\<^sub>F\<^sub>C _:_")
where
    (*TR-Future*)
    TR_Future  [simp, intro!]: 
      "\<lbrakk>(\<Delta>\<^sup>F\<^sup>-\<^sup>R) (f\<^sup>R\<^sup>F) = \<^sup>R(r,b)\<^sub>F\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>F\<^sub>C Futures(f\<mapsto>Undefined) : 0\<^sub>B\<^sub>T\<^sub>C  " |
    
    (*TR-Future-Tick*)
    TR_Future_Tick  [simp, intro!]: 
      "\<lbrakk>(\<Delta>\<^sup>F\<^sup>-\<^sup>R) (f\<^sup>R\<^sup>F) = \<^sup>R(r,0\<^sub>B\<^sub>T)\<^sup>\<diamond>\<^sub>F (*; 
         \<Delta> \<^sup>R\<turnstile>\<^sub>V val : r*)\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>F\<^sub>C Futures(f\<mapsto>FutVal val) : 0\<^sub>B\<^sub>T\<^sub>C"




(*
inductive judge_config_jud_R::"Env_R \<Rightarrow> ActiveObject \<Rightarrow> BehavioralType_Config \<Rightarrow> bool"  ("_ \<^sup>R\<turnstile>\<^sub>A\<^sub>C _:_")
where
    (*TR-Activity*)
    TR_Activity  [simp, intro!]: 
      "\<lbrakk>\<Delta> \<^sup>R\<turnstile>\<^sub>P  p  : ParConf \<K> ;
        \<Delta> \<^sup>R\<turnstile>\<^sub>R\<^sub>p Rp : ParConf \<K>' \<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>A\<^sub>C AO p Rq : \<K> \<parallel> \<K>' " 
*)


(*Expression with side effects *)
inductive judge_exp_jud_R:: "Env_R \<Rightarrow> MethodName \<Rightarrow> Expression \<Rightarrow> ExtendedType_R \<Rightarrow> BehavioralType_R \<Rightarrow> Env_R \<Rightarrow> bool"  ("_ \<^sup>R\<turnstile>\<^sub>E\<^sup>_ _:_,_|_") 
 where
    (*TR-Exp*)
    TR_Pure [simp, intro!]: 
      "\<lbrakk> \<Delta> \<^sup>R\<turnstile>\<^sub>P e : r\<rbrakk>
      \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m (Val (Prim e)): (BasType r),\<^sup>R0\<^sub>B\<^sub>T | \<Delta> " |
    TR_Exp_Plus [simp, intro!]: 
      "\<lbrakk>\<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m e: (BasType r), b | \<Delta>' ;
        \<Delta>'\<^sup>R\<turnstile>\<^sub>E\<^sup>m e': (BasType r), b' | \<Delta>''\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m (e +\<^sub>A e'): (BasType r), Seq(b;\<^sub>sb') | \<Delta>'' " |
    TR_Exp_And [simp, intro!]: 
      "\<lbrakk>\<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m e: (BasType r), b | \<Delta>' ;
        \<Delta>' \<^sup>R\<turnstile>\<^sub>E\<^sup>m e': (BasType r), b' | \<Delta>''\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m (e &\<^sub>A e') : (BasType r), Seq(b;\<^sub>sb') | \<Delta>'' " |
    TR_Exp_Test [simp, intro!]: 
      "\<lbrakk>\<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m e: (BasType r), b | \<Delta>' ;
        \<Delta>' \<^sup>R\<turnstile>\<^sub>E\<^sup>m e': (BasType r), b' | \<Delta>''\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m (e ==\<^sub>A e'): (BasType r), Seq(b;\<^sub>sb') | \<Delta>'' "  |
    
     (*TR-Sync*)
    TR_Sync [simp, intro!]: 
      "\<lbrakk>\<Delta>\<^sup>V\<^sup>-\<^sup>R x = (Future (StatFut i\<^sub>f));
        r = (\<alpha>'..m'\<leadsto>r') ;         
        \<Delta> \<^sup>R\<turnstile>\<^sub>F (StatFut i\<^sub>f) : \<^sup>R(r, b)\<^sub>F ;
        \<Delta> \<^sup>R\<turnstile>\<^sub>V this : (Obj [\<alpha>]\<^sub>O);
        \<Delta>'= (\<Delta>[(StatFut i\<^sub>f) \<rightarrow>\<^sub>R (\<^sup>R(r,0\<^sub>B\<^sub>T)\<^sup>\<diamond>\<^sub>F)]\<^sub>F) \<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m (Var x) : (BasType r'), Par((b.\<^sub>s\<^sub>R(\<alpha>..m,\<alpha>'..m')) \<parallel> rt_unsync(\<Delta>)) | (\<Delta>') " |   
    
     (*TR-Sync-Runtime*)
    TR_Sync_Runtime [simp, intro!]: 
      "\<lbrakk>\<Delta>\<^sup>V\<^sup>-\<^sup>R x = (Future (RunFut f));         
        r = (\<alpha>'..m'\<leadsto>r');
        \<Delta> \<^sup>R\<turnstile>\<^sub>F (RunFut f) : \<^sup>R(r, b)\<^sub>F ;
        \<Delta> \<^sup>R\<turnstile>\<^sub>V this : (Obj [\<alpha>]\<^sub>O);
        \<Delta>'= (\<Delta>[(RunFut f) \<rightarrow>\<^sub>R (\<^sup>R(r,0\<^sub>B\<^sub>T)\<^sup>\<diamond>\<^sub>F)]\<^sub>F)\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m (Var x) : (BasType r'), Par(((RunFuture f).\<^sub>s\<^sub>R(\<alpha>..m,\<alpha>'..m')) \<parallel> rt_unsync(\<Delta>)) | (\<Delta>') " |   

     (*TR-Value-Tick*)
    TR_Value_Tick [simp, intro!]: 
      "\<lbrakk>\<Delta>\<^sup>V\<^sup>-\<^sup>R x = (Future F);
        r = (\<alpha>..m\<leadsto>r');
        \<Delta> \<^sup>R\<turnstile>\<^sub>F F : \<^sup>R(r,0\<^sub>B\<^sub>T)\<^sup>\<diamond>\<^sub>F \<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m (Var x) : (BasType r'), \<^sup>R0\<^sub>B\<^sub>T | \<Delta> "      

(*Statements*)
inductive judge_stmt_jud_R:: "Env_R \<Rightarrow> MethodName \<Rightarrow> Statement \<Rightarrow> BehavioralType_R \<Rightarrow> Env_R \<Rightarrow> bool"  ("_ \<^sup>R\<turnstile>\<^sub>S\<^sup>_ _:_|_") 
and judge_stmtlist_jud_R:: "Env_R \<Rightarrow> MethodName \<Rightarrow> Statement list \<Rightarrow> BehavioralType_R \<Rightarrow> Env_R \<Rightarrow> bool"  ("_ \<^sup>R\<turnstile>\<^sub>S\<^sub>l\<^sup>_ _:_|_") 
 where

    (*TR-Alias*)
    TR_Alias  [simp, intro!]: 
      "\<lbrakk>(\<Delta>\<^sup>V\<^sup>-\<^sup>R) y = (Future F);
        \<Delta>'= (\<Delta>[(Variable x) \<rightarrow>\<^sub>R (Future F)]\<^sub>V)\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sup>m x =\<^sub>A (Expr (Var y)) : \<^sup>R0\<^sub>B\<^sub>T | \<Delta>' " |
  
     (*TR-Expression*)
     T_Expression [simp, intro!]:
      "\<lbrakk> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m e : (BasType r), b | \<Delta>'; 
         \<Delta>'= (\<Delta>[(Variable x) \<rightarrow>\<^sub>R (BasType r)]\<^sub>V)\<rbrakk>
       \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sup>m x =\<^sub>A (Expr e) : b | \<Delta>' " | 
     
     (*TR-NewActive*)
     TR_NewActive [simp, intro!]:
      "\<lbrakk>fresh_act_R \<Delta> \<alpha>;
        \<Delta>'= (\<Delta>[(Variable x) \<rightarrow>\<^sub>R (BasType (Obj [\<alpha>]\<^sub>O))]\<^sub>V)\<rbrakk>
      \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sup>m x =\<^sub>A newActive() : \<^sup>R0\<^sub>B\<^sub>T | \<Delta>'" |    
 
     (*TR-Invk*)
     TR_Invk [simp, intro!]:
      "\<lbrakk> \<Delta> \<^sup>R\<turnstile>\<^sub>V (This) : (Obj [\<alpha>]\<^sub>O);
        \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m e : (BasType (Obj [\<alpha>']\<^sub>O)), b | \<Delta>' ;
        (*typing parameters*)
        length parType = length el ; 
        \<forall> i<length el. \<exists> bt \<Delta>t. (\<Delta>' \<^sup>R\<turnstile>\<^sub>E\<^sup>m (el!i) : (snd (parType!i)), bt | \<Delta>t );
        (*                  *)
        
        (* apply sobstitution
        (\<Delta>'\<^sup>M) m' = ([\<alpha>'']\<^sub>O,parType){\<langle>b\<^sub>1,b\<^sub>2\<rangle>}\<^sub>R r'; *)
        (\<Delta>'\<^sup>M\<^sup>-\<^sup>R) m' = ([\<alpha>']\<^sub>O,parType){\<langle>b\<^sub>1,b\<^sub>2\<rangle>}\<^sub>R r'; 
        fresh_StatFut_R \<Delta>' i\<^sub>f ;
        r = (\<alpha>'..m'\<leadsto>r');        
        b\<^sub>3 = (m'((Obj [\<alpha>']\<^sub>O) , map snd parType)\<rightarrow>\<^sub>Rr');
        \<Delta>''= (\<Delta>'[(StatFut i\<^sub>f) \<rightarrow>\<^sub>R \<^sup>R(r, b\<^sub>3)\<^sub>F]\<^sub>F)\<rbrakk>
       \<Longrightarrow> \<Delta>' \<^sup>R\<turnstile>\<^sub>S\<^sup>m (x=\<^sub>Ae.\<^sub>Am'(el)) : Seq(b ;\<^sub>s Par(b\<^sub>3 \<parallel> rt_unsync(\<Delta>'))) | \<Delta>' " |
   
     (*T-Return*)
     T_Return [simp, intro!]:
      "\<lbrakk> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m e : (BasType r) , b | \<Delta>'\<rbrakk>
      \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sup>m (return e) : \<^sup>R0\<^sub>B\<^sub>T | \<Delta> "  |
   
     (*T-If*) 
     T_If [simp, intro!]:
     "\<lbrakk> \<Delta> \<^sup>R\<turnstile>\<^sub>E\<^sup>m cond : BasType _\<^sub>T , b | \<Delta>' ;
       \<Delta>' \<^sup>R\<turnstile>\<^sub>S\<^sub>l\<^sup>m sl\<^sub>1 : b\<^sub>1 | \<Delta>\<^sub>1 ;
       \<Delta>' \<^sup>R\<turnstile>\<^sub>S\<^sub>l\<^sup>m sl\<^sub>2 : b\<^sub>2 | \<Delta>\<^sub>2 ;
       compare_Env_R \<Delta>' \<Delta>\<^sub>1 \<Delta>\<^sub>2 ;  (*\<And>\<^sub>x\<^sub>\<in>\<^sub>d\<^sub>o\<^sub>m\<^sub>(\<^sub>\<Gamma>\<^sub>) \<Delta>\<^sub>1(x) = \<Delta>\<^sub>2(x)*)
       (\<forall>x f' f''. (\<exists> f .(((\<Delta>\<^sup>V\<^sup>-\<^sup>R) x) = (Future f)) \<longrightarrow> ((\<Delta>\<^sub>1\<^sup>V\<^sup>-\<^sup>R) x = (Future f') \<and> (\<Delta>\<^sub>2\<^sup>V\<^sup>-\<^sup>R) x = (Future f''))) 
                           \<longrightarrow> (\<Delta>\<^sub>1\<^sup>F\<^sup>-\<^sup>R) f' = (\<Delta>\<^sub>2\<^sup>F\<^sup>-\<^sup>R) f''); (*f = f' because of compare_\<Gamma>*)
                           (*\<up> \<And>\<^sub>x\<^sub>\<in>\<^sub>F\<^sub>u\<^sub>t\<^sub>(\<^sub>\<Gamma>\<^sub>) \<Gamma>\<^sub>1(\<Gamma>\<^sub>1(x)) = \<Gamma>\<^sub>2(\<Gamma>\<^sub>2(x)) *)
       \<Delta>\<^sub>2\<^sub>F = \<Delta>\<^sub>2|\<^sub>F\<^sub>R ; 
       \<Delta>' =  \<Delta>\<^sub>1 +\<^sub>\<Delta> \<Delta>\<^sub>2\<^sub>F\<rbrakk>
      \<Longrightarrow>  \<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sup>m IF cond THEN sl\<^sub>1 ELSE sl\<^sub>2 : Par(b\<^sub>1\<parallel>b\<^sub>2) | \<Delta>'" | 
 
    (*T-Seq*)
    T_Seq [simp, intro!]:
      "\<lbrakk>\<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sup>m s : b | \<Delta>' ;
        \<Delta>' \<^sup>R\<turnstile>\<^sub>S\<^sub>l\<^sup>m sl' : b' | \<Delta>'' \<rbrakk>
      \<Longrightarrow> \<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sub>l\<^sup>m s;;sl' : Seq(b;\<^sub>sb') | \<Delta>'' " |       
    T_EmptyList [simp, intro!]:
      " \<Delta> \<^sup>R\<turnstile>\<^sub>S\<^sub>l\<^sup>m [] : \<^sup>R0\<^sub>B\<^sub>T | \<Delta> " 

end
