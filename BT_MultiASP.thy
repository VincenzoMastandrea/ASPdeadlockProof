(*  Title:      BT_MultiASP.thy
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
theory BT_MultiASP imports Main SimpleMultiASP AuxiliaryFunctions begin

datatype Primitive = ASPInt | ASPBool

datatype Object = ActRef ActName  ("'[_']\<^sub>O")

datatype DepPair = DependencyPair ActName MethodName ActName MethodName ("'(_.._,_.._')")

subsection {*Behavioral Type Syntax *}
datatype BasicType =   NullType ("'_\<^sub>T")
                       | Prm Primitive     (*_*) 
                       | Obj Object        (*[\<alpha>]*)
                       | Control ActName MethodName  BasicType  ("_.._\<leadsto>_") (*\<alpha>.m\<leadsto>r *)

datatype BehavioralType =  BTNull  ("0\<^sub>B\<^sub>T")
                          | MethodCall MethodName BasicType "BasicType list" BasicType ("_'(_,_')\<rightarrow>_") 
                          | SyncPoint  BehavioralType DepPair ("_.\<^sub>s_")
                          | Par        BehavioralType BehavioralType   ("_\<parallel>_")
                          | Seq        BehavioralType BehavioralType   ("_;\<^sub>s_")

datatype BTMethod = BTMet ActName "(VarName*BasicType) list" BehavioralType BehavioralType BasicType   ("'(_,_')'{\<langle>_,_'\<rangle>}_")

datatype BTClass = BTCl "MethodName => BehavioralType"

datatype BTProgram = BTProg BTClass BehavioralType BehavioralType


datatype ExtendedType = Rec BasicType | Future FutName

datatype FutureRecord = Unchecked  BasicType BehavioralType ("'(_,_')\<^sub>F")
                      | Checked    BasicType ("'(_,0\<^sub>B\<^sub>T')\<^sup>\<diamond>\<^sub>F")

subsection {*Typing Rules *}

record Environment = 
Env_Variable::   "VarName => ExtendedType" 
Env_Primitive::   "Expression => BasicType"
Env_Expression:: "Expression => (BasicType * BehavioralType)"
Env_Future:: "FutName => FutureRecord"
Env_Stmt:: "Statement => BehavioralType"
Env_Method:: "Method => BTMethod"
Env_Class:: "BTClass"
Env_Program:: "BTProgram"


abbreviation Type_Var:: "Environment\<Rightarrow>VarName\<Rightarrow>ExtendedType"
where "Type_Var \<Gamma> v\<equiv> (Env_Variable \<Gamma>) v"

abbreviation Type_Exp:: "Environment\<Rightarrow>Expression\<Rightarrow>BasicType"
where "Type_Exp \<Gamma> e\<equiv> fst((Env_Expression \<Gamma>) e)"

abbreviation BT_Exp:: "Environment\<Rightarrow>Expression\<Rightarrow>BehavioralType"
where "BT_Exp \<Gamma> e\<equiv> snd((Env_Expression \<Gamma>) e)"

abbreviation Type_Fut:: "Environment\<Rightarrow>FutName\<Rightarrow>FutureRecord"
where "Type_Fut \<Gamma> f\<equiv> (Env_Future \<Gamma>) f"

abbreviation BT_Stmt:: "Environment\<Rightarrow>Statement\<Rightarrow>BehavioralType"
where "BT_Stmt \<Gamma> stmt\<equiv> (Env_Stmt \<Gamma>) stmt"

abbreviation BT_Met:: "Environment\<Rightarrow>Method\<Rightarrow>BTMethod"
where "BT_Met \<Gamma> met\<equiv> (Env_Method \<Gamma>) met"

abbreviation BT_Class:: "Environment\<Rightarrow>BTClass"
where "BT_Class \<Gamma>\<equiv> (Env_Class \<Gamma>)"

abbreviation BT_Prog:: "Environment\<Rightarrow>BTProgram"
where "BT_Prog \<Gamma>\<equiv> (Env_Program \<Gamma>)"

datatype Types = ET ExtendedType 
               | FR FutureRecord 
               | BT BehavioralType
               | ET_BT "ExtendedType * BehavioralType"

datatype Terms = VarN VarName
               | Val Primitive 
               | PR Program 
               | Cl Class 
               | Met Method 
               | Fut FutName 
               | St Statement 
               | Stl "Statement list"
               | ExS Rhs
               | Exp Expression
(*
abbreviation upd_record_fun:: "'a\<Rightarrow> ident \<Rightarrow> 'b \<Rightarrow> 'g \<Rightarrow> 'e"
where
"upd_record_map rec field x y \<equiv> rec\<lparr>field:=(rec field)(x:=y)\<rparr>"
*)
definition fresh_act:: "Environment \<Rightarrow> ActName \<Rightarrow> bool"
 where
  "fresh_act \<Gamma> \<alpha> \<equiv> (\<forall> x \<gamma>. (Env_Variable \<Gamma>) x = Rec(Obj [\<gamma>]\<^sub>O) \<longrightarrow> \<gamma> \<noteq> \<alpha> )"   

definition fresh_fut:: "Environment \<Rightarrow> FutName \<Rightarrow> bool"
 where
  "fresh_fut \<Gamma> f \<equiv> (\<forall> x f'. (Env_Variable \<Gamma>) x = (Future f') \<longrightarrow> f' \<noteq> f )"   



inductive typing:: "Environment \<Rightarrow> MethodName \<Rightarrow> Terms \<Rightarrow> Types \<Rightarrow> Environment \<Rightarrow> bool" ("_ \<turnstile>\<^sub>__:_'|_")
  where
    (*Expression and adresses *)
    T_Var [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Rec r)\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>m (VarN x) : (ET(Rec r)) | \<Gamma> " |
    T_Fut [simp, intro!]: 
      "\<lbrakk>(Type_Fut \<Gamma> f) =   z\<rbrakk> \<Longrightarrow>   \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR z) | \<Gamma> " |
    T_Val [simp, intro!]: 
      " \<Gamma> \<turnstile>\<^sub>m (Val e) : (ET(Rec _\<^sub>T)) | \<Gamma>" |

    (*Expression with side effects *)
    T_Pure [simp, intro!]: 
      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>m (VarN e) : (ET(Rec r)) | \<Gamma>
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (VarN e) : (ET_BT((Rec r), 0\<^sub>B\<^sub>T)) | \<Gamma> " |
     T_Exp_Plus [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec r), b) | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : ET_BT((Rec r), b') | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e +\<^sub>A e')) : ET_BT((Rec r), (b;\<^sub>sb')) | \<Gamma>'' " |
     T_Exp_And [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec r), b) | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : ET_BT((Rec r), b') | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e &\<^sub>A e')) : ET_BT((Rec r), (b;\<^sub>sb')) | \<Gamma>'' " |
     T_Exp_Test [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec r), b) | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : ET_BT((Rec r), b') | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e ==\<^sub>A e')) : ET_BT((Rec r), (b;\<^sub>sb')) | \<Gamma>'' " |  
     T_Sync [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Future f); 
        \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR fut_rec) | \<Gamma> ;
        fut_rec_uncheked = (Unchecked r b);
        r = (\<alpha>'..m'\<leadsto>r');
        \<Gamma> \<turnstile>\<^sub>m this : (ET (Rec (Obj [\<alpha>]\<^sub>O))) | \<Gamma> ;
        fut_rec_cheked = (Checked r);
        \<Gamma>'= \<Gamma>\<lparr>Env_Future := (Env_Future \<Gamma>)(f := fut_rec_checked)\<rparr>
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (VarN x) : (ET_BT((Rec r'), (b.\<^sub>s(\<alpha>..m,\<alpha>'..m')) \<parallel> Unsync)) | (\<Gamma>') " | 
     T_Value_Tick [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Future f); 
        \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR fut_rec) | \<Gamma> ;
        fut_rec = (Checked r);
        r = (\<alpha>..m\<leadsto>r')
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (VarN x) : (ET_BT((Rec r'), 0\<^sub>B\<^sub>T)) | \<Gamma> " | 
     
     (*Statements *)       
     T_Alias  [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> y) = (Future f) ;
        S = (x =\<^sub>A Expr(Var y)) ;
        \<Gamma>'= \<Gamma>\<lparr>Env_Variable := (Env_Variable \<Gamma>)(x := (Future f))\<rparr>
      \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(0\<^sub>B\<^sub>T) | \<Gamma>' " |
     
     T_Var_Expression [simp, intro!]:
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec r), b) | \<Gamma>' ;
       S = (x =\<^sub>A (Expr e)) ;
       \<Gamma>''= \<Gamma>\<lparr>Env_Variable := (Env_Variable \<Gamma>)(x := (Rec r))\<rparr> 
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(b) | \<Gamma>'' " |
     
     T_NewActive [simp, intro!]:
      "\<lbrakk>S = (x =\<^sub>A newActive()) ;
        fresh_act \<Gamma> \<alpha> ;
        \<Gamma>'= \<Gamma>\<lparr>Env_Variable := (Env_Variable \<Gamma>)(x := (Rec (Obj [\<alpha>]\<^sub>O)))\<rparr> 
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(0\<^sub>B\<^sub>T) | \<Gamma>' " | 
     
     T_Invk [simp, intro!]:
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m this : (ET (Rec (Obj [\<alpha>]\<^sub>O))) | \<Gamma> ;
        \<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec (Obj [\<alpha>]\<^sub>O)), b) | \<Gamma>' ;
        m' = MName met;
        \<Gamma> \<turnstile>\<^sub>m (Met met) : BT(m'((Obj [\<alpha>]\<^sub>O) , parType)\<rightarrow>r') | \<Gamma>' ;
        S = (x=\<^sub>Ae.\<^sub>Am(el)) ;
        fresh_fut \<Gamma> f ;
        \<Gamma>''= \<Gamma>'\<lparr>Env_Future := (Env_Future \<Gamma>)(f := (r, b)\<^sub>F )\<rparr> 
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(0\<^sub>B\<^sub>T) | \<Gamma>' "

     
      
     
        
(*    
   T_Value [simp, intro!]: 
      "\<lbrakk> (fut_rec = (Checked t)\<or>fut_rec = (Unchecked t B));
         \<Gamma> \<turnstile> (Var e) : (ET (Future f)) | \<Gamma>;
         \<Gamma> \<turnstile> (Fut f) : (FR fut_rec) | \<Gamma>     
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var e) : (ET(Rec t)) | \<Gamma>" |
*)










