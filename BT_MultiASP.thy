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
                          | SyncPoint  MethodName BasicType "BasicType list" BasicType DepPair ("_'(_,_')\<rightarrow> _._")
                          | Par        BehavioralType BehavioralType   ("_\<parallel>_")
                          | Seq        BehavioralType BehavioralType   ("_;\<^sub>s_")

datatype BTMethod = BTMet ActName "(VarName*BasicType) list" BehavioralType BehavioralType BasicType   ("'(_,_')'{\<langle>_,_'\<rangle>}_")

datatype BTClass = BTCl "MethodName => BehavioralType"

datatype BTProgram = BTProg BTClass BehavioralType BehavioralType


datatype ExtendedType = Rec BasicType | Future FutName

datatype FutureRecord = Unchecked  BasicType BehavioralType ("'(_,_')\<^sub>F")
                      | Checked    BasicType ("'(_,0\<^sub>B\<^sub>T')\<^sub>F")

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

datatype Types =  ET ExtendedType 
               | FR FutureRecord 
               | BT BehavioralType
               | ET_BT "ExtendedType * BehavioralType"

datatype Terms = Var VarName
               | Val Primitive 
               | PR Program 
               | Cl Class 
               | Met Method 
               | Fut FutName 
               | St Statement 
               | ExS Rhs
               | Exp Expression

inductive typing:: "Environment \<Rightarrow> MethodName \<Rightarrow> Terms \<Rightarrow> Types \<Rightarrow> Environment \<Rightarrow> bool" ("_ \<turnstile>\<^sub>__:_'|_")
  where
    T_Var [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Rec r)\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>m (Var x) : (ET(Rec r)) | \<Gamma>" |
    T_Fut [simp, intro!]: 
      "\<lbrakk>(Type_Fut \<Gamma> f) =   z\<rbrakk> \<Longrightarrow>   \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR z) | \<Gamma>" |
    T_Val [simp, intro!]: 
      " \<Gamma> \<turnstile>\<^sub>m (Val e) : (ET(Rec _\<^sub>T)) | \<Gamma>" |
    T_Pure [simp, intro!]: 
      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>m (Var e) : (ET(Rec r)) | \<Gamma>
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Var e) : (ET_BT((Rec r), 0\<^sub>B\<^sub>T)) | \<Gamma>" |
     T_Exp_Plus [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec r), b) | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : ET_BT((Rec r), b') | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e +\<^sub>A e')) : ET_BT((Rec r), (b;\<^sub>sb')) | \<Gamma>''" |
     T_Exp_And [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec r), b) | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : ET_BT((Rec r), b') | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e &\<^sub>A e')) : ET_BT((Rec r), (b;\<^sub>sb')) | \<Gamma>''" |
     T_Exp_Test [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : ET_BT((Rec r), b) | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : ET_BT((Rec r), b') | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e ==\<^sub>A e')) : ET_BT((Rec r), (b;\<^sub>sb')) | \<Gamma>''" |  
     T_Sync [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Future f); 
        \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR fut_rec) | \<Gamma> ;
        fut_rec_uncheked = Unchecked r b;
        r = (\<alpha>'..m'\<leadsto>r');
        \<Gamma> \<turnstile>\<^sub>m this : (ET (Rec (Obj [\<alpha>]\<^sub>O))) | \<Gamma> ;
        fut_rec_cheked = Checked r;
        \<Gamma>'= (Env_Future \<Gamma>)(f \<mapsto> fut_rec_checked)
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Var x) : (ET_BT((Rec r'), 0\<^sub>B\<^sub>T)) | \<Gamma>" |  
     T_Value_Tick [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Future f); 
        \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR fut_rec) | \<Gamma> ;
        fut_rec = (Checked r);
        r = (\<alpha>..m\<leadsto>r')
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Var x) : (ET_BT((Rec r'), 0\<^sub>B\<^sub>T)) | \<Gamma>" 
            
        
      
     
        
(*    


     

    T_Value [simp, intro!]: 
      "\<lbrakk> (fut_rec = (Checked t)\<or>fut_rec = (Unchecked t B));
         \<Gamma> \<turnstile> (Var e) : (ET (Future f)) | \<Gamma>;
         \<Gamma> \<turnstile> (Fut f) : (FR fut_rec) | \<Gamma>     
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var e) : (ET(Rec t)) | \<Gamma>" |
*)










