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

datatype Primitive = ASPInt int | ASPBool bool

datatype DepPair = DependencyPair ActName MethodName ActName MethodName ("'(_.._,_.._')")

subsection {*Behavioral Type Syntax *}
datatype BasicType = Prm Primitive ("'_\<^sub>T")    (*_*) 
                   | Obj ActName    ("'[_']\<^sub>O")    (*[\<alpha>]*)
                   | Control ActName MethodName  BasicType  ("_.._\<leadsto>_") (*\<alpha>.m\<leadsto>r *)

datatype ExtendedType =  NullType        ("\<bottom>") 
                      |Rec BasicType 
                      | Future FutName

datatype BehavioralType =  BTNull  ("0\<^sub>B\<^sub>T")
                          | MethodCall MethodName BasicType "BasicType list" BasicType ("_'(_,_')\<rightarrow>_") 
                          | SyncPoint  BehavioralType DepPair ("_.\<^sub>s_")
                          | Par        BehavioralType BehavioralType   ("_\<parallel>_")
                          | Seq        BehavioralType BehavioralType   ("_;\<^sub>s_")

datatype FutureRecord = Unchecked  BasicType BehavioralType ("'(_,_')\<^sub>F")
                      | Checked    BasicType ("'(_,0\<^sub>B\<^sub>T')\<^sup>\<diamond>\<^sub>F")


datatype BTMethod = BTMet ActName "(VarName*BasicType) list" BehavioralType BehavioralType BasicType   ("'(_,_')'{\<langle>_,_'\<rangle>}_")

datatype BTClass = BTCl "MethodName => BehavioralType"

datatype BTProgram = BTProg BTClass BehavioralType BehavioralType

subsection {*Typing Rules *}

type_synonym \<Gamma>\<^sub>v = "VarName => ExtendedType"
type_synonym \<Gamma>\<^sub>f = "FutName => FutureRecord"
type_synonym \<Gamma>\<^sub>m = "Method => BTMethod"
datatype \<Gamma> = \<Gamma>\<^sub>v \<Gamma>\<^sub>f \<Gamma>\<^sub>m

record Environment = 
Env_Variable::   "VarName => ExtendedType" 
Env_Primitive::   "Primitive => BasicType"
Env_Expression:: "Expression => (BasicType * BehavioralType)"
Env_Future:: "FutName => FutureRecord"
Env_Stmt:: "Statement => BehavioralType"
Env_Method:: "Method => BTMethod"
Env_Class:: "BTClass"
Env_Program:: "BTProgram"

abbreviation Type_Var:: "Environment\<Rightarrow>VarName\<Rightarrow>ExtendedType"
where "Type_Var \<Gamma> v\<equiv> (Env_Variable \<Gamma>) v"

abbreviation Type_Prim:: "Environment\<Rightarrow>Primitive\<Rightarrow>BasicType"
where "Type_Prim \<Gamma> e\<equiv> (Env_Primitive \<Gamma>) e"

abbreviation Type_BT_Exp:: "Environment\<Rightarrow>Expression\<Rightarrow>(BasicType * BehavioralType)"
where "Type_BT_Exp \<Gamma> e\<equiv> (Env_Expression \<Gamma>) e"

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

datatype Type = ET ExtendedType 
               | FR FutureRecord 
               | BT BehavioralType
               | ET_BT BasicType  BehavioralType ( "'(_,_')\<^sub>B\<^sub>T")
               | BTM BTMethod

datatype Type2 = None | T Type

datatype Term = VarN VarName      (*\<rightarrow>  ExtendedType *)
               | Val Primitive     (*\<rightarrow>  ExtendedType(Rec(Prm )) *)
               | PR Program        (*\<rightarrow>  BehavioralType *)
               | Cl Class          (*\<rightarrow>  BehavioralType *)
               | Met Method        (*\<rightarrow>  BehavioralType *)
               | Fut FutName       (*\<rightarrow>  FutureRecord *) 
               | St Statement      (*\<rightarrow>  BehavioralType *)
               | Stl "Statement list"    
               | Exp Expression    (*\<rightarrow>  ExtendedType  BehavioralType *)


primrec Gamma_of_x:: "Environment \<Rightarrow>Term \<Rightarrow> Type2"
where 
  "Gamma_of_x \<Gamma> (VarN v) = T(ET(Type_Var \<Gamma> v))" |
  "Gamma_of_x \<Gamma> (Val v) = T(ET(Rec (Type_Prim \<Gamma> v)))" |
  "Gamma_of_x \<Gamma> (Fut f) = T(FR(Type_Fut \<Gamma> f))" |
  "Gamma_of_x \<Gamma> (St s) = T(BT((BT_Stmt \<Gamma> s)))" |
  "Gamma_of_x \<Gamma> (Exp e) = T(((Type_Exp \<Gamma> e),(BT_Exp \<Gamma> e))\<^sub>B\<^sub>T)" |
  "Gamma_of_x \<Gamma> (Met m) = T(BTM(BT_Met \<Gamma> m))" |
  "Gamma_of_x \<Gamma> (Stl sl) = None" |
  "Gamma_of_x \<Gamma> (PR p) = None" |
  "Gamma_of_x \<Gamma> (Cl c) = None" 
  

  
(*
abbreviation upd_record_fun:: "'a\<Rightarrow> ident \<Rightarrow> 'b \<Rightarrow> 'g \<Rightarrow> 'e"
where
"upd_record_map rec field x y \<equiv> rec\<lparr>field:=(rec field)(x:=y)\<rparr>"
*)
definition fresh_act
 where
  "fresh_act \<Gamma> \<alpha> \<equiv> (\<forall> x \<gamma>. (Env_Variable \<Gamma>) x = Rec([\<gamma>]\<^sub>O) \<longrightarrow> \<gamma> \<noteq> \<alpha> )"   

definition fresh_fut
 where
  "fresh_fut \<Gamma> f \<equiv> (\<forall> x f'. (Env_Variable \<Gamma>) x = (Future f') \<longrightarrow> f' \<noteq> f )"   

definition compare_\<Gamma>_each_x 
 where
  "compare_\<Gamma>_each_x \<Gamma> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<equiv> \<forall> x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4 x\<^sub>5 x\<^sub>6 . (
                            (\<exists> y . (Env_Variable \<Gamma>) x\<^sub>1 = y \<longrightarrow> (Env_Variable \<Gamma>\<^sub>1) x\<^sub>1 = (Env_Variable \<Gamma>\<^sub>2) x\<^sub>1) \<and> 
                            (\<exists> y . (Env_Primitive  \<Gamma>) x\<^sub>2 = y \<longrightarrow> (Env_Primitive \<Gamma>\<^sub>1)  x\<^sub>2 = (Env_Primitive \<Gamma>\<^sub>2) x\<^sub>2) \<and> 
                            (\<exists> y . (Env_Expression  \<Gamma>) x\<^sub>3 = y \<longrightarrow> (Env_Expression \<Gamma>\<^sub>1) x\<^sub>3 = (Env_Expression \<Gamma>\<^sub>2) x\<^sub>3) \<and>
                            (\<exists> y . (Env_Future  \<Gamma>) x\<^sub>4 = y \<longrightarrow> (Env_Future \<Gamma>\<^sub>1)  x\<^sub>4 = (Env_Future \<Gamma>\<^sub>2)  x\<^sub>4) \<and>
                            (\<exists> y . (Env_Stmt  \<Gamma>) x\<^sub>5 = y \<longrightarrow> (Env_Stmt \<Gamma>\<^sub>1) x\<^sub>5 = (Env_Stmt \<Gamma>\<^sub>2) x\<^sub>5) \<and>
                            (\<exists> y . (Env_Method  \<Gamma>) x\<^sub>6 = y \<longrightarrow> (Env_Method \<Gamma>\<^sub>1) x\<^sub>6 = (Env_Method \<Gamma>\<^sub>2) x\<^sub>6) \<and>
                            (\<exists> y . (Env_Class  \<Gamma>) = y \<longrightarrow> (Env_Class \<Gamma>\<^sub>1) = (Env_Class \<Gamma>\<^sub>2))  \<and>
                            (\<exists> y . (Env_Program  \<Gamma>) = y \<longrightarrow> (Env_Program \<Gamma>\<^sub>1) = (Env_Program \<Gamma>\<^sub>2)))"


definition sum_\<Gamma> 
 where
  "sum_\<Gamma> \<Gamma>' \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<equiv> \<forall> x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4 x\<^sub>5 x\<^sub>6 . (
                            ( (Env_Variable \<Gamma>')   x\<^sub>1 = (Env_Variable \<Gamma>\<^sub>1)   x\<^sub>1
                              \<or> (Env_Variable \<Gamma>')   x\<^sub>1 = (Env_Variable \<Gamma>\<^sub>2)   x\<^sub>1) \<and> 
                            ( (Env_Primitive \<Gamma>')  x\<^sub>2 = (Env_Primitive \<Gamma>\<^sub>1)  x\<^sub>2 
                              \<or> (Env_Primitive \<Gamma>')  x\<^sub>2 = (Env_Primitive \<Gamma>\<^sub>2)  x\<^sub>2) \<and> 
                            ( (Env_Expression \<Gamma>') x\<^sub>3 = (Env_Expression \<Gamma>\<^sub>1) x\<^sub>3 
                              \<or> (Env_Expression \<Gamma>') x\<^sub>3 = (Env_Expression \<Gamma>\<^sub>2) x\<^sub>3) \<and>
                            ( (Env_Future \<Gamma>')  x\<^sub>4 = (Env_Future \<Gamma>\<^sub>1)  x\<^sub>4 
                              \<or> (Env_Future \<Gamma>')  x\<^sub>4 = (Env_Future \<Gamma>\<^sub>2)  x\<^sub>4 ) \<and>
                            ( (Env_Stmt \<Gamma>')    x\<^sub>5 = (Env_Stmt \<Gamma>\<^sub>1)    x\<^sub>5 
                              \<or> (Env_Stmt \<Gamma>')    x\<^sub>5 = (Env_Stmt \<Gamma>\<^sub>2)    x\<^sub>5) \<and>
                            ( (Env_Method \<Gamma>')  x\<^sub>6 = (Env_Method \<Gamma>\<^sub>1)  x\<^sub>6 
                              \<or> (Env_Method \<Gamma>')  x\<^sub>6 = (Env_Method \<Gamma>\<^sub>2)  x\<^sub>6) \<and>
                            ((Env_Class \<Gamma>') = (Env_Class \<Gamma>\<^sub>1) \<and> (Env_Class \<Gamma>') = (Env_Class \<Gamma>\<^sub>2))  \<and>
                            ((Env_Program \<Gamma>') = (Env_Program \<Gamma>\<^sub>1) \<and> (Env_Program \<Gamma>') = (Env_Program \<Gamma>\<^sub>2)) )"



inductive typing:: "Environment \<Rightarrow> MethodName \<Rightarrow> Term \<Rightarrow> Type \<Rightarrow> Environment \<Rightarrow> bool" ("_ \<turnstile>\<^sub>__:_'|_")
  where
    (*Expression and adresses *)
    T_Var [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Rec r)\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>m (VarN x) : (ET(Rec r)) | \<Gamma> " |
    T_Fut [simp, intro!]: 
      "\<lbrakk>(Type_Fut \<Gamma> f) =   z\<rbrakk> \<Longrightarrow>   \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR z) | \<Gamma> " |
    T_Val [simp, intro!]: 
      "\<lbrakk>(Type_Prim \<Gamma> e) =   z\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>m (Val e) : (ET(Rec z)) | \<Gamma> " |

    (*Expression with side effects *)
    T_Pure [simp, intro!]: 
      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>m (VarN e) : (ET(Rec r)) | \<Gamma>
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (VarN e) : (r, 0\<^sub>B\<^sub>T)\<^sub>B\<^sub>T | \<Gamma> " |
     T_Exp_Plus [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : (r, b)\<^sub>B\<^sub>T | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : (r, b')\<^sub>B\<^sub>T | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e +\<^sub>A e')) : (r, (b;\<^sub>sb'))\<^sub>B\<^sub>T | \<Gamma>'' " |
     T_Exp_And [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : (r, b)\<^sub>B\<^sub>T | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : (r, b')\<^sub>B\<^sub>T | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e &\<^sub>A e')) : (r, (b;\<^sub>sb'))\<^sub>B\<^sub>T | \<Gamma>'' " |
     T_Exp_Test [simp, intro!]: 
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : (r, b)\<^sub>B\<^sub>T | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Exp e') : (r, b')\<^sub>B\<^sub>T | \<Gamma>'' 
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Exp (e ==\<^sub>A e')) : (r, (b;\<^sub>sb'))\<^sub>B\<^sub>T | \<Gamma>'' " |  
     T_Sync [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Future f); 
        \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR fut_rec) | \<Gamma> ;
        fut_rec_uncheked = (Unchecked r b);
        r = (\<alpha>'..m'\<leadsto>r');
        \<Gamma> \<turnstile>\<^sub>m this : (ET (Rec ([\<alpha>]\<^sub>O))) | \<Gamma> ;
        fut_rec_cheked = (Checked r);
        \<Gamma>'= \<Gamma>\<lparr>Env_Future := (Env_Future \<Gamma>)(f := fut_rec_checked)\<rparr>
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (VarN x) : ( r', (b.\<^sub>s(\<alpha>..m,\<alpha>'..m')) \<parallel> Unsync)\<^sub>B\<^sub>T | (\<Gamma>') " | 
     T_Value_Tick [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> x) = (Future f); 
        \<Gamma> \<turnstile>\<^sub>m (Fut f) : (FR fut_rec) | \<Gamma> ;
        fut_rec = (Checked r);
        r = (\<alpha>..m\<leadsto>r')
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (VarN x) : (r', 0\<^sub>B\<^sub>T)\<^sub>B\<^sub>T | \<Gamma> " | 
     
     (*Statements *)       
     T_Alias  [simp, intro!]: 
      "\<lbrakk>(Type_Var \<Gamma> y) = (Future f) ;
        S = (x =\<^sub>A Expr(Var y)) ;
        \<Gamma>'= \<Gamma>\<lparr>Env_Variable := (Env_Variable \<Gamma>)(x := (Future f))\<rparr>
      \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(0\<^sub>B\<^sub>T) | \<Gamma>' " |
     
     T_Var_Expression [simp, intro!]:
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m (Exp e) : (r, b)\<^sub>B\<^sub>T | \<Gamma>' ;
       S = (x =\<^sub>A (Expr e)) ;
       \<Gamma>''= \<Gamma>\<lparr>Env_Variable := (Env_Variable \<Gamma>)(x := (Rec r))\<rparr> 
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(b) | \<Gamma>'' " |
     
     T_NewActive [simp, intro!]:
      "\<lbrakk>S = (x =\<^sub>A newActive()) ;
        fresh_act \<Gamma> \<alpha> ;
        \<Gamma>'= \<Gamma>\<lparr>Env_Variable := (Env_Variable \<Gamma>)(x := (Rec ([\<alpha>]\<^sub>O)))\<rparr> 
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(0\<^sub>B\<^sub>T) | \<Gamma>' " | 
     
     T_Invk [simp, intro!]:
      "\<lbrakk>\<Gamma> \<turnstile>\<^sub>m this : (ET (Rec ([\<alpha>]\<^sub>O))) | \<Gamma> ;
        \<Gamma> \<turnstile>\<^sub>m (Exp e) : (([\<alpha>']\<^sub>O), b)\<^sub>B\<^sub>T | \<Gamma>' ;
        m' = MName met;
        \<Gamma>' \<turnstile>\<^sub>m (Met met) : BT(m'(obj , parType)\<rightarrow>r') | \<Gamma>' ;     
        S = (x=\<^sub>Ae.\<^sub>Am(el)) ;
        fresh_fut \<Gamma> f ;
        r = (\<alpha>'..m'\<leadsto>r');
        (*miss typing parameters*)
        b' = (m'(([\<alpha>']\<^sub>O) , parType')\<rightarrow>r');
        \<Gamma>''= \<Gamma>'\<lparr>Env_Future := (Env_Future \<Gamma>)(f := (r, b')\<^sub>F )\<rparr> 
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(b ;\<^sub>s (b' \<parallel> Unsync)) | \<Gamma>' " |

     T_Seq [simp, intro!]:
      "\<lbrakk>sl = s;;sl' ;
        \<Gamma> \<turnstile>\<^sub>m (St s) : BT(b) | \<Gamma>' ;
        \<Gamma>' \<turnstile>\<^sub>m (Stl sl') : BT(b') | \<Gamma>''
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (Stl sl) : BT(b;\<^sub>sb') | \<Gamma>'' " |
     
     T_Return [simp, intro!]:
      "\<lbrakk>S = (return e) ;
        \<Gamma> \<turnstile>\<^sub>m (Exp e) : (ET(Rec r)) | \<Gamma> ;
        m' = MName met;
        \<Gamma> \<turnstile>\<^sub>m (Met met) : BT(m'(obj , parType)\<rightarrow>r') | \<Gamma>        
       \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>m (St S) : BT(0\<^sub>B\<^sub>T) | \<Gamma> "   |

     T_If [simp, intro!]:
     "\<lbrakk> \<Gamma> \<turnstile>\<^sub>m (Exp e) : (ET(Rec (Prm (ASPBool r)))) | \<Gamma> ;
       \<Gamma> \<turnstile>\<^sub>m (Stl sl\<^sub>1) : BT(b\<^sub>1) | \<Gamma>\<^sub>1 ;
       \<Gamma> \<turnstile>\<^sub>m (Stl sl\<^sub>2) : BT(b\<^sub>2) | \<Gamma>\<^sub>2 ;
       compare_\<Gamma>_each_x \<Gamma> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<and> (\<forall>x f' f''. (\<exists> f .((Type_Var \<Gamma> x) = (Future f)) \<longrightarrow> ((Type_Var \<Gamma>\<^sub>1 x) = (Future f') \<and>  (Type_Var \<Gamma>\<^sub>2 x) = (Future f'') 
                           \<longrightarrow> (Type_Fut \<Gamma>\<^sub>1 f') =  (Type_Fut \<Gamma>\<^sub>2 f'')))); (*f = f' because of compare_\<Gamma>*)
       sum_\<Gamma> \<Gamma>' \<Gamma>\<^sub>1 \<Gamma>\<^sub>2
 \<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile>\<^sub>m (St S) : BT(b\<^sub>1\<parallel>b\<^sub>2) | \<Gamma>'"  
 
(*    
   T_Value [simp, intro!]: 
      "\<lbrakk> (fut_rec = (Checked t)\<or>fut_rec = (Unchecked t B));
         \<Gamma> \<turnstile> (Var e) : (ET (Future f)) | \<Gamma>;
         \<Gamma> \<turnstile> (Fut f) : (FR fut_rec) | \<Gamma>     
        \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var e) : (ET(Rec t)) | \<Gamma>" |
*)


