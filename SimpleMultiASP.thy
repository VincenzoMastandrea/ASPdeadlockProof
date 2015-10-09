(*  Title:      SimpleMultiASP.thy
    Author:     Vincenzo Mastandrea Ludovic Henrio and Florian Kammuller
                2015

    Note:       Multi-active object formalisation
                1) One class
                2) No class filds and parameters
                3) Alowed passing future
*)

(*Conventions:
  x,y=varname
  locs = local variables
  Stl = statement list
  EContext is an execution context, ie a thread 
  EcL = EContext list*)

header {* Syntax and Semantics *}

theory SimpleMultiASP imports Main AuxiliaryFunctions CommonStructure begin
 
subsection {* Syntax *}
(* 
type_synonym ItfName = string
type_synonym VarName =  string
datatype VarOrThis = This | Variable VarName
type_synonym ClassName = string
type_synonym MethodName = string

type_synonym ActName = nat
type_synonym FutName = nat
*)

datatype Signature = Method ItfName MethodName  "(ItfName * VarName) list" 
  (* signature = Method returnType MethodName (list of parameters)*)


(*
type_synonym  Object = "(VarName~=>Value) * ClassName"
abbreviation GetObject:: "Object \<Rightarrow>VarName=>Value option" ("_.[_]")
  where "GetObject ob x \<equiv> (fst ob) x"
abbreviation SetObject:: "Object \<Rightarrow>VarName=>Value\<Rightarrow>Object" ("_.[_]:=_")
  where "SetObject ob x v\<equiv> ((fst ob)(x\<mapsto>v),snd ob)"
*)

datatype Expression = Val Value
             | Var VarOrThis 
             | Plus Expression Expression ("_+\<^sub>A_" [120,120] 200) 
             | And Expression Expression ("_&\<^sub>A_" [100,100] 300) 
             | Test Expression Expression ("_==\<^sub>A_" [100,100] 300) 
             
datatype Rhs = Expr Expression
             | Call Expression MethodName "Expression list" ("_.\<^sub>A_'(_')" [440,0,50] 500) (*e.m(e list) *)
             | Hole (* runtime term *)

datatype Statement =  Assign VarName Rhs  (infix "=\<^sub>A"  400) (*x=z*)
| NewActive VarName ("_ =\<^sub>A newActive'(')" [300] 300)
| Return Expression ("return _" [300] 300)(*return E *)
| If Expression "Statement list" "Statement list" ("IF _ THEN _ ELSE _ " [300,0,0] 300)(*if E then s else s *)
(* skip |  NB: skip and seq are not necessary thanks to the use of statement list
| Seq Statement Statement (infix ";;"  100)*)

abbreviation MakeStatementList:: "Statement \<Rightarrow>Statement list\<Rightarrow>Statement list" (infix ";;" 100)
  where "MakeStatementList s Stl\<equiv> s#Stl"
abbreviation MakeStatementList2:: "Statement \<Rightarrow>Statement\<Rightarrow>Statement list" (infix ";;;" 80)
  where "MakeStatementList2 s s'\<equiv> s#[s']"

record Method = 
MethSignature:: Signature 
LocalVariables::"(ItfName * VarName) list" 
Body::"Statement list"
(*MethDefinition methodname (local variables) body*)


abbreviation MName:: "Method \<Rightarrow> MethodName"
where "MName m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>MethName"

abbreviation MRType:: "Method \<Rightarrow> ItfName"
where "MRType m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>returnType"

abbreviation MParams:: "Method \<Rightarrow>(ItfName * VarName) list"  
where "MParams m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>listparameters"

record Class = 
 Name::ClassName 
 Methods::"(Method list)"
             (*ASPclass (listofmethodbodies) *)

datatype Program = Prog Class "(ItfName * VarName) list" "Statement list"

type_synonym EContext = "(VarName~=>Value) * (Statement list)" 
                         (*{l|s} execution context = location of this, local variables, and statements *)

type_synonym Request = "StaticFuture * MethodName * (Value list)" (*q ::= (f,m,\<^bold>v) *)

abbreviation EC_locs:: "EContext \<Rightarrow>(VarName~=>Value)"
where "EC_locs Ec \<equiv> fst Ec"

abbreviation EC_Stl:: "EContext \<Rightarrow>Statement list"
where "EC_Stl Ec \<equiv> snd Ec"
(*datatype Process = Proc Request "Context list" *)

datatype ActiveObject = AO "Request~=>EContext" "Request list"
    (* active object location , store, task list, request queue*)

datatype FutValue = Undefined | FutVal Value 

datatype Configuration = Cn "ActName~=>ActiveObject" "StaticFuture~=>FutValue"

subsection {*finite configuration *}
definition finite_Processes :: "(Request~=>EContext) \<Rightarrow> bool"
  where
    "finite_Processes (processMap) \<equiv> finite (dom (processMap)) \<and>
       (\<forall> cont\<in>ran(processMap). finite (dom(EC_locs(cont))))"

primrec finite_Configuration :: "Configuration => bool"
  where
 " finite_Configuration (Cn AOs Futures) =
      (finite (dom AOs) \<and> finite (dom Futures) \<and> 
      (\<forall> ao\<in>(ran AOs). \<forall> P Q. ao = AO P Q \<longrightarrow> finite_Processes P))"

declare SimpleMultiASP.finite_Configuration.simps[simp del]

text{* Binding and fetching elements *}
definition fetchClass
where
"fetchClass P \<equiv> 
case P of (Prog C Vars Stl) \<Rightarrow> C
"

definition fetchMethodInClass
where
"fetchMethodInClass class m \<equiv> 
Option.bind 
(List.find (\<lambda>method. (MName method = m)) (Methods class))
(\<lambda>method. Some (map snd (MParams method), map snd (LocalVariables method), Body method))
"

abbreviation DefinedClassNames
where "DefinedClassNames prog \<equiv> (case prog of Prog C vl xtl \<Rightarrow>Name C)"


definition Bind::"Program\<Rightarrow>MethodName\<Rightarrow>Value list\<Rightarrow> EContext option"
where
 "Bind P m value_list\<equiv>
(case  fetchMethodInClass (fetchClass P) m  of 
       Some (param_list,locs,b) \<Rightarrow> 
         if length param_list = length value_list then
           ( let locales=  (map_of (zip locs (replicate (length locs) (Prim null))))
                    ++ (map_of (zip param_list value_list)) in
                Some (locales,b))
           else None
       | None \<Rightarrow> None)
" 


(* semantics parameterized by compatibility and binder function*)
axiomatization 
  Compatible :: "(Request * Request) set"
where                                         
  symmetric_compatible: "sym Compatible"

lemma COMP[rule_format]: "\<forall>x y. (x,y)\<in>Compatible\<longrightarrow>(y,x)\<in>Compatible"
apply (fold sym_def)
apply (rule symmetric_compatible)
done

section{*SOS*}

inductive_set EvalValue:: "(Value \<times> Value) set"
where
  Valnull[simp,intro]: "(Prim null, Prim null)\<in>EvalValue"              |
  Valint[simp,intro]:  "(Prim (ASPInt i), Prim (ASPInt i))\<in>EvalValue"   |
  valbool[simp,intro]: "(Prim (ASPBool b), Prim (ASPBool b))\<in>EvalValue" |
  valact[simp,intro]:  "(ActRef \<alpha>, (ActRef \<alpha>) )\<in>EvalValue"   |
  valfut[simp,intro]:  "(FutRef f, (FutRef f) )\<in>EvalValue"

lemma EvalValue_is_deterministic[rule_format,intro]: "(e,v)\<in>EvalValue \<longrightarrow>(e,v')\<in>EvalValue \<longrightarrow>v=v'"
apply (rule impI)
apply auto
apply (erule EvalValue.cases,simp+)+
done

inductive_set EvalExpr:: "(Expression \<times> (VarName~=>Value) \<times> Value) set"
(* (e1,locs,v) is true if e1 EVALUATES to v  in a setting where local variables are locs*)
 where
   exprval [simp,intro]:  "(v,ev)\<in>EvalValue \<Longrightarrow>(Val v, locs, ev)\<in>EvalExpr"                   |
   exprlocs[simp,intro]:  "\<lbrakk>locs(x)=Some v;(v,ev)\<in>EvalValue\<rbrakk> \<Longrightarrow>(Var (Variable x), locs, ev)\<in>EvalExpr" |
   expradd [simp,intro]:  "\<lbrakk>(e,locs,Prim (ASPInt i))\<in>EvalExpr;(e',locs, Prim (ASPInt i'))\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e +\<^sub>A e', locs,Prim (ASPInt (i+i')))\<in>EvalExpr"                             |
   exprand [simp,intro]:  "\<lbrakk>(e,locs,Prim (ASPBool b))\<in>EvalExpr;(e',locs,Prim (ASPBool b'))\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e &\<^sub>A e', locs, Prim (ASPBool (b\<and>b')))\<in>EvalExpr"                            |
   exprtest[simp,intro]:  "\<lbrakk>(e,locs,Prim (ASPInt i))\<in>EvalExpr;(e',locs,Prim (ASPInt i'))\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e ==\<^sub>A e', locs, Prim (ASPBool (i=i')))\<in>EvalExpr"

lemma EvalExpr_is_deterministic[rule_format]: 
      " (e,locs,v)\<in>EvalExpr \<longrightarrow> (\<forall> v'. (e,locs,v')\<in>EvalExpr \<longrightarrow>v=v')"
apply (rule impI)
apply (erule EvalExpr.induct)
apply (auto)
apply (erule EvalExpr.cases)
apply (auto)
apply (erule EvalExpr.cases)
apply (auto)
apply (erule_tac ?a1.0="e+\<^sub>Ae'"  in EvalExpr.cases,auto)
apply (erule_tac ?a1.0="e&\<^sub>Ae'"  in EvalExpr.cases,auto)
apply (erule_tac ?a1.0="e==\<^sub>Ae'" in EvalExpr.cases,auto)
done

abbreviation Ready:: "Request\<Rightarrow>(Request~=>EContext)\<Rightarrow>(Request list)\<Rightarrow>bool"
 (*Ready q,p,Rq returns true if q is ready to be served*)
where
 "Ready R tasks Rq \<equiv>(\<forall> Q\<in>dom(tasks). (R,Q)\<in>Compatible)
                     \<and> (\<forall> Q\<in>set Rq. (R,Q)\<in>Compatible)"

inductive reduction :: "Program\<Rightarrow>[Configuration, Configuration] => bool"  ("_\<turnstile>_\<leadsto>_" 50)
  where
    Serve [simp, intro!]: 
      "\<lbrakk>(Activities \<alpha>) = Some (AO tasks (Rq@R#Rq')) ; R=(f,m,vl); 
        Ready R tasks Rq; 
        Bind P m vl = Some EC\<rbrakk> 
          \<Longrightarrow> P\<turnstile>Cn Activities Futures 
                \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO (tasks(R\<mapsto>EC))) (Rq@Rq'))) Futures" |

    AssignLocal  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq); 
       tasks Q = Some ((locs,(x=\<^sub>AExpr e);;Stl)); 
       x\<in>dom locs ; (e,locs, v)\<in>EvalExpr 
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO (tasks(Q\<mapsto>(locs(x\<mapsto>v),Stl))) Rq)))  Futures" |

     NewActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq); 
       tasks Q = Some (locs,x =\<^sub>A newActive();;Stl); 
       \<gamma>\<notin>dom Activities       
      \<rbrakk>   
        \<Longrightarrow> P\<turnstile>Cn Activities Futures 
             \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO (tasks(Q\<mapsto>(locs,x=\<^sub>AExpr (Val (ActRef \<gamma>));;Stl))) Rq))
                             (\<gamma>\<mapsto> (AO empty [])))  Futures" |

   InvkActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq); 
       Activities \<beta> = Some (AO tasks\<^sub>\<beta> Rq\<^sub>\<beta>); 
       tasks Q = Some (locs,x=\<^sub>A(e.\<^sub>Am(el));;Stl);
       \<alpha>\<noteq>\<beta>;
       (e,locs,ActRef \<beta>)\<in>EvalExpr;
       f\<notin>dom Futures; 
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,locs,value_list!i)\<in>EvalExpr)
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO (tasks(Q\<mapsto>(locs,x=\<^sub>AExpr (Val (FutRef f));;Stl))) Rq)
                          (\<beta>\<mapsto> AO tasks\<^sub>\<beta> (Rq\<^sub>\<beta>@[(f,m,value_list)]) )) 
               (Futures(f\<mapsto>Undefined))" |

   InvkActive_Self  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq); 
       tasks Q = Some (locs,x=\<^sub>A(e.\<^sub>Am(el));;Stl);
       (e,locs,ActRef \<alpha>)\<in>EvalExpr;
       f\<notin>dom Futures;   
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,locs,value_list!i)\<in>EvalExpr)
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO (tasks(Q\<mapsto>(locs,x=\<^sub>AExpr (Val (FutRef f));;Stl))) (Rq@[(f,m,value_list)]))) 
               (Futures(f\<mapsto>Undefined))" |

   ReturnRequest [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq); 
       tasks Q = Some (locs,return e;;Stl);   Q=(f,m,vl);
       (e,locs,v)\<in>EvalExpr  
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO (tasks|``Q) Rq) ) (Futures(f\<mapsto>FutVal v ))" |

    UpdateFuture [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq); 
       tasks Q = Some (locs,Stl);   Q=(f,m,vl);
       locs x = Some (FutRef f);  
       Futures f = Some (FutVal v )
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO (tasks(Q\<mapsto>(locs(x\<mapsto>v),Stl))) Rq)) Futures"   |

    IfThenElseTrue [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq); 
       tasks Q = Some (locs,(IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl);
       (e,locs,Prim (ASPBool True))\<in>EvalExpr
   \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO (tasks(Q\<mapsto>(locs,s\<^sub>t@Stl))) Rq))) Futures"  |

    IfThenElseFalse [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO tasks Rq);
       tasks Q = Some (locs,(IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl);
       (e,locs,Prim (ASPBool False))\<in>EvalExpr
   \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO (tasks(Q\<mapsto>(locs,s\<^sub>e@Stl))) Rq))) Futures"  

definition emptyObjClass  where
"emptyObjClass \<equiv> 
\<lparr> Name = ''EmptyObjectClass'',
  Methods=[]
\<rparr>"

definition BuildInitialConfigurationfromVarsStl:: "(VarName list) \<Rightarrow>Statement list\<Rightarrow> Configuration"
where
  "BuildInitialConfigurationfromVarsStl vl stl \<equiv> Cn (empty(0\<mapsto>(AO
                  (empty((0,''m'',[])\<mapsto>((map_of (zip vl (replicate (length vl) (Prim null)))),stl))) [])))
                  (empty(0\<mapsto>Undefined))"

definition InitialConfiguration:: "Program \<Rightarrow>Configuration"
where  
" InitialConfiguration prog \<equiv> case prog of (Prog C Vars Stl) \<Rightarrow> BuildInitialConfigurationfromVarsStl (map snd Vars) Stl" 


end
