 (*  Title:     CommonStructure.thy
    Author:     Mastandrea Vincenzo 2015
    Note:       Common structure for behavioral types both static and runtime
*)

header {* Common structure for Behavioral Types *}

theory CommonStructure imports Main begin

type_synonym ItfName = string
type_synonym VarName =  string
datatype VarOrThis = This | Variable VarName
type_synonym ClassName = string
type_synonym MethodName = string

type_synonym ActName = nat

type_synonym StaticFuture = nat
type_synonym RuntimeFuture = nat

datatype Primitive = null | ASPInt int | ASPBool bool

datatype Value =  Prim Primitive (* static values *)
                | ActRef ActName (* runtime values *)
                | FutRef StaticFuture        

datatype Future = StatFut StaticFuture  ("_\<^sup>S\<^sup>F")
                | RunFut RuntimeFuture  ("_\<^sup>R\<^sup>F")

datatype DepPair = DependencyPair ActName MethodName ActName MethodName ("'(_.._,_.._')")

datatype ObjectRecord = ObjRec ActName  ("'[_']\<^sub>O")    (*[\<alpha>]*)

datatype BasicType = PrmType ("'_\<^sub>T")    (*_*) 
                     | Obj ObjectRecord   
                     | Control ActName MethodName  BasicType  ("_.._\<leadsto>_") (*\<alpha>.m\<leadsto>r *)

abbreviation MakeBTRSeqList:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix ";\<^sub>s\<^sub>l" 100)
  where "bt ;\<^sub>s\<^sub>l Btl\<equiv> bt#Btl"
abbreviation MakeBTRSeqList2:: "'a \<Rightarrow> 'a \<Rightarrow> 'a list" (infix ";\<^sub>s" 80)
  where "bt ;\<^sub>s bt'\<equiv> bt#[bt']"

abbreviation MakeBTRParList:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix "\<parallel>\<parallel>" 100)
  where "bt \<parallel>\<parallel> Btl\<equiv> bt@Btl"
abbreviation MakeBTRParList2:: "'a \<Rightarrow> 'a \<Rightarrow> 'a list" (infix "\<parallel>" 80)
  where "bt \<parallel> bt'\<equiv> bt#[bt']"



end
