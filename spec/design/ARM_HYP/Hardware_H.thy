(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Hardware_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Hardware_H
imports
  "../../machine/ARM_HYP/MachineOps"
  State_H
begin
context Arch begin global_naming ARM_HYP_H

type_synonym irq = "Platform.ARM_HYP.irq"

type_synonym paddr = "Platform.ARM_HYP.paddr"

datatype vmrights =
    VMNoAccess
  | VMKernelOnly
  | VMReadOnly
  | VMReadWrite

datatype pde =
    InvalidPDE
  | PageTablePDE paddr
  | SectionPDE paddr bool bool vmrights
  | SuperSectionPDE paddr bool bool vmrights

primrec
  pdeFrame :: "pde \<Rightarrow> paddr"
where
  "pdeFrame (SuperSectionPDE v0 v1 v2 v3) = v0"
| "pdeFrame (SectionPDE v0 v1 v2 v3) = v0"

primrec
  pdeRights :: "pde \<Rightarrow> vmrights"
where
  "pdeRights (SuperSectionPDE v0 v1 v2 v3) = v3"
| "pdeRights (SectionPDE v0 v1 v2 v3) = v3"

primrec
  pdeExecuteNever :: "pde \<Rightarrow> bool"
where
  "pdeExecuteNever (SuperSectionPDE v0 v1 v2 v3) = v2"
| "pdeExecuteNever (SectionPDE v0 v1 v2 v3) = v2"

primrec
  pdeCacheable :: "pde \<Rightarrow> bool"
where
  "pdeCacheable (SuperSectionPDE v0 v1 v2 v3) = v1"
| "pdeCacheable (SectionPDE v0 v1 v2 v3) = v1"

primrec
  pdeTable :: "pde \<Rightarrow> paddr"
where
  "pdeTable (PageTablePDE v0) = v0"

primrec
  pdeFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeFrame_update f (SuperSectionPDE v0 v1 v2 v3) = SuperSectionPDE (f v0) v1 v2 v3"
| "pdeFrame_update f (SectionPDE v0 v1 v2 v3) = SectionPDE (f v0) v1 v2 v3"

primrec
  pdeRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeRights_update f (SuperSectionPDE v0 v1 v2 v3) = SuperSectionPDE v0 v1 v2 (f v3)"
| "pdeRights_update f (SectionPDE v0 v1 v2 v3) = SectionPDE v0 v1 v2 (f v3)"

primrec
  pdeExecuteNever_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeExecuteNever_update f (SuperSectionPDE v0 v1 v2 v3) = SuperSectionPDE v0 v1 (f v2) v3"
| "pdeExecuteNever_update f (SectionPDE v0 v1 v2 v3) = SectionPDE v0 v1 (f v2) v3"

primrec
  pdeCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeCacheable_update f (SuperSectionPDE v0 v1 v2 v3) = SuperSectionPDE v0 (f v1) v2 v3"
| "pdeCacheable_update f (SectionPDE v0 v1 v2 v3) = SectionPDE v0 (f v1) v2 v3"

primrec
  pdeTable_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pde \<Rightarrow> pde"
where
  "pdeTable_update f (PageTablePDE v0) = PageTablePDE (f v0)"

abbreviation (input)
  PageTablePDE_trans :: "(paddr) \<Rightarrow> pde" ("PageTablePDE'_ \<lparr> pdeTable= _ \<rparr>")
where
  "PageTablePDE_ \<lparr> pdeTable= v0 \<rparr> == PageTablePDE v0"

abbreviation (input)
  SectionPDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("SectionPDE'_ \<lparr> pdeFrame= _, pdeCacheable= _, pdeExecuteNever= _, pdeRights= _ \<rparr>")
where
  "SectionPDE_ \<lparr> pdeFrame= v0, pdeCacheable= v1, pdeExecuteNever= v2, pdeRights= v3 \<rparr> == SectionPDE v0 v1 v2 v3"

abbreviation (input)
  SuperSectionPDE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pde" ("SuperSectionPDE'_ \<lparr> pdeFrame= _, pdeCacheable= _, pdeExecuteNever= _, pdeRights= _ \<rparr>")
where
  "SuperSectionPDE_ \<lparr> pdeFrame= v0, pdeCacheable= v1, pdeExecuteNever= v2, pdeRights= v3 \<rparr> == SuperSectionPDE v0 v1 v2 v3"

definition
  isInvalidPDE :: "pde \<Rightarrow> bool"
where
 "isInvalidPDE v \<equiv> case v of
    InvalidPDE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isPageTablePDE :: "pde \<Rightarrow> bool"
where
 "isPageTablePDE v \<equiv> case v of
    PageTablePDE v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSectionPDE :: "pde \<Rightarrow> bool"
where
 "isSectionPDE v \<equiv> case v of
    SectionPDE v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSuperSectionPDE :: "pde \<Rightarrow> bool"
where
 "isSuperSectionPDE v \<equiv> case v of
    SuperSectionPDE v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype pte =
    InvalidPTE
  | LargePagePTE paddr bool bool vmrights
  | SmallPagePTE paddr bool bool vmrights

primrec
  pteFrame :: "pte \<Rightarrow> paddr"
where
  "pteFrame (LargePagePTE v0 v1 v2 v3) = v0"
| "pteFrame (SmallPagePTE v0 v1 v2 v3) = v0"

primrec
  pteRights :: "pte \<Rightarrow> vmrights"
where
  "pteRights (LargePagePTE v0 v1 v2 v3) = v3"
| "pteRights (SmallPagePTE v0 v1 v2 v3) = v3"

primrec
  pteCacheable :: "pte \<Rightarrow> bool"
where
  "pteCacheable (LargePagePTE v0 v1 v2 v3) = v1"
| "pteCacheable (SmallPagePTE v0 v1 v2 v3) = v1"

primrec
  pteExecuteNever :: "pte \<Rightarrow> bool"
where
  "pteExecuteNever (LargePagePTE v0 v1 v2 v3) = v2"
| "pteExecuteNever (SmallPagePTE v0 v1 v2 v3) = v2"

primrec
  pteFrame_update :: "(paddr \<Rightarrow> paddr) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteFrame_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE (f v0) v1 v2 v3"
| "pteFrame_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE (f v0) v1 v2 v3"

primrec
  pteRights_update :: "(vmrights \<Rightarrow> vmrights) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteRights_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE v0 v1 v2 (f v3)"
| "pteRights_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE v0 v1 v2 (f v3)"

primrec
  pteCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteCacheable_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE v0 (f v1) v2 v3"
| "pteCacheable_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE v0 (f v1) v2 v3"

primrec
  pteExecuteNever_update :: "(bool \<Rightarrow> bool) \<Rightarrow> pte \<Rightarrow> pte"
where
  "pteExecuteNever_update f (LargePagePTE v0 v1 v2 v3) = LargePagePTE v0 v1 (f v2) v3"
| "pteExecuteNever_update f (SmallPagePTE v0 v1 v2 v3) = SmallPagePTE v0 v1 (f v2) v3"

abbreviation (input)
  LargePagePTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pte" ("LargePagePTE'_ \<lparr> pteFrame= _, pteCacheable= _, pteExecuteNever= _, pteRights= _ \<rparr>")
where
  "LargePagePTE_ \<lparr> pteFrame= v0, pteCacheable= v1, pteExecuteNever= v2, pteRights= v3 \<rparr> == LargePagePTE v0 v1 v2 v3"

abbreviation (input)
  SmallPagePTE_trans :: "(paddr) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (vmrights) \<Rightarrow> pte" ("SmallPagePTE'_ \<lparr> pteFrame= _, pteCacheable= _, pteExecuteNever= _, pteRights= _ \<rparr>")
where
  "SmallPagePTE_ \<lparr> pteFrame= v0, pteCacheable= v1, pteExecuteNever= v2, pteRights= v3 \<rparr> == SmallPagePTE v0 v1 v2 v3"

definition
  isInvalidPTE :: "pte \<Rightarrow> bool"
where
 "isInvalidPTE v \<equiv> case v of
    InvalidPTE \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isLargePagePTE :: "pte \<Rightarrow> bool"
where
 "isLargePagePTE v \<equiv> case v of
    LargePagePTE v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSmallPagePTE :: "pte \<Rightarrow> bool"
where
 "isSmallPagePTE v \<equiv> case v of
    SmallPagePTE v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype vmattributes =
    VMAttributes bool bool bool

primrec
  armParityEnabled :: "vmattributes \<Rightarrow> bool"
where
  "armParityEnabled (VMAttributes v0 v1 v2) = v1"

primrec
  armExecuteNever :: "vmattributes \<Rightarrow> bool"
where
  "armExecuteNever (VMAttributes v0 v1 v2) = v2"

primrec
  armPageCacheable :: "vmattributes \<Rightarrow> bool"
where
  "armPageCacheable (VMAttributes v0 v1 v2) = v0"

primrec
  armParityEnabled_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armParityEnabled_update f (VMAttributes v0 v1 v2) = VMAttributes v0 (f v1) v2"

primrec
  armExecuteNever_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armExecuteNever_update f (VMAttributes v0 v1 v2) = VMAttributes v0 v1 (f v2)"

primrec
  armPageCacheable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> vmattributes \<Rightarrow> vmattributes"
where
  "armPageCacheable_update f (VMAttributes v0 v1 v2) = VMAttributes (f v0) v1 v2"

abbreviation (input)
  VMAttributes_trans :: "(bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> vmattributes" ("VMAttributes'_ \<lparr> armPageCacheable= _, armParityEnabled= _, armExecuteNever= _ \<rparr>")
where
  "VMAttributes_ \<lparr> armPageCacheable= v0, armParityEnabled= v1, armExecuteNever= v2 \<rparr> == VMAttributes v0 v1 v2"

lemma armParityEnabled_armParityEnabled_update [simp]:
  "armParityEnabled (armParityEnabled_update f v) = f (armParityEnabled v)"
  by (cases v) simp

lemma armParityEnabled_armExecuteNever_update [simp]:
  "armParityEnabled (armExecuteNever_update f v) = armParityEnabled v"
  by (cases v) simp

lemma armParityEnabled_armPageCacheable_update [simp]:
  "armParityEnabled (armPageCacheable_update f v) = armParityEnabled v"
  by (cases v) simp

lemma armExecuteNever_armParityEnabled_update [simp]:
  "armExecuteNever (armParityEnabled_update f v) = armExecuteNever v"
  by (cases v) simp

lemma armExecuteNever_armExecuteNever_update [simp]:
  "armExecuteNever (armExecuteNever_update f v) = f (armExecuteNever v)"
  by (cases v) simp

lemma armExecuteNever_armPageCacheable_update [simp]:
  "armExecuteNever (armPageCacheable_update f v) = armExecuteNever v"
  by (cases v) simp

lemma armPageCacheable_armParityEnabled_update [simp]:
  "armPageCacheable (armParityEnabled_update f v) = armPageCacheable v"
  by (cases v) simp

lemma armPageCacheable_armExecuteNever_update [simp]:
  "armPageCacheable (armExecuteNever_update f v) = armPageCacheable v"
  by (cases v) simp

lemma armPageCacheable_armPageCacheable_update [simp]:
  "armPageCacheable (armPageCacheable_update f v) = f (armPageCacheable v)"
  by (cases v) simp

definition
fromPAddr :: "paddr \<Rightarrow> machine_word"
where
"fromPAddr \<equiv> Platform.ARM_HYP.fromPAddr"

definition
pageColourBits :: "nat"
where
"pageColourBits \<equiv> Platform.ARM_HYP.pageColourBits"

definition
setCurrentPD :: "paddr \<Rightarrow> unit machine_monad"
where
"setCurrentPD pd\<equiv> (
    setCurrentPDPL2 pd
)"

definition
clearExMonitor :: "unit machine_monad"
where
"clearExMonitor\<equiv> return ()"

definition
"pteBits\<equiv> (3 ::nat)"

definition
"pdeBits\<equiv> (3 ::nat)"

definition
"pdBits\<equiv> (11 ::nat) + pdeBits"

definition
"ptBits\<equiv> (9 ::nat) + pteBits"

definition
"vcpuBits \<equiv> pageBits"

definition
pteSize :: "nat"
where
"pteSize \<equiv> bit pteBits"

definition
pdeSize :: "nat"
where
"pdeSize \<equiv> bit pdeBits"

definition
vgicIRQActive :: "machine_word"
where
"vgicIRQActive \<equiv> 2 `~shiftL~` 28"

definition
vgicIRQMask :: "machine_word"
where
"vgicIRQMask \<equiv> 3 `~shiftL~` 28"

definition
physBase :: "paddr"
where
"physBase \<equiv> toPAddr Platform.ARM_HYP.physBase"

definition
kernelBase :: "vptr"
where
"kernelBase \<equiv> Platform.ARM_HYP.kernelBase"


end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming ARM_HYP_H

end
qualify ARM_HYP_H (in Arch) 
(* vmrights instance proofs *)
(*<*)
instantiation vmrights :: enum begin
interpretation Arch .
definition
  enum_vmrights: "enum_class.enum \<equiv> 
    [ 
      VMNoAccess,
      VMKernelOnly,
      VMReadOnly,
      VMReadWrite
    ]"


definition
  "enum_class.enum_all (P :: vmrights \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: vmrights \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_vmrights enum_all_vmrights_def enum_ex_vmrights_def)
  by fast+
end

instantiation vmrights :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_vmrights: "enum_alt \<equiv> 
    alt_from_ord (enum :: vmrights list)"
instance ..
end

instantiation vmrights :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_vmrights)
end

(*>*)
end_qualify
context Arch begin global_naming ARM_HYP_H


definition
hapFromVMRights :: "vmrights \<Rightarrow> machine_word"
where
"hapFromVMRights x0\<equiv> (case x0 of
    VMKernelOnly \<Rightarrow>    0
  | VMNoAccess \<Rightarrow>    0
  | VMReadOnly \<Rightarrow>    1
  | VMReadWrite \<Rightarrow>    3
  )"

definition
wordsFromPDE :: "pde \<Rightarrow> machine_word list"
where
"wordsFromPDE x0\<equiv> (case x0 of
    InvalidPDE \<Rightarrow>    [0, 0]
  | (PageTablePDE table) \<Rightarrow>  
    let
     w0 = 3 || (fromIntegral table && 0xfffff000)
    in
    [w0, 0]
  | (SectionPDE frame cacheable xn rights) \<Rightarrow>  
    let
     w1 = 0 || (if xn then (1 << 22) else 0);
          w0 = 1 ||
               (fromIntegral frame && 0xfffff000) ||
               (1 << 10) ||
               (hapFromVMRights rights `~shiftL~` 6) ||
               (if cacheable then 0xf `~shiftL~` 2 else 0)
    in
    [w0, w1]
  | (SuperSectionPDE frame cacheable xn rights) \<Rightarrow>  
    let
     w1 = 0 || (if xn then (1 << 22) else 0) || bit 20;
          w0 = 1 ||
               (fromIntegral frame && 0xfffff000) ||
               (1 << 10) ||
               (hapFromVMRights rights `~shiftL~` 6) ||
               (if cacheable then 0xf `~shiftL~` 2 else 0)
    in
    [w0, w1]
  )"

definition
wordsFromPTE :: "pte \<Rightarrow> machine_word list"
where
"wordsFromPTE x0\<equiv> (case x0 of
    InvalidPTE \<Rightarrow>    [0, 0]
  | (SmallPagePTE frame cacheable xn rights) \<Rightarrow>  
    let
     w1 = 0 || (if xn then (1 << 22) else 0) || bit 20;
          w0 = 3 ||
               (fromIntegral frame && 0xfffff000) ||
               (1 << 10) ||
               (hapFromVMRights rights `~shiftL~` 6) ||
               (if cacheable then 0xf `~shiftL~` 2 else 0)
    in
    [w0, w1]
  | (LargePagePTE frame cacheable xn rights) \<Rightarrow>  
    let
     w1 = 0 || (if xn then (1 << 22) else 0);
          w0 = 3 ||
               (fromIntegral frame && 0xfffff000) ||
               (1 << 10) ||
               (hapFromVMRights rights `~shiftL~` 6) ||
               (if cacheable then 0xf `~shiftL~` 2 else 0)
    in
    [w0, w1]
  )"


end
end
