(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
  VSpace lookup code.
*)

theory ArchHypervisor_H
imports
  "../CNode_H"
  "../KI_Decls_H"
begin
context Arch begin global_naming ARM_H


consts'
handleHypervisorFault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> unit kernel"


defs handleHypervisorFault_def:
"handleHypervisorFault arg1 hyp \<equiv> case hyp of ARMNoHypFaults \<Rightarrow> haskell_fail []"

end
end
