(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchInterrupt_H
imports "../RetypeDecls_H" "../CNode_H" "../InterruptDecls_H" ArchInterruptDecls_H
begin
context Arch begin global_naming ARM_HYP_H

defs decodeIRQControlInvocation_def:
"decodeIRQControlInvocation arg1 arg2 arg3 arg4 \<equiv> throw IllegalOperation"

defs performIRQControl_def:
"performIRQControl arg1 \<equiv> haskell_fail []"

defs checkIRQ_def:
"checkIRQ irq\<equiv> rangeCheck irq (fromEnum minIRQ) (fromEnum maxIRQ)"

defs handleReservedIRQ_def:
"handleReservedIRQ irq \<equiv> haskell_fail []"

defs initInterruptController_def:
"initInterruptController\<equiv> (do
    setIRQState IRQReserved $ IRQ irqVGICMaintenance;
    return ()
od)"


end
end
