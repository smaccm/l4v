%
% Copyright 2016, Data61, CSIRO
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

The ARM target does not have any hypervisor support.

> module SEL4.Kernel.Hypervisor.ARM where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Machine.Hardware.ARM as Arch

\end{impdetails}

> handleHypervisorFault :: PPtr TCB -> Arch.HypFaultType -> Kernel ()
> handleHypervisorFault _ Arch.ARMNoHypFaults = fail "No hypervisor on this architecture"

