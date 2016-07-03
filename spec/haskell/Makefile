#
# Copyright 2014, General Dynamics C4 Systems
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(GD_GPL)
#

BOOT_MODULES = Kernel/CSpace Kernel/Thread Kernel/FaultHandler \
    Kernel/VSpace Kernel/Init Model/PSpace Object/TCB Object/CNode  \
    Object/ObjectType Object/Endpoint Object/Interrupt
# FIXME ^ VCPUs go above?

BOOT_FILES=$(BOOT_MODULES:%=src/SEL4/%.lhs-boot)

GHC=ghc

#all: build pdf FIXME original
all: build-arm-hyp

build: $(BOOT_FILES)
	cabal sandbox init
	cabal install --dependencies-only -w "$(GHC)"
	cabal configure --configure-option="arm-kzm" -w "$(GHC)" \
	    --flags="ArchArm"
	cabal build

# FIXME XXX these warnings are useless during large Haskell updates
GHC_FIXME_OPTS=--ghc-options="-fno-warn-unused-matches -fno-warn-unused-imports"

build-arm-hyp: $(BOOT_FILES)
	cabal sandbox init
	cabal install --dependencies-only -w "$(GHC)"
	cabal configure --configure-option="arm-tk1" -w "$(GHC)" \
	    --flags="ArchArmHyp -FFI" $(GHC_FIXME_OPTS)
	cabal build

build-arm-hyp-nosmmu: $(BOOT_FILES)
	cabal sandbox init
	cabal install --dependencies-only -w "$(GHC)"
	cabal configure --configure-option="arm-tk1-nosmmu" -w "$(GHC)" \
	    --flags="ArchArmHyp -FFI" $(GHC_FIXME_OPTS)
	cabal build

pdf:
	cd doc && make

%.lhs-boot: %.lhs mkhsboot.pl
	perl mkhsboot.pl -l < $< > $@

clean:
	rm -f $(BOOT_FILES)
	cabal clean

.PHONY: all build build-arm-hyp pdf clean

