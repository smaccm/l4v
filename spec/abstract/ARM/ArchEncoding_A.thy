header "Encoding ARM VSpace concepts"

theory ArchEncoding_A imports
  ArchVSpace_A
begin

text {* 
  Convert a set of rights into binary form.
  @{text "AP[2:1]"} permission model, cf. B3.7.1, pg 1357.
  For stage 1 translations:
  0 means kernel-only (PL1) access (read/write),
  1 means read/write at any privilege level,
  2 means read-only for user-level (PL0), read-write for kernel (PL1).
*}
definition
  word_from_vm_rights :: "vm_rights \<Rightarrow> word32" where  
  "word_from_vm_rights R \<equiv> 
  if vm_read_write \<subseteq> R then 1
  else if vm_read_only \<subseteq> R then 2
  else 0"


text {* The vm rights of a PTE. Empty if not applicable. *}
fun
  vm_rights_of :: "pte \<Rightarrow> cap_rights"
where
  "vm_rights_of (Block_1G_PTE _ _ rights) = rights" |
  "vm_rights_of (Block_2M_PTE _ _ rights) = rights" |
  "vm_rights_of (PagePTE _ _ rights) = rights" |
  "vm_rights_of _ = {}"

text {* The vm attributes of a PTE. Empty if not applicable. *}
fun
  vm_attribs_of :: "pte \<Rightarrow> vm_attributes"
where
  "vm_attribs_of (Block_1G_PTE _ attrs _) = attrs" |
  "vm_attribs_of (Block_2M_PTE _ attrs _) = attrs" |
  "vm_attribs_of (PagePTE _ attrs _) = attrs" |
  "vm_attribs_of _ = {}"

text {*
  Encoding of VM attributes as in stage 1 block and page descriptors (cf B3.6.2, pg 1342).
  We only allow users to specify the Cacheable attribute, which translates to 
  Write-Back, Write-Allocate (cf B3.8.2, pg 1367).
  This assumes TRE == 0 Remap disabled (cf B3.8.1, pg 1366).
*}
definition
  word_from_vmattr :: "vm_attributes \<Rightarrow> machine_word"
where
  "word_from_vmattr attr \<equiv> if PageCacheable \<in> attr then 0b110 else 0"

text {* Encode a page table entry into the equivalent entry that the page
table walker implemented in ARM hardware would parse, cf B3.6.1. *}
definition
  word_from_pte :: "pte \<Rightarrow> machine_word" where
  "word_from_pte pte \<equiv> 
    (if pte = InvalidPTE then 0 
     else if is_block pte then 1
     else 0b11) ||
    addr_from_pte pte ||
    (word_from_vmattr (vm_attribs_of pte) << 2) ||
    (word_from_vm_rights (vm_rights_of pte) << 6)"

end
