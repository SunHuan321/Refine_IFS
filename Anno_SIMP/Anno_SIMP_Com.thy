theory Anno_SIMP_Com
  imports Main 
begin

type_synonym 's bexp = "'s set"
type_synonym 's assn = "'s set"

datatype 's ann_prog =
    AnnBasic "('s assn)" "'s \<Rightarrow>'s"
  | AnnSeq "'s ann_prog" "'s ann_prog"
  | AnnCond "('s assn)" "'s bexp" "'s ann_prog" "'s ann_prog"
  | AnnWhile "('s assn)" "'s bexp" "'s ann_prog"
  | AnnAwait "('s assn)" "'s bexp" "'s ann_prog"
  | AnnNondt "('s assn)" "('s \<times> 's) set"

primrec ann_pre ::"'s ann_prog \<Rightarrow> 's assn"  where
  "ann_pre (AnnBasic r f) = r"
| "ann_pre (AnnSeq c1 c2) = ann_pre c1"
| "ann_pre (AnnCond r b c1 c2) = r"
| "ann_pre (AnnWhile r b c) = r"
| "ann_pre (AnnAwait r b c) = r"
| "ann_pre (AnnNondt r f) = r"

end