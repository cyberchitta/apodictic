import VersoManual
import ApodicticDoc.Result
import ApodicticDoc.Archaeology

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Apodictic: Machine-Checked Praxeology" =>

%%%
authors := ["restlessronin"]
%%%

The axiom archaeology of Austrian praxeology, formalized in Lean 4:
the narrative of every axiom's pedigree, the findings forced by the
proof assistant, the design decisions as they were made, and the
rejected encodings as type-checked code.

{include 1 ApodicticDoc.Result}

{include 1 ApodicticDoc.Archaeology}
