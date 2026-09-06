import VersoManual
import ApodicticDoc.Result

open Verso.Genre Manual

set_option pp.rawOnError true

/-
The archaeology part was DROPPED (human decision 2026-09-06): its
narrative duplicated `_notes/`, its docstring quotes duplicated
`Result`, and its crashes were rationale for an encoding the library
no longer uses. `ApodicticDoc.Rejected` went the same way once the
switch to structures made both crashes unreachable. History lives in
`_notes/`; this package emits one part.
-/
#doc (Manual) "Apodictic: Machine-Checked Praxeology" =>

%%%
authors := ["restlessronin"]
%%%

Austrian praxeology formalized in Lean 4: the axioms, the theorems
they carry, and the receipt under each theorem.

{include 1 ApodicticDoc.Result}
