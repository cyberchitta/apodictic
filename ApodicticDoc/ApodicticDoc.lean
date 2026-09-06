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

Mises claimed that the theorems of praxeology carry the same certainty
as the theorems of mathematics. They follow from the plain fact that
people act, he thought, as strictly as a theorem follows from its
axioms, and no experience could ever overturn one.

This is a test of that claim on a single theorem: Rothbard's law of
marginal utility, rebuilt in Lean 4, a proof assistant. A proof
assistant will not let a step be skipped, so anything the spoken
argument passes over in silence has to be written down before the
proof will go through — and written somewhere a reader can find it.

**The finding.** The law needs exactly one premise from praxeology,
and that premise is not about action. It is about what a man *would*
do with stocks he does not have. Rothbard's own derivation runs in the
subjunctive: he sets six horses beside five and asks which want "the
larger stock would have satisfied". But his own rule is that
praxeology "may deal with utilities only as deduced from the concrete
actions of human beings", and the premise his law needs is not one
that rule admits.

The trouble is his, not something imported from outside. Nothing here
refutes the law. Lean certifies that the reasoning is valid and that
it uses nothing beyond what the statement carries; what is in question
is where the one starting premise came from.

The argument follows Rothbard's own worked case — the six horses of
*Man, Economy, and State* — from beginning to end, and the Lean at the
close is about those same six horses.

{include 1 ApodicticDoc.Result}
